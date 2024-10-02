use crate::constants::sk_enc_constants_4096_2x55_65537::{
      E_BOUND, K0IS, K1_BOUND, N, QIS, R1_BOUNDS, R2_BOUNDS, S_BOUND,
  };

use halo2_base::{
    halo2_proofs::{
        dev::MockProver,
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Assigned, Circuit, Column,
            ConstraintSystem, Error, Fixed, Instance, ProvingKey, VerifyingKey, Selector},
        poly::{
            commitment::{Params, ParamsProver},
            kzg::{
                commitment::{KZGCommitmentScheme, ParamsKZG},
                multiopen::{ProverGWC, VerifierGWC, ProverSHPLONK,},
                strategy::AccumulatorStrategy,
            },
            Rotation, VerificationStrategy,
        },
        transcript::{TranscriptReadBuffer, TranscriptWriterBuffer, Challenge255},
        halo2curves::{
          bn256::{Bn256, Fr, G1Affine},
          group::ff::Field,
      },
      SerdeFormat,

    },
    gates::{circuit::BaseCircuitParams, GateInstructions, RangeChip, RangeInstructions},
    utils::ScalarField,
    QuantumCell::Constant,
};

use crate::Deserialize;
use axiom_eth::rlc::{                                                                                                                                  
      chip::RlcChip,                                                                                                                                     
      circuit::{builder::RlcCircuitBuilder, instructions::RlcCircuitInstructions, RlcCircuitParams},                                                         utils::executor::{RlcCircuit, RlcExecutor},
  }; 

use crate::poly::{Poly, PolyAssigned};
use super::CircuitExt;

/// `BfvSkEncryptionCircuit` is a circuit that checks the correct formation of a ciphertext resulting from BFV secret key encryption
/// All the polynomials coefficients and scalars are normalized to be in the range `[0, p)` where p is the modulus of the prime field of the circuit
///
/// # Parameters:
/// * `s`: secret polynomial, sampled from ternary distribution.
/// * `e`: error polynomial, sampled from discrete Gaussian distribution.
/// * `k1`: scaled message polynomial.
/// * `r2is`: list of r2i polynomials for each i-th CRT basis .
/// * `r1is`: list of r1i polynomials for each CRT i-th CRT basis.
/// * `ais`: list of ai polynomials for each CRT i-th CRT basis.
/// * `ct0is`: list of ct0i (first component of the ciphertext cti) polynomials for each CRT i-th CRT basis.
#[derive(Deserialize, Clone)]
pub struct BfvSkEncryptionCircuit {
    s: Vec<String>,
    e: Vec<String>,
    k1: Vec<String>,
    r2is: Vec<Vec<String>>,
    r1is: Vec<Vec<String>>,
    ais: Vec<Vec<String>>,
    ct0is: Vec<Vec<String>>,
}

/// Payload returned by the first phase of the circuit to be reused in the second phase
pub struct Payload<F: ScalarField> {
    s_assigned: PolyAssigned<F>,
    e_assigned: PolyAssigned<F>,
    k1_assigned: PolyAssigned<F>,
    r2is_assigned: Vec<PolyAssigned<F>>,
    r1is_assigned: Vec<PolyAssigned<F>>,
    ais_assigned: Vec<PolyAssigned<F>>,
    ct0is_assigned: Vec<PolyAssigned<F>>,
}

impl<F: ScalarField> RlcCircuitInstructions<F> for BfvSkEncryptionCircuit {
    type FirstPhasePayload = Payload<F>;

    /// #### Phase 0

    /// In this phase, the polynomials for each matrix $S_i$ are assigned to the circuit. Namely:
    /// * polynomials `s`, `e`, `k1` are assigned to the witness table. This has to be done only once as these polynomial are common to each $S_i$ matrix
    /// * polynomials `r1i`, `r2i` are assigned to the witness table for each $S_i$ matrix
    /// * polynomials `ai`, `ct0i` are assigned to the witness table for each $S_i$ matrix and exposed as public inputs

    /// Witness values are element of the finite field $\mod{p}$. Negative coefficients $-z$ are assigned as field elements $p - z$.

    /// At the end of phase 0, the witness generated so far is interpolated into a polynomial and committed by the prover. The hash of this commitment is used as challenge and will be used as a source of randomness $\gamma$ in Phase 1. This feature is made available by Halo2 [Challenge API](https://hackmd.io/@axiom/SJw3p-qX3).
    fn virtual_assign_phase0(
        &self,
        builder: &mut RlcCircuitBuilder<F>,
        _: &RangeChip<F>,
    ) -> Self::FirstPhasePayload {
        let ctx = builder.base.main(0);

        let mut public_inputs = vec![];

        let s = Poly::<F>::new(self.s.clone());
        let s_assigned = PolyAssigned::new(ctx, s);

        let e = Poly::<F>::new(self.e.clone());
        let e_assigned = PolyAssigned::new(ctx, e);

        let k1 = Poly::<F>::new(self.k1.clone());
        let k1_assigned = PolyAssigned::new(ctx, k1);

        let mut r2is_assigned = vec![];
        let mut r1is_assigned = vec![];
        let mut ais_assigned = vec![];
        let mut ct0is_assigned = vec![];

        for z in 0..self.ct0is.len() {
            let r2i = Poly::<F>::new(self.r2is[z].clone());
            let r2i_assigned = PolyAssigned::new(ctx, r2i);
            r2is_assigned.push(r2i_assigned);

            let r1i = Poly::<F>::new(self.r1is[z].clone());
            let r1i_assigned = PolyAssigned::new(ctx, r1i);
            r1is_assigned.push(r1i_assigned);

            let ai = Poly::<F>::new(self.ais[z].clone());
            let ai_assigned = PolyAssigned::new(ctx, ai);
            ais_assigned.push(ai_assigned);

            let ct0i = Poly::<F>::new(self.ct0is[z].clone());
            let ct0i_assigned = PolyAssigned::new(ctx, ct0i);
            ct0is_assigned.push(ct0i_assigned);
        }

        // EXPOSE PUBLIC INPUTS ais and ct0is
        for ai in ais_assigned.iter() {
            public_inputs.push(ai.assigned_coefficients[0]);
        }

        // push each ct0i polynomial to the public inputs
        for ct0i in ct0is_assigned.iter() {
            public_inputs.push(ct0i.assigned_coefficients[0]);
        }

        builder.base.assigned_instances[0] = public_inputs;

        Payload {
            s_assigned,
            e_assigned,
            k1_assigned,
            r2is_assigned,
            r1is_assigned,
            ais_assigned,
            ct0is_assigned,
        }
    }

    /// #### Phase 1

    /// In this phase, the following two core constraints are enforced:

    /// - The coefficients of $S_i$ are in the expected range.  
    /// - $U_i(\gamma) \times S_i(\gamma) =Ct_{0,i}(\gamma)$

    /// ##### Range Check

    /// The coefficients of the private polynomials from each $i$-th matrix $S_i$ are checked to be in the correct range
    /// * Range check polynomials `s`, `e`, `k1`. This has to be done only once as these polynomial are common to each $S_i$ matrix
    /// * Range check polynomials `r1i`, `r2i` for each $S_i$ matrix

    /// Since negative coefficients `-z` are assigned as `p - z` to the circuit, this might result in very large coefficients. Performing the range check on such large coefficients requires large lookup tables. To avoid this, the coefficients (both negative and positive) are shifted by a constant to make them positive and then perform the range check.

    /// ##### Evaluation at $\gamma$ Constraint

    /// * Constrain the evaluation of the polynomials `s`, `e`, `k1` at $\gamma$. This has to be done only once as these polynomial are common to each $S_i$ matrix
    /// * Constrain the evaluation of the polynomials `r1i`, `r2i` at $\gamma$ for each $S_i$ matrix
    /// * Constrain the evaluation of the polynomials `ai` and `ct0i` at $\gamma$ for each $U_i$ matrix
    /// * Constrain the evaluation of the polynomials `cyclo` at $\gamma$ . This has to be done only once as the cyclotomic polynomial is common to each $U_i$ matrix

    /// ##### Correct Encryption Constraint

    /// It is needed to prove that $U_i(\gamma) \times S_i(\gamma) =Ct_{0,i}(\gamma)$. This can be rewritten as `ct0i = ct0i_hat + r1i * qi + r2i * cyclo`, where `ct0i_hat = ai * s + e + k1 * k0i`.

    /// This constrained is enforced by proving that `LHS(gamma) = RHS(gamma)`. According to the Schwartz-Zippel lemma, if this relation between polynomial when evaluated at a random point holds true, then then the polynomials are identical with high probability. Note that `qi` and `k0i` (for each $U_i$ matrix) are constants to the circuit encoded during key generation.
    /// * Constrain that `ct0i(gamma) = ai(gamma) * s(gamma) + e(gamma) + k1(gamma) * k0i + r1i(gamma) * qi + r2i(gamma) * cyclo(gamma)` for each $i$-th CRT basis
    fn virtual_assign_phase1(
        builder: &mut RlcCircuitBuilder<F>,
        range: &RangeChip<F>,
        rlc: &RlcChip<F>,
        payload: Self::FirstPhasePayload,
    ) {
        let Payload {
            s_assigned,
            e_assigned,
            k1_assigned,
            r2is_assigned,
            r1is_assigned,
            ais_assigned,
            ct0is_assigned,
        } = payload;

        let (ctx_gate, ctx_rlc) = builder.rlc_ctx_pair();
        let gate = range.gate();

        let mut qi_constants = vec![];
        let mut k0i_constants = vec![];

        for z in 0..ct0is_assigned.len() {
            let qi_constant = Constant(F::from_str_vartime(QIS[z]).unwrap());
            qi_constants.push(qi_constant);

            let k0i_constant = Constant(F::from_str_vartime(K0IS[z]).unwrap());
            k0i_constants.push(k0i_constant);
        }

        s_assigned.range_check(ctx_gate, range, S_BOUND);
        e_assigned.range_check(ctx_gate, range, E_BOUND);
        k1_assigned.range_check(ctx_gate, range, K1_BOUND);

        for z in 0..ct0is_assigned.len() {
            r2is_assigned[z].range_check(ctx_gate, range, R2_BOUNDS[z]);
            r1is_assigned[z].range_check(ctx_gate, range, R1_BOUNDS[z]);
        }

        // EVALUATION AT GAMMA CONSTRAINT

        let bits_used = usize::BITS as usize - N.leading_zeros() as usize;
        rlc.load_rlc_cache((ctx_gate, ctx_rlc), gate, bits_used);
        let cyclo_at_gamma_assigned = rlc.rlc_pow_fixed(ctx_gate, gate, N);
        let cyclo_at_gamma_assigned =
            gate.add(ctx_gate, cyclo_at_gamma_assigned, Constant(F::from(1)));

        let s_at_gamma = s_assigned.enforce_eval_at_gamma(ctx_rlc, rlc);
        let e_at_gamma = e_assigned.enforce_eval_at_gamma(ctx_rlc, rlc);
        let k1_at_gamma = k1_assigned.enforce_eval_at_gamma(ctx_rlc, rlc);

        // For each `i` Prove that LHS(gamma) = RHS(gamma)
        // LHS = ct0i(gamma)
        // RHS = ai(gamma) * s(gamma) + e(gamma) + k1(gamma) * k0i + r1i(gamma) * qi + r2i(gamma) * cyclo(gamma)
        for z in 0..ct0is_assigned.len() {
            let r1i_at_gamma = r1is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);
            let r2i_at_gamma = r2is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);
            let ai_at_gamma = ais_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);
            let ct0i_at_gamma = ct0is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);

            // CORRECT ENCRYPTION CONSTRAINT

            // rhs = ai(gamma) * s(gamma) + e(gamma)
            let rhs = gate.mul_add(ctx_gate, ai_at_gamma, s_at_gamma, e_at_gamma);

            // rhs = rhs + k1(gamma) * k0i
            let rhs = gate.mul_add(ctx_gate, k1_at_gamma, k0i_constants[z], rhs);

            // rhs = rhs + r1i(gamma) * qi
            let rhs = gate.mul_add(ctx_gate, r1i_at_gamma, qi_constants[z], rhs);

            // rhs = rhs + r2i(gamma) * cyclo(gamma)
            let rhs = gate.mul_add(ctx_gate, r2i_at_gamma, cyclo_at_gamma_assigned, rhs);
            let lhs = ct0i_at_gamma;

            // LHS(gamma) = RHS(gamma)
            let res = gate.is_equal(ctx_gate, lhs, rhs);
            gate.assert_is_const(ctx_gate, &res, &F::from(1));
        }
    }

    fn instances(&self) -> Vec<Vec<F>> {
        let mut instance = vec![];
        for ai in self.ais.iter() {
            let ai_poly = Poly::<F>::new(ai.clone());
            instance.push(ai_poly.coefficients[0]);
        }
        for ct0i in self.ct0is.iter() {
            let ct0i_poly = Poly::<F>::new(ct0i.clone());
            instance.push(ct0i_poly.coefficients[0]);
        }
        vec![instance]
    }
}


impl <F:ScalarField, I> CircuitExt<F> for RlcCircuit<F, I>
  where                     
      I: RlcCircuitInstructions<F>,                                                               
  {                                                                              
      fn instances(&self) -> Vec<Vec<F>> {
          self.instances()  
      }                                          
                                                                                                                           
     // fn instances(&self) ->  Vec<Vec<F>>{                                                                                                     
     //     self.0.logic_inputs.instances()                                                                                                       
     // }                
                                                                                                                                                 
      fn num_instance(&self) -> Vec<usize> {                                                                                                     
          vec![1 as usize]                                                                                                       
      }                                         
  }
