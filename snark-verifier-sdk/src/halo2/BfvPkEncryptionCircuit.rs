

use crate::constants::pk_enc_constants_1024_15x60_65537::{E_BOUND, K0IS, N, PK_BOUND, QIS, R1_BOUNDS, R2_BOUNDS, P1_BOUNDS, P2_BOUNDS, U_BOUND, K1_BOUND, };

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


#[derive(Deserialize, Clone)]
pub struct BfvPkEncryptionCircuit {
    pk0i: Vec<Vec<String>>,
    pk1i: Vec<Vec<String>>,
    pub u: Vec<String>,
    e0: Vec<String>,
    e1: Vec<String>,
    k1: Vec<String>,
    r2is: Vec<Vec<String>>,
    pub r1is: Vec<Vec<String>>,
    p2is: Vec<Vec<String>>,
    p1is: Vec<Vec<String>>,
    ct0is: Vec<Vec<String>>,
    ct1is: Vec<Vec<String>>,
}

pub struct Payload<F: ScalarField> {
    pk0i_assigned: Vec<PolyAssigned<F>>,
    pk1i_assigned: Vec<PolyAssigned<F>>,
    u_assigned: PolyAssigned<F>,
    e0_assigned: PolyAssigned<F>,
    e1_assigned: PolyAssigned<F>,
    k1_assigned: PolyAssigned<F>,
    r2is_assigned: Vec<PolyAssigned<F>>,
    r1is_assigned: Vec<PolyAssigned<F>>,
    p2is_assigned: Vec<PolyAssigned<F>>,
    p1is_assigned: Vec<PolyAssigned<F>>,
    ct0is_assigned: Vec<PolyAssigned<F>>,
    ct1is_assigned: Vec<PolyAssigned<F>>,
}

impl<F: ScalarField> RlcCircuitInstructions<F> for BfvPkEncryptionCircuit {
    type FirstPhasePayload = Payload<F>;

    /// #### Phase 0

    /// In this phase, the polynomials for each matrix $S_i$ are assigned to the circuit. Namely:
    /// * polynomials `u`,'e1, `e0`, `k1`, `pk0i`,`pk1_q1` are assigned to the witness table. This has to be done only once as these polynomial are common to each $S_i$ matrix
    /// * polynomials `r1i`, `r2i`,`p1i`,`p2i` are assigned to the witness table for each $S_i$ matrix
    /// * polynomials 'ct0is' and 'ct1is` are assigned to the witness table for each $Ct_i$

    /// Witness values are element of the finite field $\mod{p}$. Negative coefficients $-z$ are assigned as field elements $p - z$.

    /// At the end of phase 0, the witness generated so far is interpolated into a polynomial and committed by the prover. The hash of this commitment is used as challenge and will be used as a source of randomness $\gamma$ in Phase 1. This feature is made available by Halo2 [Challenge API](https://hackmd.io/@axiom/SJw3p-qX3).

    fn virtual_assign_phase0(
        &self,
        builder: &mut RlcCircuitBuilder<F>,
        _: &RangeChip<F>,
    ) -> Self::FirstPhasePayload {
        let ctx = builder.base.main(0);

        let mut public_inputs = vec![];

        let pk0i = self
            .pk0i
            .iter()
            .map(|pk0i| Poly::<F>::new(pk0i.clone()))
            .collect::<Vec<_>>();
        let pk0i_assigned = pk0i
            .into_iter()
            .map(|pk0i| PolyAssigned::new(ctx, pk0i))
            .collect::<Vec<_>>();

        let pk1i = self
            .pk1i
            .iter()
            .map(|pk1i| Poly::<F>::new(pk1i.clone()))
            .collect::<Vec<_>>();
        let pk1i_assigned = pk1i
            .into_iter()
            .map(|pk1i| PolyAssigned::new(ctx, pk1i))
            .collect::<Vec<_>>();

        let u = Poly::<F>::new(self.u.clone());
        let u_assigned = PolyAssigned::new(ctx, u);

        let e0 = Poly::<F>::new(self.e0.clone());
        let e0_assigned = PolyAssigned::new(ctx, e0);

        let e1 = Poly::<F>::new(self.e1.clone());
        let e1_assigned = PolyAssigned::new(ctx, e1);

        let k1 = Poly::<F>::new(self.k1.clone());
        let k1_assigned = PolyAssigned::new(ctx, k1);

        let r1is_assigned = self
            .r1is
            .iter()
            .map(|r1is| {
                let r1is = Poly::<F>::new(r1is.clone());
                PolyAssigned::new(ctx, r1is)
            })
            .collect::<Vec<_>>();

        let r2is_assigned = self
            .r2is
            .iter()
            .map(|r2is| {
                let r2is = Poly::<F>::new(r2is.clone());
                PolyAssigned::new(ctx, r2is)
            })
            .collect::<Vec<_>>();

        let p1is_assigned = self
            .p1is
            .iter()
            .map(|p1is| {
                let p1is = Poly::<F>::new(p1is.clone());
                PolyAssigned::new(ctx, p1is)
            })
            .collect::<Vec<_>>();

        let p2is_assigned = self
            .p2is
            .iter()
            .map(|p2is| {
                let p2is = Poly::<F>::new(p2is.clone());
                PolyAssigned::new(ctx, p2is)
            })
            .collect::<Vec<_>>();

        let ct0is_assigned = self
            .ct0is
            .iter()
            .map(|ct0is| {
                let ct0is = Poly::<F>::new(ct0is.clone());
                PolyAssigned::new(ctx, ct0is)
            })
            .collect::<Vec<_>>();

        let ct1is_assigned = self
            .ct1is
            .iter()
            .map(|ct1is| {
                let ct1is = Poly::<F>::new(ct1is.clone());
                PolyAssigned::new(ctx, ct1is)
            })
            .collect::<Vec<_>>();

        for pk0 in pk0i_assigned.iter() {
            public_inputs.push(pk0.assigned_coefficients[0]);
        }
        for pk1 in pk1i_assigned.iter() {
            public_inputs.push(pk1.assigned_coefficients[0]);
        }
        for ct0 in ct0is_assigned.iter() {
            public_inputs.push(ct0.assigned_coefficients[0]);
        }
        for ct1 in ct1is_assigned.iter() {
            public_inputs.push(ct1.assigned_coefficients[0]);
        }

        builder.base.assigned_instances[0] = public_inputs;

        Payload {
            pk0i_assigned,
            pk1i_assigned,
            u_assigned,
            e0_assigned,
            e1_assigned,
            k1_assigned,
            r2is_assigned,
            r1is_assigned,
            p2is_assigned,
            p1is_assigned,
            ct0is_assigned,
            ct1is_assigned,
        }
    }

    fn virtual_assign_phase1(
        builder: &mut RlcCircuitBuilder<F>,
        range: &RangeChip<F>,
        rlc: &RlcChip<F>,
        payload: Self::FirstPhasePayload,
    ) {
        let Payload {
            pk0i_assigned,
            pk1i_assigned,
            u_assigned,
            e0_assigned,
            e1_assigned,
            k1_assigned,
            r2is_assigned,
            r1is_assigned,
            p2is_assigned,
            p1is_assigned,
            ct0is_assigned,
            ct1is_assigned,
        } = payload;

        // ASSIGNMENT

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

        // cyclo poly is equal to x^N + 1
        let bits_used = (usize::BITS as usize) - (N.leading_zeros() as usize);
        rlc.load_rlc_cache((ctx_gate, ctx_rlc), gate, bits_used);
        let cyclo_at_gamma_assigned = rlc.rlc_pow_fixed(ctx_gate, gate, N);
        let cyclo_at_gamma_assigned =
            gate.add(ctx_gate, cyclo_at_gamma_assigned, Constant(F::from(1)));

        u_assigned.range_check(ctx_gate, range, U_BOUND);
        e0_assigned.range_check(ctx_gate, range, E_BOUND);
        e1_assigned.range_check(ctx_gate, range, E_BOUND);
        k1_assigned.range_check(ctx_gate, range, K1_BOUND);

        let _ = pk0i_assigned
            .iter()
            .enumerate()
            .map(|(i, pk_assigned)| pk_assigned.range_check(ctx_gate, range, PK_BOUND[i]));

        let _ = pk1i_assigned
            .iter()
            .enumerate()
            .map(|(i, pk_assigned)| pk_assigned.range_check(ctx_gate, range, PK_BOUND[i]));

        for z in 0..ct0is_assigned.len() {
            r2is_assigned[z].range_check(ctx_gate, range, R2_BOUNDS[z]);
            r1is_assigned[z].range_check(ctx_gate, range, R1_BOUNDS[z]);
            p2is_assigned[z].range_check(ctx_gate, range, P2_BOUNDS[z]);
            p1is_assigned[z].range_check(ctx_gate, range, P1_BOUNDS[z]);
        }

        let u_at_gamma = u_assigned.enforce_eval_at_gamma(ctx_rlc, rlc);
        let e0_at_gamma = e0_assigned.enforce_eval_at_gamma(ctx_rlc, rlc);
        let e1_at_gamma = e1_assigned.enforce_eval_at_gamma(ctx_rlc, rlc);
        let k1_at_gamma = k1_assigned.enforce_eval_at_gamma(ctx_rlc, rlc);
        let pk0i_at_gamma = pk0i_assigned
            .iter()
            .map(|pk_assigned| pk_assigned.enforce_eval_at_gamma(ctx_rlc, rlc))
            .collect::<Vec<_>>();
        let pk1i_at_gamma = pk1i_assigned
            .iter()
            .map(|pk_assigned| pk_assigned.enforce_eval_at_gamma(ctx_rlc, rlc))
            .collect::<Vec<_>>();
        let gate = range.gate();

        // For each `i` Prove that LHS(gamma) = RHS(gamma)
        // pk0_u = pk0i(gamma) * u(gamma) + e0(gamma)
        // LHS = ct0i(gamma)
        // RHS = pk0_u  + k1(gamma) * k0i + r1i(gamma) * qi + r2i(gamma) * cyclo(gamma)

        for z in 0..ct0is_assigned.len() {
            let pk0_u = gate.mul_add(ctx_gate, pk0i_at_gamma[z], u_at_gamma, e0_at_gamma);
            let r1i_at_gamma = r1is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);
            let r2i_at_gamma = r2is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);

            // CORRECT ENCRYPTION CONSTRAINT

            // rhs = pk0_u + k1(gamma) * k0i
            let rhs = gate.mul_add(ctx_gate, k1_at_gamma, k0i_constants[z], pk0_u);

            // rhs = rhs + r1i(gamma) * qi
            let rhs = gate.mul_add(ctx_gate, r1i_at_gamma, qi_constants[z], rhs);

            // rhs = rhs + r2i(gamma) * cyclo(gamma)
            let rhs = gate.mul_add(ctx_gate, r2i_at_gamma, cyclo_at_gamma_assigned, rhs);
            let lhs = ct0is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);

            // LHS(gamma) = RHS(gamma)
            let res = gate.is_equal(ctx_gate, lhs, rhs);
            gate.assert_is_const(ctx_gate, &res, &F::from(1));
        }

        for z in 0..ct1is_assigned.len() {
            let pk1_u = gate.mul_add(ctx_gate, pk1i_at_gamma[z], u_at_gamma, e1_at_gamma);

            let p1i_at_gamma = p1is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);
            let p2i_at_gamma = p2is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);

            //rhs = pk1_u + p2i * cyclo(gamma)
            let rhs = gate.mul_add(ctx_gate, p2i_at_gamma, cyclo_at_gamma_assigned, pk1_u);

            //rhs = rhs + p1s * qi
            let rhs = gate.mul_add(ctx_gate, p1i_at_gamma, qi_constants[z], rhs);

            let lhs = ct1is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);

            let res = gate.is_equal(ctx_gate, lhs, rhs);
            gate.assert_is_const(ctx_gate, &res, &F::from(1));
        }
    }

    fn instances(&self) -> Vec<Vec<F>> {
        let mut instance = vec![];
        for pk0 in self.pk0i.iter() {
            let pk0_poly = Poly::<F>::new(pk0.clone());
            instance.push(pk0_poly.coefficients[0]);
        }
        for pk1 in self.pk1i.iter() {
            let pk1_poly = Poly::<F>::new(pk1.clone());
            instance.push(pk1_poly.coefficients[0]);
        }
        for ct0i in self.ct0is.iter() {
            let ct0i_poly = Poly::<F>::new(ct0i.clone());
            instance.push(ct0i_poly.coefficients[0]);
        }
        for ct1i in self.ct1is.iter() {
            let ct1i_poly = Poly::<F>::new(ct1i.clone());
            instance.push(ct1i_poly.coefficients[0]);
        }
        vec![instance]
    }
}


impl <F:ScalarField, I> CircuitExt<F> for RlcCircuit<F, I>
  where                     
      I: RlcCircuitInstructions<F>,                                                               
  {                                                                              
      fn instances(&self) ->  Vec<Vec<F>>{                                                                                                     
          self.0.logic_inputs.instances()                                                                                                       
      }                
      fn num_instance(&self) -> Vec<usize> {
        let instances = self.instances(); 
        instances.iter().map(Vec::len).collect() // Compute lengths of each inner vector
      }
     // fn num_instance(&self) -> Vec<usize> {                                                                                                     
     //     vec![4 as usize]                                                                                                       
     // }                                         
  }