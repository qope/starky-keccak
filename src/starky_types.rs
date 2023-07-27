use std::{fmt::Debug, ops::Deref};

use plonky2::{
    field::extension::Extendable,
    fri::{
        structure::{FriOpeningBatch, FriOpeningBatchTarget, FriOpenings, FriOpeningsTarget},
        witness_util::set_fri_proof_target,
    },
    hash::hash_types::RichField,
    iop::witness::WitnessWrite,
    plonk::config::{AlgebraicHasher, GenericConfig},
};
use starky::proof::{
    StarkOpeningSet, StarkOpeningSetTarget, StarkProof, StarkProofTarget,
    StarkProofWithPublicInputs, StarkProofWithPublicInputsTarget,
};

pub struct WrappedStarkOpeningSetTarget<'a, const D: usize>(pub &'a StarkOpeningSetTarget<D>);

impl<'a, const D: usize> Deref for WrappedStarkOpeningSetTarget<'a, D> {
    type Target = StarkOpeningSetTarget<D>;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'a, const D: usize> Debug for WrappedStarkOpeningSetTarget<'a, D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StarkOpeningSet")
            .field("local_values", &self.local_values)
            .field("next_values", &self.next_values)
            .field("permutation_zs", &self.permutation_zs)
            .field("permutation_zs_next", &self.permutation_zs_next)
            .field("quotient_polys", &self.quotient_polys)
            .finish()
    }
}

pub struct WrappedStarkProofTarget<'a, const D: usize>(pub &'a StarkProofTarget<D>);

impl<'a, const D: usize> Deref for WrappedStarkProofTarget<'a, D> {
    type Target = StarkProofTarget<D>;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'a, const D: usize> Debug for WrappedStarkProofTarget<'a, D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StarkProof")
            .field("trace_cap", &self.trace_cap)
            .field("permutation_zs_cap", &self.permutation_zs_cap)
            .field("quotient_polys_cap", &self.quotient_polys_cap)
            .field("openings", &WrappedStarkOpeningSetTarget(&self.openings))
            .field("opening_proof", &self.opening_proof)
            .finish()
    }
}

pub struct WrappedStarkProofWithPublicInputsTarget<'a, const D: usize>(
    pub &'a StarkProofWithPublicInputsTarget<D>,
);

impl<'a, const D: usize> Deref for WrappedStarkProofWithPublicInputsTarget<'a, D> {
    type Target = StarkProofWithPublicInputsTarget<D>;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl<'a, const D: usize> Debug for WrappedStarkProofWithPublicInputsTarget<'a, D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StarkProofWithPublicInputsTarget")
            .field("proof", &WrappedStarkProofTarget(&self.proof))
            .field("public_inputs", &self.public_inputs)
            .finish()
    }
}

pub fn set_stark_proof_with_pis_target<F, C: GenericConfig<D, F = F>, W, const D: usize>(
    witness: &mut W,
    stark_proof_with_pis_target: &StarkProofWithPublicInputsTarget<D>,
    stark_proof_with_pis: &StarkProofWithPublicInputs<F, C, D>,
) where
    F: RichField + Extendable<D>,
    C::Hasher: AlgebraicHasher<F>,
    W: WitnessWrite<F>,
{
    let StarkProofWithPublicInputs {
        proof,
        public_inputs,
    } = stark_proof_with_pis;
    let StarkProofWithPublicInputsTarget {
        proof: pt,
        public_inputs: pi_targets,
    } = stark_proof_with_pis_target;

    // Set public inputs.
    assert_eq!(pi_targets.len(), public_inputs.len());
    for (&pi_t, &pi) in pi_targets.iter().zip(public_inputs) {
        witness.set_target(pi_t, pi);
    }

    set_stark_proof_target(witness, pt, proof);
}

pub fn to_fri_openings<F: RichField + Extendable<D>, const D: usize>(
    openings: &StarkOpeningSet<F, D>,
) -> FriOpenings<F, D> {
    let zeta_batch = FriOpeningBatch {
        values: openings
            .local_values
            .iter()
            .chain(openings.permutation_zs.iter().flatten())
            .chain(&openings.quotient_polys)
            .copied()
            .collect::<Vec<_>>(),
    };
    let zeta_next_batch = FriOpeningBatch {
        values: openings
            .next_values
            .iter()
            .chain(openings.permutation_zs_next.iter().flatten())
            .copied()
            .collect::<Vec<_>>(),
    };

    FriOpenings {
        batches: vec![zeta_batch, zeta_next_batch],
    }
}

pub fn to_fri_openings_target<const D: usize>(
    openings: &StarkOpeningSetTarget<D>,
) -> FriOpeningsTarget<D> {
    let zeta_batch = FriOpeningBatchTarget {
        values: openings
            .local_values
            .iter()
            .chain(openings.permutation_zs.iter().flatten())
            .chain(&openings.quotient_polys)
            .copied()
            .collect::<Vec<_>>(),
    };
    let zeta_next_batch = FriOpeningBatchTarget {
        values: openings
            .next_values
            .iter()
            .chain(openings.permutation_zs_next.iter().flatten())
            .copied()
            .collect::<Vec<_>>(),
    };

    FriOpeningsTarget {
        batches: vec![zeta_batch, zeta_next_batch],
    }
}

pub fn set_stark_proof_target<F, C: GenericConfig<D, F = F>, W, const D: usize>(
    witness: &mut W,
    proof_target: &StarkProofTarget<D>,
    proof: &StarkProof<F, C, D>,
) where
    F: RichField + Extendable<D>,
    C::Hasher: AlgebraicHasher<F>,
    W: WitnessWrite<F>,
{
    witness.set_cap_target(&proof_target.trace_cap, &proof.trace_cap);
    witness.set_cap_target(&proof_target.quotient_polys_cap, &proof.quotient_polys_cap);

    witness.set_fri_openings(
        &to_fri_openings_target(&proof_target.openings),
        &to_fri_openings(&proof.openings),
    );

    if let (Some(permutation_zs_cap_target), Some(permutation_zs_cap)) =
        (&proof_target.permutation_zs_cap, &proof.permutation_zs_cap)
    {
        witness.set_cap_target(permutation_zs_cap_target, permutation_zs_cap);
    }

    set_fri_proof_target(witness, &proof_target.opening_proof, &proof.opening_proof);
}
