use itertools::Itertools;
use plonky2::{
    field::extension::Extendable,
    field::types::Field,
    hash::hash_types::RichField,
    iop::{
        target::Target,
        witness::{PartialWitness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData},
        config::{GenericConfig, PoseidonGoldilocksConfig},
        proof::ProofWithPublicInputs,
    },
    util::timing::TimingTree,
};
use starky::{
    proof::StarkProofWithPublicInputsTarget,
    prover::prove,
    recursive_verifier::{
        add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
        verify_stark_proof_circuit,
    },
    verifier::verify_stark_proof,
};

use crate::{
    keccak256_circuit::{keccak256, keccak256_circuit_with_statements, solidity_keccak256, solidity_keccak256_circuit_with_statements},
    keccak_stark::{KeccakStark, NUM_INPUTS, NUM_ROUNDS},
};

pub fn multi_keccak256(inputs: Vec<Vec<u32>>) -> (Vec<[u32; 8]>, Vec<u32>) {
    let mut outputs = vec![];
    let mut pi = vec![];
    for input in inputs {
        let (output, input_pi) = keccak256(input);
        outputs.push(output);
        pi.extend(input_pi);
    }
    (outputs, pi)
}

pub fn multi_solidity_keccak256(inputs: Vec<Vec<u32>>) -> (Vec<[u32; 8]>, Vec<u32>) {
    let mut outputs = vec![];
    let mut pi = vec![];
    for input in inputs {
        let (output, input_pi) = solidity_keccak256(input);
        outputs.push(output);
        pi.extend(input_pi);
    }
    (outputs, pi)
}

pub fn multi_keccak256_circuit_with_statements<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    inputs: Vec<Vec<Target>>,
) -> (Vec<[Target; 8]>, Vec<Target>) {
    let mut pi: Vec<Target> = vec![];
    let mut outputs = vec![];
    for input in inputs {
        let (output, pi_t) = keccak256_circuit_with_statements(builder, input);
        outputs.push(output);
        pi.extend(pi_t);
    }
    (outputs, pi)
}

pub fn multi_solidity_keccak256_circuit_with_statements<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    inputs: Vec<Vec<Target>>,
) -> (Vec<[Target; 8]>, Vec<Target>) {
    let mut pi: Vec<Target> = vec![];
    let mut outputs = vec![];
    for input in inputs {
        let (output, pi_t) = solidity_keccak256_circuit_with_statements(builder, input);
        outputs.push(output);
        pi.extend(pi_t);
    }
    (outputs, pi)
}

pub struct MultiKeccak256Circuit<F, C, const D: usize>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
{
    pub data: CircuitData<F, C, D>,
    pub stark_proof_t: StarkProofWithPublicInputsTarget<D>,
    pub inputs_t: Vec<Vec<Target>>,
    pub outputs_t: Vec<[Target; 8]>,
}

const D: usize = 2;
type C = PoseidonGoldilocksConfig;
type F = <C as GenericConfig<D>>::F;

pub fn build_multi_keccak256_circuit(input_lens: Vec<usize>) -> MultiKeccak256Circuit<F, C, D> {
    let block_size = 136 / 4;
    let num_perms: usize = input_lens
        .iter()
        .map(|input_len| input_len / block_size + 1)
        .sum();
    let degree_bits = (NUM_ROUNDS * num_perms)
        .next_power_of_two()
        .trailing_zeros() as usize;
    type S = KeccakStark<F, D>;
    let stark = S::new(num_perms);
    let inner_config = stark.config();
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let inputs_t = input_lens
        .iter()
        .map(|&input_len| builder.add_virtual_targets(input_len))
        .collect_vec();
    let (outputs_t, pi_t) = multi_keccak256_circuit_with_statements(&mut builder, inputs_t.clone());
    let stark_proof_t =
        add_virtual_stark_proof_with_pis(&mut builder, stark, &inner_config, degree_bits);
    verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, &stark_proof_t, &inner_config);
    pi_t.iter()
        .zip(stark_proof_t.public_inputs.iter())
        .for_each(|(x, y)| {
            builder.connect(*x, *y);
        });

    let inputs_and_outputs = inputs_t
        .iter()
        .zip(outputs_t.iter())
        .flat_map(|(input_t, output_t)| [input_t.as_slice(), output_t].concat())
        .collect_vec();
    builder.register_public_inputs(&inputs_and_outputs);
    let data = builder.build::<C>();

    MultiKeccak256Circuit {
        data,
        stark_proof_t,
        inputs_t,
        outputs_t,
    }
}

pub fn generate_multi_keccak256_proof(
    inputs: Vec<Vec<u32>>,
    circuit: &MultiKeccak256Circuit<F, C, D>,
) -> ProofWithPublicInputs<F, C, D> {
    let block_size = 136 / 4;
    let num_perms: usize = inputs
        .iter()
        .map(|input| input.len() / block_size + 1)
        .sum();

    let (outputs, pi) = multi_keccak256(inputs.clone());
    let mut perm_inputs: Vec<[u64; NUM_INPUTS]> = vec![];
    for i in 0..num_perms {
        let perm_input = pi[i * 100..i * 100 + 50].to_vec();
        let perm_input = perm_input
            .chunks(2)
            .map(|chunk| chunk[0] as u64 + ((chunk[1] as u64) << 32))
            .collect_vec();
        perm_inputs.push(perm_input.try_into().unwrap());
    }

    type S = KeccakStark<F, D>;
    let stark = S::new(num_perms);
    let inner_config = stark.config();
    let trace = stark.generate_trace(perm_inputs, 8);
    let pi = pi.iter().map(|x| F::from_canonical_u32(*x)).collect_vec();
    let inner_proof = prove::<F, C, S, D>(
        stark,
        &inner_config,
        trace,
        pi.try_into().unwrap(),
        &mut TimingTree::default(),
    )
    .unwrap();
    verify_stark_proof(stark, inner_proof.clone(), &inner_config).unwrap();

    let mut pw = PartialWitness::new();
    set_stark_proof_with_pis_target(&mut pw, &circuit.stark_proof_t, &inner_proof);
    // set inputs
    inputs
        .iter()
        .zip(circuit.inputs_t.iter())
        .for_each(|(input, input_t)| {
            input
                .iter()
                .zip(input_t.iter())
                .for_each(|(w, t)| pw.set_target(*t, F::from_canonical_u32(*w)))
        });
    // set outputs
    outputs
        .iter()
        .zip(circuit.outputs_t.iter())
        .for_each(|(output, output_t)| {
            output
                .iter()
                .zip(output_t.iter())
                .for_each(|(w, t)| pw.set_target(*t, F::from_canonical_u32(*w)))
        });
    let proof = circuit.data.prove(pw).unwrap();
    proof
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use itertools::Itertools;
    use plonky2::field::{goldilocks_field::GoldilocksField, types::Field};
    use rand::Rng;

    use crate::multi_keccak256_circuit::{
        build_multi_keccak256_circuit, generate_multi_keccak256_proof, multi_keccak256,
    };

    #[test]
    fn test_multi_keccak256_circuit() {
        let input_lens: Vec<usize> = vec![256, 1, 20];

        let circuit = build_multi_keccak256_circuit(input_lens.clone());
        let mut rng = rand::thread_rng();
        let inputs: Vec<Vec<u32>> = input_lens
            .iter()
            .map(|&input_len| vec![rng.gen(); input_len])
            .collect_vec();

        let now = Instant::now();
        let proof = generate_multi_keccak256_proof(inputs.clone(), &circuit);
        println!("proof generation took {:?}", now.elapsed());

        // assertion
        {
            let (outputs, _pi) = multi_keccak256(inputs.clone());
            let inputs_and_outputs = inputs
                .iter()
                .zip(outputs.iter())
                .flat_map(|(input, output)| [input.as_slice(), output].concat())
                .map(GoldilocksField::from_canonical_u32)
                .collect_vec();
            assert!(proof.public_inputs == inputs_and_outputs);
        }
    }
}
