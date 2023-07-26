use crate::keccak_stark::{KeccakStark, NUM_ROUNDS};
use itertools::Itertools;
use plonky2::{
    field::extension::Extendable,
    field::types::Field,
    hash::hash_types::RichField,
    iop::{
        target::{BoolTarget, Target},
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
use tiny_keccak::keccakf;

pub fn keccakf_u32(input: [u32; 50]) -> [u32; 50] {
    let mut state = input
        .chunks(2)
        .map(|chunk| chunk[0] as u64 + ((chunk[1] as u64) << 32))
        .collect_vec()
        .try_into()
        .unwrap();
    keccakf(&mut state);
    let output = state
        .iter()
        .flat_map(|&x| vec![x as u32, (x >> 32) as u32])
        .collect_vec();
    output.try_into().unwrap()
}

pub fn keccak256(input: Vec<u32>) -> ([u32; 8], Vec<u32>) {
    let mut pi = vec![];
    let block_size = 136 / 4;
    let num_blocks = input.len() / block_size + 1;
    let mut padded = vec![0u32; block_size * num_blocks];
    padded[0..input.len()].copy_from_slice(&input);
    padded[input.len()] = 0x01;
    *padded.last_mut().unwrap() ^= 0x80 << 24;
    let mut state = [0u32; 50];
    for i in 0..num_blocks {
        for j in 0..block_size {
            state[j] ^= padded[i * block_size + j];
        }
        let input = state;
        let output = keccakf_u32(input);
        pi.extend(input);
        pi.extend(output);
        state = output;
    }
    (state[0..8].try_into().unwrap(), pi)
}

pub fn solidity_keccak256(input: Vec<u32>) -> ([u32; 8], Vec<u32>) {
    let input = input
        .iter()
        .map(|v| u32::from_le_bytes(v.to_be_bytes()))
        .collect::<Vec<_>>();
    let (output, pi) = keccak256(input);
    let output = output.map(|v| u32::from_be_bytes(v.to_le_bytes()));

    (output, pi)
}

pub fn xor_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    x: Target,
    y: Target,
) -> Target {
    let x_bit = builder.split_le(x, 32);
    let y_bit = builder.split_le(y, 32);
    let z_bit = x_bit
        .iter()
        .zip(y_bit.iter())
        .map(|(&x, &y)| {
            let sum = builder.add(x.target, y.target);
            let z = builder.arithmetic(-F::TWO, F::ONE, x.target, y.target, sum);
            BoolTarget::new_unsafe(z)
        })
        .collect_vec();
    builder.le_sum(z_bit.into_iter())
}

pub fn keccak256_circuit_with_statements<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    input: Vec<Target>,
) -> ([Target; 8], Vec<Target>) {
    let mut pi: Vec<Target> = vec![];
    let zero = builder.zero();
    let one = builder.one();
    let c = builder.constant(F::from_canonical_u32(0x80 << 24));
    let block_size = 136 / 4;
    let num_blocks = input.len() / block_size + 1;
    let mut padded = vec![zero; block_size * num_blocks];
    padded[0..input.len()].copy_from_slice(&input);
    padded[input.len()] = one;
    *padded.last_mut().unwrap() = xor_circuit(builder, *padded.last().unwrap(), c);
    let mut state = [zero; 50];
    for i in 0..num_blocks {
        for j in 0..block_size {
            state[j] = xor_circuit(builder, state[j], padded[i * block_size + j]);
        }
        let input = state;
        let output = [(); 50].map(|_| builder.add_virtual_target());
        pi.extend(input);
        pi.extend(output);
        state = output;
    }
    (state[0..8].try_into().unwrap(), pi)
}

pub fn solidity_keccak256_circuit_with_statements<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    input: Vec<Target>,
) -> ([Target; 8], Vec<Target>) {
    let input = input
        .iter()
        .map(|v| {
            let w = builder.split_le(*v, 32);
            builder.le_sum(w.chunks(8).rev().flatten())
        })
        .collect::<Vec<_>>();
    let (output, pi) = keccak256_circuit_with_statements(builder, input);
    let output = output
        .map(|v| {
            let w = builder.split_le(v, 32);
            builder.le_sum(w.chunks(8).rev().flatten())
        });

    (output, pi)
}

const D: usize = 2;
type C = PoseidonGoldilocksConfig;
type F = <C as GenericConfig<D>>::F;

pub struct Keccak256Circuit {
    pub data: CircuitData<F, C, D>,
    pub stark_proof_t: StarkProofWithPublicInputsTarget<D>,
    pub input_t: Vec<Target>,
    pub output_t: [Target; 8],
}

pub fn build_keccak256_circuit(input_len: usize) -> Keccak256Circuit {
    let block_size = 136 / 4;
    let num_perms = input_len / block_size + 1;
    let degree_bits = (NUM_ROUNDS * num_perms)
        .next_power_of_two()
        .trailing_zeros() as usize;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = KeccakStark<F, D>;
    let stark = S {
        num_io: num_perms,
        f: Default::default(),
    };
    let inner_config = stark.config();
    let config = CircuitConfig::standard_recursion_config();
    let mut builder = CircuitBuilder::<F, D>::new(config);
    let input_t = builder.add_virtual_targets(input_len);
    let (output_t, pi_t) = keccak256_circuit_with_statements(&mut builder, input_t.clone());
    let stark_proof_t =
        add_virtual_stark_proof_with_pis(&mut builder, stark, &inner_config, degree_bits);
    verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, &stark_proof_t, &inner_config);
    pi_t.iter()
        .zip(stark_proof_t.public_inputs.iter())
        .for_each(|(x, y)| {
            builder.connect(*x, *y);
        });

    let input_and_output = [input_t.as_slice(), &output_t].concat();
    builder.register_public_inputs(&input_and_output);
    let data = builder.build::<C>();

    Keccak256Circuit {
        data,
        stark_proof_t,
        input_t,
        output_t,
    }
}

pub fn generate_keccak256_proof(
    input: Vec<u32>,
    circuit: &Keccak256Circuit,
) -> ProofWithPublicInputs<F, C, D> {
    let block_size = 136 / 4;
    let num_perms = input.len() / block_size + 1;

    let (output, pi) = keccak256(input.clone());
    let mut inputs = vec![];
    for i in 0..num_perms {
        let input = pi[i * 100..i * 100 + 50].to_vec();
        let input = input
            .chunks(2)
            .map(|chunk| chunk[0] as u64 + ((chunk[1] as u64) << 32))
            .collect_vec();
        inputs.push(input.try_into().unwrap());
    }

    type S = KeccakStark<F, D>;
    let stark = S {
        num_io: num_perms,
        f: Default::default(),
    };
    let inner_config = stark.config();
    let trace = stark.generate_trace(inputs.try_into().unwrap(), 8);
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
    input
        .iter()
        .zip(circuit.input_t.iter())
        .for_each(|(w, t)| pw.set_target(*t, F::from_canonical_u32(*w)));
    // set outputs
    output
        .iter()
        .zip(circuit.output_t.iter())
        .for_each(|(w, t)| pw.set_target(*t, F::from_canonical_u32(*w)));
    let proof = circuit.data.prove(pw).unwrap();
    proof
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use super::{build_keccak256_circuit, generate_keccak256_proof, keccak256};
    use crate::keccak256_circuit::{keccak256_circuit_with_statements, xor_circuit};
    use itertools::Itertools;
    use plonky2::field::types::Field;
    use plonky2::iop::witness::{PartialWitness, WitnessWrite};
    use plonky2::plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::CircuitConfig,
        config::{GenericConfig, PoseidonGoldilocksConfig},
    };
    use rand::Rng;
    use tiny_keccak::{Hasher, Keccak};

    #[test]
    fn test_keccak256() {
        let mut rng = rand::thread_rng();
        let input = vec![rng.gen(); 33];
        let (output, _pi) = keccak256(input.clone());
        let output_expected: [u32; 8] = {
            let mut hasher = Keccak::v256();
            let mut output = [0u8; 32];
            let input = input
                .iter()
                .flat_map(|&x| vec![x as u8, (x >> 8) as u8, (x >> 16) as u8, (x >> 24) as u8])
                .collect_vec();
            hasher.update(&input);
            hasher.finalize(&mut output);
            let output = output
                .chunks(4)
                .map(|chunk| {
                    let mut res = 0u32;
                    for i in 0..4 {
                        res += (chunk[i] as u32) << (8 * i);
                    }
                    res
                })
                .collect_vec();
            output.try_into().unwrap()
        };
        assert!(output == output_expected);
    }

    #[test]
    fn test_xor_u32() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x = builder.constant(F::from_canonical_u32(0x12345678));
        let y = builder.constant(F::from_canonical_u32(0x87654321));
        let z = xor_circuit(&mut builder, x, y);
        let z_expected = F::from_canonical_u32(0x12345678 ^ 0x87654321);

        let mut pw = PartialWitness::<F>::new();
        pw.set_target(z, z_expected);
        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }

    #[test]
    fn test_statement_keccak256_circuit() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let mut rng = rand::thread_rng();
        let input = vec![rng.gen(); 3545];
        let (output, pi) = keccak256(input.clone());

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);

        let input_t = input
            .iter()
            .map(|x| builder.constant(F::from_canonical_u32(*x)))
            .collect_vec();
        let (output_t, pi_t) = keccak256_circuit_with_statements(&mut builder, input_t.clone());
        let mut pw = PartialWitness::<F>::new();
        output
            .iter()
            .zip(output_t.iter())
            .for_each(|(w, t)| pw.set_target(*t, F::from_canonical_u32(*w)));
        pi.iter()
            .zip(pi_t.iter())
            .for_each(|(w, t)| pw.set_target(*t, F::from_canonical_u32(*w)));

        let data = builder.build::<C>();
        let _proof = data.prove(pw).unwrap();
    }

    #[test]
    fn test_keccak256_circuit() {
        let input_len: usize = 256 * 4;
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let circuit = build_keccak256_circuit(input_len);
        let mut rng = rand::thread_rng();
        let input: Vec<u32> = vec![rng.gen(); input_len];

        let now = Instant::now();
        let proof = generate_keccak256_proof(input.clone(), &circuit);
        println!("proof generation took {:?}", now.elapsed());

        // assertion
        {
            let (output, _pi) = keccak256(input.clone());
            let input_and_output = [input.as_slice(), &output]
                .concat()
                .iter()
                .map(|x| F::from_canonical_u32(*x))
                .collect_vec();
            assert!(proof.public_inputs == input_and_output);
        }
    }
}
