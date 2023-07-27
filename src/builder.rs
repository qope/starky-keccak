use plonky2::{
    field::extension::Extendable,
    hash::hash_types::RichField,
    iop::{
        generator::{GeneratedValues, SimpleGenerator},
        target::{BoolTarget, Target},
        witness::{PartitionWitness, Witness, WitnessWrite},
    },
    plonk::{
        circuit_builder::CircuitBuilder,
        circuit_data::{CircuitConfig, CircuitData},
        config::{AlgebraicHasher, GenericConfig},
    },
    util::timing::TimingTree,
};
use starky::{
    config::StarkConfig,
    proof::StarkProofWithPublicInputsTarget,
    recursive_verifier::{add_virtual_stark_proof_with_pis, verify_stark_proof_circuit},
    verifier::verify_stark_proof,
};
use tiny_keccak::{Hasher, Keccak};

use crate::{
    keccak_stark::KeccakStark,
    multi_keccak256_circuit::{multi_keccak256, multi_keccak256_circuit_with_statements},
    starky_types::{set_stark_proof_with_pis_target, WrappedStarkProofWithPublicInputsTarget},
};

pub const NUM_ROUNDS: usize = 24;
pub const BLOCK_SIZE: usize = 136 / 4;

type U32Target = Target;

pub(crate) fn u8_to_le_bits(num: u8) -> Vec<bool> {
    let mut result = Vec::with_capacity(8);
    let mut n = num;
    for _ in 0..8 {
        result.push(n & 1 == 1);
        n >>= 1;
    }

    result
}

pub(crate) fn le_bits_to_u8(input: &[bool]) -> u8 {
    let mut result = 0;
    for (i, b) in input.iter().enumerate() {
        if *b {
            result |= 1 << i;
        }
    }

    result
}

#[derive(Clone, Debug)]
pub struct Keccak256MockGenerator {
    pub input: Vec<BoolTarget>,
    pub output: [BoolTarget; 256],
}

impl<F: RichField> SimpleGenerator<F> for Keccak256MockGenerator {
    #[cfg(feature = "new-plonky2")]
    fn id(&self) -> String {
        "Keccak256MockGenerator".to_string()
    }

    fn dependencies(&self) -> Vec<Target> {
        self.input.iter().map(|t| t.target).collect()
    }

    // NOTICE: not generate constraints for the hash
    fn run_once(&self, witness: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let get_bool =
            |bool_target: BoolTarget| -> bool { witness.get_target(bool_target.target) == F::ONE };

        assert_eq!(self.input.len() % 8, 0);
        // assert_eq!(self.output.len(), 256);
        let input_le = self.input.iter().map(|v| get_bool(*v)).collect::<Vec<_>>();
        let input = input_le.chunks(8).map(le_bits_to_u8).collect::<Vec<_>>();

        let mut output = [0u8; 32];
        let mut hasher = Keccak::v256();
        hasher.update(&input);
        hasher.finalize(&mut output);

        let output_le = output
            .into_iter()
            .flat_map(u8_to_le_bits)
            .collect::<Vec<_>>();

        assert_eq!(self.output.len(), output_le.len());
        for (target, witness) in self.output.iter().zip(output_le.iter()) {
            out_buffer.set_bool_target(*target, *witness);
        }
    }

    #[cfg(feature = "new-plonky2")]
    fn serialize(&self, _dst: &mut Vec<u8>) -> plonky2::util::serialization::IoResult<()> {
        unimplemented!()
    }

    #[cfg(feature = "new-plonky2")]
    fn deserialize(
        _src: &mut plonky2::util::serialization::Buffer,
    ) -> plonky2::util::serialization::IoResult<Self> {
        unimplemented!()
    }
}

pub struct CircuitBuilderWithKeccak<F: RichField + Extendable<D>, const D: usize> {
    pub builder: CircuitBuilder<F, D>,
    pub(crate) keccak_io: Vec<(Vec<U32Target>, [U32Target; 8])>,
}

impl<F: RichField + Extendable<D>, const D: usize> std::ops::Deref
    for CircuitBuilderWithKeccak<F, D>
{
    type Target = CircuitBuilder<F, D>;

    fn deref(&self) -> &Self::Target {
        &self.builder
    }
}

impl<F: RichField + Extendable<D>, const D: usize> std::ops::DerefMut
    for CircuitBuilderWithKeccak<F, D>
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.builder
    }
}

impl<F: RichField + Extendable<D>, const D: usize> CircuitBuilderWithKeccak<F, D> {
    pub fn new(config: CircuitConfig) -> Self {
        Self {
            builder: CircuitBuilder::new(config),
            keccak_io: vec![],
        }
    }

    pub fn keccak256(&mut self, input: Vec<U32Target>) -> [U32Target; 8] {
        // NOTICE: The limbs of `output` are secure because these are constrained as 32-bit integers by the starky circuit.
        let output: [U32Target; 8] = [(); 8].map(|_| self.add_virtual_target());
        self.keccak_io.push((input, output));

        output
    }

    #[cfg(not(feature = "not-constrain-keccak"))]
    pub fn build<C>(mut self) -> CircuitData<F, C, D>
    where
        C: GenericConfig<D, F = F> + 'static,
        C::Hasher: AlgebraicHasher<F>,
    {
        if !self.keccak_io.is_empty() {
            let num_perms: usize = self
                .keccak_io
                .iter()
                .map(|(input, _output)| input.len() / BLOCK_SIZE + 1)
                .sum();

            // NOTICE: If `num_perms` is less than 3, it is more efficient to prove the case without using a starky.
            if num_perms < 3 {
                use plonky2_keccak256::keccak::keccak256_circuit;

                for (input, output) in self.keccak_io.iter() {
                    let input_le = input
                        .iter()
                        .flat_map(|v| {
                            let w = self.builder.split_le(*v, 32);
                            w.chunks(8).rev().flatten().cloned().collect::<Vec<_>>()
                        })
                        .collect(); // TODO: Is this secure?
                    let output_le = keccak256_circuit::<F, D>(input_le, &mut self.builder);

                    let actual_output = output_le
                        .chunks(32)
                        .map(|v| self.builder.le_sum(v.chunks(8).rev().flatten()))
                        .collect::<Vec<_>>();

                    for (x, y) in actual_output.iter().zip(output.iter()) {
                        self.builder.connect(*x, *y);
                    }
                }
            } else {
                // TODO: If the input is too large, should it be divided into several starky circuits.
                let mut inputs = vec![];
                let mut outputs = vec![];
                for (input, output) in self.keccak_io.into_iter() {
                    let input = input
                        .iter()
                        .map(|v| {
                            let w = self.builder.split_le(*v, 32);
                            self.builder.le_sum(w.chunks(8).rev().flatten())
                        })
                        .collect::<Vec<_>>();

                    inputs.push(input);
                    outputs.push(output);
                }
                let generator =
                    Keccak256StarkyProofGenerator::<F, C, D>::new(&mut self.builder, inputs);

                for (xs, ys) in outputs.iter().zip(generator.outputs.iter()) {
                    for (x, y) in xs.iter().zip(ys.iter()) {
                        let y_bits = self.builder.split_le(*y, 32);
                        let y = self.builder.le_sum(y_bits.chunks(8).rev().flatten());
                        self.builder.connect(*x, y);
                    }
                }

                #[cfg(not(feature = "new-plonky2"))]
                self.builder
                    .add_generators(vec![Box::new(generator.adapter())]);

                #[cfg(feature = "new-plonky2")]
                self.builder.add_generators(vec![
                    plonky2::iop::generator::WitnessGeneratorRef::new(generator.adapter()),
                ]);
            }
        }

        dbg!(self.builder.num_gates());
        self.builder.build::<C>()
    }

    #[cfg(feature = "not-constrain-keccak")]
    pub fn build<C>(mut self) -> CircuitData<F, C, D>
    where
        C: GenericConfig<D, F = F>,
    {
        for (input, output) in self.keccak_io.iter() {
            let input_le = input
                .iter()
                .flat_map(|v| {
                    let w = self.builder.split_le(*v, 32);
                    w.chunks(8).rev().flatten().cloned().collect::<Vec<_>>()
                })
                .collect();
            let output_le = [(); 256].map(|_| self.builder.add_virtual_bool_target_safe());
            let generator = Keccak256MockGenerator {
                input: input_le,
                output: output_le,
            };

            #[cfg(not(feature = "new-plonky2"))]
            self.builder
                .add_generators(vec![Box::new(generator.adapter())]);

            #[cfg(feature = "new-plonky2")]
            self.builder
                .add_generators(vec![plonky2::iop::generator::WitnessGeneratorRef::new(
                    generator.adapter(),
                )]);

            let actual_output = output_le
                .chunks(32)
                .map(|v| self.builder.le_sum(v.chunks(8).rev().flatten()))
                .collect::<Vec<_>>();

            for (x, y) in actual_output.iter().zip(output.iter()) {
                self.builder.connect(*x, *y);
            }
        }

        dbg!(self.builder.num_gates());
        self.builder.build::<C>()
    }
}

pub struct Keccak256StarkyProofGenerator<
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
    const D: usize,
> {
    pub inputs: Vec<Vec<Target>>,
    pub outputs: Vec<[Target; 8]>,
    pub starky_pi: Vec<Target>,
    pub starky_proof: StarkProofWithPublicInputsTarget<D>,
    _config: std::marker::PhantomData<C>,
}

// TODO: Implement Debug trait for StarkProofWithPublicInputsTarget itself, then remove this.
impl<F, C, const D: usize> std::fmt::Debug for Keccak256StarkyProofGenerator<F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Keccak256StarkyProofGenerator")
            .field("inputs", &self.inputs)
            .field("outputs", &self.outputs)
            .field("starky_pi", &self.starky_pi)
            .field(
                "starky_proof",
                &WrappedStarkProofWithPublicInputsTarget(&self.starky_proof),
            )
            .finish()
    }
}

impl<F: RichField + Extendable<D>, C: GenericConfig<D, F = F>, const D: usize>
    Keccak256StarkyProofGenerator<F, C, D>
{
    pub fn new(builder: &mut CircuitBuilder<F, D>, inputs: Vec<Vec<Target>>) -> Self
    where
        C::Hasher: AlgebraicHasher<F>,
    {
        let num_perms: usize = inputs
            .iter()
            .map(|input| input.len() / BLOCK_SIZE + 1)
            .sum();

        let (outputs, starky_pi) = multi_keccak256_circuit_with_statements(builder, inputs.clone());

        let degree_bits = (NUM_ROUNDS * num_perms)
            .next_power_of_two()
            .trailing_zeros() as usize;
        let stark = KeccakStark::<F, D>::new(num_perms);
        let stark_config = stark.config();
        let inner_config = StarkConfig::standard_fast_config(
            stark_config.num_columns,
            stark_config.num_public_inputs,
        );
        let starky_proof =
            add_virtual_stark_proof_with_pis(builder, stark, &inner_config, degree_bits);
        verify_stark_proof_circuit::<F, C, _, D>(builder, stark, &starky_proof, &inner_config);
        for (x, y) in starky_pi.iter().zip(starky_proof.public_inputs.iter()) {
            builder.connect(*x, *y);
        }

        Self {
            inputs,
            outputs,
            starky_pi,
            starky_proof,
            _config: std::marker::PhantomData,
        }
    }
}

impl<F, C, const D: usize> SimpleGenerator<F> for Keccak256StarkyProofGenerator<F, C, D>
where
    F: RichField + Extendable<D>,
    C: GenericConfig<D, F = F> + 'static,
    C::Hasher: AlgebraicHasher<F>,
{
    #[cfg(feature = "new-plonky2")]
    fn id(&self) -> String {
        format!("Keccak256StarkyProofGenerator")
    }

    fn dependencies(&self) -> Vec<Target> {
        self.inputs
            .clone()
            .into_iter()
            .flatten()
            .collect::<Vec<_>>()
    }

    // NOTICE: not generate constraints for the hash
    fn run_once(&self, pw: &PartitionWitness<F>, out_buffer: &mut GeneratedValues<F>) {
        let num_perms: usize = self
            .inputs
            .iter()
            .map(|input| input.len() / BLOCK_SIZE + 1)
            .sum();

        let inputs = self
            .inputs
            .iter()
            .map(|input| {
                input
                    .iter()
                    .map(|v| pw.get_target(*v).to_canonical_u64() as u32)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        let (outputs, starky_pi) = multi_keccak256(inputs);

        assert_eq!(self.outputs.len(), outputs.len());
        for (targets, witnesses) in self.outputs.iter().zip(outputs.iter()) {
            assert_eq!(targets.len(), witnesses.len());
            for (target, witness) in targets.iter().zip(witnesses.iter()) {
                out_buffer.set_target(*target, F::from_canonical_u32(*witness));
            }
        }

        let mut perm_inputs = vec![];
        for i in 0..num_perms {
            let input = starky_pi[i * 100..i * 100 + 50].to_vec();
            let input = input
                .chunks(2)
                .map(|chunk| chunk[0] as u64 + ((chunk[1] as u64) << 32))
                .collect::<Vec<_>>();
            perm_inputs.push(input.try_into().unwrap());
        }

        let stark = KeccakStark::<F, D>::new(num_perms);
        let stark_config = stark.config();
        let inner_config = StarkConfig::standard_fast_config(
            stark_config.num_columns,
            stark_config.num_public_inputs,
        );
        let trace = stark.generate_trace(perm_inputs, 8);
        let starky_pi = starky_pi
            .iter()
            .map(|x| F::from_canonical_u32(*x))
            .collect::<Vec<_>>();
        let inner_proof = starky::prover::prove::<F, C, _, D>(
            stark,
            &inner_config,
            trace,
            starky_pi,
            &mut TimingTree::default(),
        )
        .unwrap();
        verify_stark_proof(stark, inner_proof.clone(), &inner_config).unwrap();

        set_stark_proof_with_pis_target(out_buffer, &self.starky_proof, &inner_proof);
    }

    #[cfg(feature = "new-plonky2")]
    fn serialize(&self, _dst: &mut Vec<u8>) -> plonky2::util::serialization::IoResult<()> {
        unimplemented!()
    }

    #[cfg(feature = "new-plonky2")]
    fn deserialize(
        _src: &mut plonky2::util::serialization::Buffer,
    ) -> plonky2::util::serialization::IoResult<Self>
    where
        Self: Sized,
    {
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use plonky2::{
        field::types::Field,
        iop::witness::{PartialWitness, WitnessWrite},
        plonk::{
            circuit_builder::CircuitBuilder,
            circuit_data::{CircuitConfig, VerifierCircuitTarget},
            config::{GenericConfig, PoseidonGoldilocksConfig},
        },
    };
    use rand::Rng;

    use crate::keccak256_circuit::solidity_keccak256;

    use super::CircuitBuilderWithKeccak;

    #[test]
    fn test_keccak_starky() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilderWithKeccak::<F, D>::new(config);
        let input1_target = builder.add_virtual_targets(33);
        let output1_target = builder.keccak256(input1_target.clone());
        builder.register_public_inputs(&output1_target);
        dbg!(builder.num_gates());
        let circuit_data = builder.build::<C>();
        dbg!(circuit_data.common.degree_bits());

        let mut rng = rand::thread_rng();
        let input1: Vec<u32> = vec![rng.gen(); 33];
        let output1 = solidity_keccak256(input1.clone()).0;

        let mut pw = PartialWitness::new();
        assert_eq!(input1.len(), input1_target.len());
        for (t, w) in input1_target.iter().zip(input1) {
            pw.set_target(*t, F::from_canonical_u32(w));
        }

        println!("start proving: keccak256 with starky");
        let start = Instant::now();
        let proof_with_pis = circuit_data.prove(pw).unwrap();
        let end = start.elapsed();
        println!("prove: {}.{:03} sec", end.as_secs(), end.subsec_millis());

        assert_eq!(
            proof_with_pis.public_inputs,
            [output1.map(F::from_canonical_u32).to_vec()].concat()
        );

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let proof_with_pis_target = builder.add_virtual_proof_with_pis(&circuit_data.common);
        let verifier_data = VerifierCircuitTarget {
            constants_sigmas_cap: builder
                .constant_merkle_cap(&circuit_data.verifier_only.constants_sigmas_cap),
            circuit_digest: builder.constant_hash(circuit_data.verifier_only.circuit_digest),
        };
        builder.verify_proof::<C>(&proof_with_pis_target, &verifier_data, &circuit_data.common);
        dbg!(builder.num_gates());
        let outer_circuit_data = builder.build::<C>();
        dbg!(outer_circuit_data.common.degree_bits());

        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&proof_with_pis_target, &proof_with_pis);

        println!("start proving: first recursion");
        let start = Instant::now();
        let proof_with_pis = outer_circuit_data.prove(pw).unwrap();
        let end = start.elapsed();
        println!("prove: {}.{:03} sec", end.as_secs(), end.subsec_millis());

        let circuit_data = outer_circuit_data;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let proof_with_pis_target = builder.add_virtual_proof_with_pis(&circuit_data.common);
        let verifier_data = VerifierCircuitTarget {
            constants_sigmas_cap: builder
                .constant_merkle_cap(&circuit_data.verifier_only.constants_sigmas_cap),
            circuit_digest: builder.constant_hash(circuit_data.verifier_only.circuit_digest),
        };
        builder.verify_proof::<C>(&proof_with_pis_target, &verifier_data, &circuit_data.common);
        dbg!(builder.num_gates());
        let outer_circuit_data = builder.build::<C>();
        dbg!(outer_circuit_data.common.degree_bits());

        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&proof_with_pis_target, &proof_with_pis);

        println!("start proving: second recursion");
        let start = Instant::now();
        let _proof_with_pis = outer_circuit_data.prove(pw).unwrap();
        let end = start.elapsed();
        println!("prove: {}.{:03} sec", end.as_secs(), end.subsec_millis());
    }

    #[test]
    fn test_keccak_starky_two() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilderWithKeccak::<F, D>::new(config);
        let input1_target = builder.add_virtual_targets(33);
        let input2_target = builder.add_virtual_targets(2048);
        let output1_target = builder.keccak256(input1_target.clone());
        let output2_target = builder.keccak256(input2_target.clone());
        builder.register_public_inputs(&output1_target);
        builder.register_public_inputs(&output2_target);
        dbg!(builder.num_gates());
        let circuit_data = builder.build::<C>();
        dbg!(circuit_data.common.degree_bits());

        let mut rng = rand::thread_rng();
        let input1: Vec<u32> = vec![rng.gen(); 33];
        let output1 = solidity_keccak256(input1.clone()).0;

        let mut rng = rand::thread_rng();
        let input2: Vec<u32> = vec![rng.gen(); 2048];
        let output2 = solidity_keccak256(input2.clone()).0;

        let mut pw = PartialWitness::new();
        assert_eq!(input1.len(), input1_target.len());
        for (t, w) in input1_target.iter().zip(input1) {
            pw.set_target(*t, F::from_canonical_u32(w));
        }

        assert_eq!(input2.len(), input2_target.len());
        for (t, w) in input2_target.iter().zip(input2) {
            pw.set_target(*t, F::from_canonical_u32(w));
        }

        println!("start proving: keccak256 with starky");
        let start = Instant::now();
        let proof_with_pis = circuit_data.prove(pw).unwrap();
        let end = start.elapsed();
        println!("prove: {}.{:03} sec", end.as_secs(), end.subsec_millis());

        assert_eq!(
            proof_with_pis.public_inputs,
            [
                output1.map(F::from_canonical_u32).to_vec(),
                output2.map(F::from_canonical_u32).to_vec()
            ]
            .concat()
        );

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let proof_with_pis_target = builder.add_virtual_proof_with_pis(&circuit_data.common);
        let verifier_data = VerifierCircuitTarget {
            constants_sigmas_cap: builder
                .constant_merkle_cap(&circuit_data.verifier_only.constants_sigmas_cap),
            circuit_digest: builder.constant_hash(circuit_data.verifier_only.circuit_digest),
        };
        builder.verify_proof::<C>(&proof_with_pis_target, &verifier_data, &circuit_data.common);
        dbg!(builder.num_gates());
        let outer_circuit_data = builder.build::<C>();
        dbg!(outer_circuit_data.common.degree_bits());

        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&proof_with_pis_target, &proof_with_pis);

        println!("start proving: first recursion");
        let start = Instant::now();
        let proof_with_pis = outer_circuit_data.prove(pw).unwrap();
        let end = start.elapsed();
        println!("prove: {}.{:03} sec", end.as_secs(), end.subsec_millis());

        let circuit_data = outer_circuit_data;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let proof_with_pis_target = builder.add_virtual_proof_with_pis(&circuit_data.common);
        let verifier_data = VerifierCircuitTarget {
            constants_sigmas_cap: builder
                .constant_merkle_cap(&circuit_data.verifier_only.constants_sigmas_cap),
            circuit_digest: builder.constant_hash(circuit_data.verifier_only.circuit_digest),
        };
        builder.verify_proof::<C>(&proof_with_pis_target, &verifier_data, &circuit_data.common);
        dbg!(builder.num_gates());
        let outer_circuit_data = builder.build::<C>();
        dbg!(outer_circuit_data.common.degree_bits());

        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&proof_with_pis_target, &proof_with_pis);

        println!("start proving: second recursion");
        let start = Instant::now();
        let _proof_with_pis = outer_circuit_data.prove(pw).unwrap();
        let end = start.elapsed();
        println!("prove: {}.{:03} sec", end.as_secs(), end.subsec_millis());
    }

    #[test]
    fn test_keccak_starky_many() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;

        // Compute the keccak hash `INPUTS_LEN` times.
        const INPUTS_LEN: usize = 3;
        // The length of each input in the keccak hash is `INPUT_LEN`.
        const INPUT_LEN: usize = 24;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilderWithKeccak::<F, D>::new(config);
        let mut inputs_target = vec![];
        for _ in 0..INPUTS_LEN {
            let input_target = builder.add_virtual_targets(INPUT_LEN);
            let output_target = builder.keccak256(input_target.clone());
            builder.register_public_inputs(&output_target);
            inputs_target.push(input_target);
        }
        dbg!(builder.num_gates());
        let circuit_data = builder.build::<C>();
        dbg!(circuit_data.common.degree_bits());

        let mut inputs = vec![];
        let mut outputs = vec![];
        for _ in 0..INPUTS_LEN {
            let mut rng = rand::thread_rng();
            let input: Vec<u32> = vec![rng.gen(); INPUT_LEN];
            let output = solidity_keccak256(input.clone()).0;
            inputs.push(input);
            outputs.push(output);
        }

        let mut pw = PartialWitness::new();
        for (input_target, input) in inputs_target.iter().zip(inputs) {
            assert_eq!(input.len(), input_target.len());
            for (t, w) in input_target.iter().zip(input) {
                pw.set_target(*t, F::from_canonical_u32(w));
            }
        }

        println!("start proving: keccak256 with starky");
        let start = Instant::now();
        let proof_with_pis = circuit_data.prove(pw).unwrap();
        let end = start.elapsed();
        println!("prove: {}.{:03} sec", end.as_secs(), end.subsec_millis());

        assert_eq!(
            proof_with_pis.public_inputs,
            outputs
                .iter()
                .flat_map(|output| output.map(F::from_canonical_u32).to_vec())
                .collect::<Vec<_>>(),
        );

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let proof_with_pis_target = builder.add_virtual_proof_with_pis(&circuit_data.common);
        let verifier_data = VerifierCircuitTarget {
            constants_sigmas_cap: builder
                .constant_merkle_cap(&circuit_data.verifier_only.constants_sigmas_cap),
            circuit_digest: builder.constant_hash(circuit_data.verifier_only.circuit_digest),
        };
        builder.verify_proof::<C>(&proof_with_pis_target, &verifier_data, &circuit_data.common);
        dbg!(builder.num_gates());
        let outer_circuit_data = builder.build::<C>();
        dbg!(outer_circuit_data.common.degree_bits());

        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&proof_with_pis_target, &proof_with_pis);

        println!("start proving: first recursion");
        let start = Instant::now();
        let proof_with_pis = outer_circuit_data.prove(pw).unwrap();
        let end = start.elapsed();
        println!("prove: {}.{:03} sec", end.as_secs(), end.subsec_millis());

        let circuit_data = outer_circuit_data;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let proof_with_pis_target = builder.add_virtual_proof_with_pis(&circuit_data.common);
        let verifier_data = VerifierCircuitTarget {
            constants_sigmas_cap: builder
                .constant_merkle_cap(&circuit_data.verifier_only.constants_sigmas_cap),
            circuit_digest: builder.constant_hash(circuit_data.verifier_only.circuit_digest),
        };
        builder.verify_proof::<C>(&proof_with_pis_target, &verifier_data, &circuit_data.common);
        dbg!(builder.num_gates());
        let outer_circuit_data = builder.build::<C>();
        dbg!(outer_circuit_data.common.degree_bits());

        let mut pw = PartialWitness::new();
        pw.set_proof_with_pis_target(&proof_with_pis_target, &proof_with_pis);

        println!("start proving: second recursion");
        let start = Instant::now();
        let _proof_with_pis = outer_circuit_data.prove(pw).unwrap();
        let end = start.elapsed();
        println!("prove: {}.{:03} sec", end.as_secs(), end.subsec_millis());
    }
}
