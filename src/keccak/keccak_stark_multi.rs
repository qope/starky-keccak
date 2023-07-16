use std::marker::PhantomData;

use itertools::Itertools;
use plonky2::field::extension::{Extendable, FieldExtension};
use plonky2::field::packed::PackedField;
use plonky2::field::polynomial::PolynomialValues;
use plonky2::hash::hash_types::RichField;
use plonky2::timed;
use plonky2::util::timing::TimingTree;

use crate::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};
use crate::keccak::columns::{reg_a, reg_step, NUM_COLUMNS, REG_FILTER};

use crate::keccak::round_flags::{eval_round_flags, eval_round_flags_recursively};
use crate::keccak::utils::{split_lo_and_hi, write_state};
use crate::stark::Stark;
use crate::util::trace_rows_to_poly_values;
use crate::vars::{StarkEvaluationTargets, StarkEvaluationVars};

use super::columns::reg_a_prime_prime_prime;
use super::keccak::{
    eval_keccak_round, eval_keccak_round_circuit, generate_keccak_trace_row_for_round,
};
use super::pulse::{eval_pulse, eval_pulse_circuit, get_pulse_col};
use super::utils::{
    gen_keccak_pulse_positions, read_input, read_input_target, read_output, read_output_target,
    read_state, state_eq, state_eq_circuit,
};

/// Number of rounds in a Keccak permutation.
pub(crate) const NUM_ROUNDS: usize = 24;

/// Number of 64-bit elements in the Keccak permutation input.
pub(crate) const NUM_INPUTS: usize = 25;

const NUM_IO_PAIRS: usize = 61;

#[derive(Copy, Clone, Default)]
pub struct KeccakStark<F, const D: usize> {
    pub(crate) f: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> KeccakStark<F, D> {
    /// Generate the rows of the trace. Note that this does not generate the permuted columns used
    /// in our lookup arguments, as those are computed after transposing to column-wise form.
    fn generate_trace_rows(
        &self,
        inputs: [[u64; NUM_INPUTS]; NUM_IO_PAIRS],
        min_rows: usize,
    ) -> Vec<[F; NUM_COLUMNS]> {
        let num_rows = (NUM_IO_PAIRS * NUM_ROUNDS)
            .max(min_rows)
            .next_power_of_two();
        let mut rows = Vec::with_capacity(num_rows);
        for input in inputs.iter() {
            let mut rows_for_perm = self.generate_trace_rows_for_perm(*input);
            // Since this is a real operation, not padding, we set the filter to 1 on the last row.
            rows_for_perm[NUM_ROUNDS - 1][REG_FILTER] = F::ONE;
            rows.extend(rows_for_perm);
        }

        let pad_rows = self.generate_trace_rows_for_perm([0; NUM_INPUTS]);
        while rows.len() < num_rows {
            rows.extend(&pad_rows);
        }
        rows.drain(num_rows..);
        rows
    }

    fn generate_trace_rows_for_perm(&self, input: [u64; NUM_INPUTS]) -> Vec<[F; NUM_COLUMNS]> {
        let mut rows = vec![[F::ZERO; NUM_COLUMNS]; NUM_ROUNDS];

        // Populate the round input for the first round.
        for x in 0..5 {
            for y in 0..5 {
                let input_xy = input[y * 5 + x];
                let reg_lo = reg_a(x, y);
                let reg_hi = reg_lo + 1;
                rows[0][reg_lo] = F::from_canonical_u64(input_xy & 0xFFFFFFFF);
                rows[0][reg_hi] = F::from_canonical_u64(input_xy >> 32);
            }
        }

        generate_keccak_trace_row_for_round(&mut rows[0], 0);
        for round in 1..24 {
            self.copy_output_to_input(rows[round - 1], &mut rows[round]);
            generate_keccak_trace_row_for_round(&mut rows[round], round);
        }

        rows
    }

    fn copy_output_to_input(&self, prev_row: [F; NUM_COLUMNS], next_row: &mut [F; NUM_COLUMNS]) {
        for x in 0..5 {
            for y in 0..5 {
                let in_lo = reg_a(x, y);
                let in_hi = in_lo + 1;
                let out_lo = reg_a_prime_prime_prime(x, y);
                let out_hi = out_lo + 1;
                next_row[in_lo] = prev_row[out_lo];
                next_row[in_hi] = prev_row[out_hi];
            }
        }
    }

    pub fn generate_trace(
        &self,
        inputs: [[u64; NUM_INPUTS]; NUM_IO_PAIRS],
        min_rows: usize,
        timing: &mut TimingTree,
    ) -> Vec<PolynomialValues<F>> {
        // Generate the witness, except for permuted columns in the lookup argument.
        let trace_rows = timed!(
            timing,
            "generate trace rows",
            self.generate_trace_rows(inputs, min_rows)
        );
        let trace_polys = timed!(
            timing,
            "convert to PolynomialValues",
            trace_rows_to_poly_values(trace_rows)
        );
        trace_polys
    }

    pub fn generate_public_inputs(
        &self,
        inputs: [[u64; NUM_INPUTS]; NUM_IO_PAIRS],
        outputs: [[u64; NUM_INPUTS]; NUM_IO_PAIRS],
    ) -> [F; 2 * 50 * NUM_IO_PAIRS] {
        let mut pi = [F::ZERO; 2 * 50 * NUM_IO_PAIRS];
        let mut cur_col = 0;
        inputs
            .iter()
            .zip(outputs.iter())
            .map(|(&input, &output)| {
                let input = split_lo_and_hi(input).map(F::from_canonical_u32);
                let output = split_lo_and_hi(output).map(F::from_canonical_u32);
                write_state(&mut pi, &input, &mut cur_col);
                write_state(&mut pi, &output, &mut cur_col);
            })
            .collect_vec();
        assert!(cur_col == 2 * 50 * NUM_IO_PAIRS);
        pi
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for KeccakStark<F, D> {
    const COLUMNS: usize = NUM_COLUMNS + 1 + 4 * NUM_IO_PAIRS;
    const PUBLIC_INPUTS: usize = 4 * NUM_INPUTS * NUM_IO_PAIRS;

    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: StarkEvaluationVars<FE, P, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
        eval_round_flags(vars, yield_constr);

        // The filter must be 0 or 1.
        let filter = vars.local_values[REG_FILTER];
        yield_constr.constraint(filter * (filter - P::ONES));

        // If this is not the final step, the filter must be off.
        let final_step = vars.local_values[reg_step(NUM_ROUNDS - 1)];
        let not_final_step = P::ONES - final_step;
        yield_constr.constraint(not_final_step * filter);

        // eval pulse
        eval_pulse(
            yield_constr,
            vars.local_values,
            vars.next_values,
            NUM_COLUMNS,
            gen_keccak_pulse_positions(NUM_IO_PAIRS),
        );

        let start_pulse_col = NUM_COLUMNS;

        let mut input_flags = vec![];
        let mut output_flags = vec![];
        for i in 0..NUM_IO_PAIRS {
            input_flags.push(vars.local_values[get_pulse_col(start_pulse_col, 2 * i)]);
            output_flags.push(vars.local_values[get_pulse_col(start_pulse_col, 2 * i + 1)]);
        }

        // public inputs and outputs
        let pi: [P; Self::PUBLIC_INPUTS] = vars.public_inputs.map(|x| x.into());
        let input = read_input(vars.local_values);
        let output = read_output(vars.local_values);
        let mut cur_col = 0;
        (0..NUM_IO_PAIRS).for_each(|i| {
            let input_pi = read_state(&pi, &mut cur_col);
            let output_pi = read_state(&pi, &mut cur_col);
            state_eq(yield_constr, input_flags[i], input, input_pi);
            state_eq(yield_constr, output_flags[i], output, output_pi);
        });

        eval_keccak_round::<FE, P, D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>(
            yield_constr,
            vars,
        );
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut plonky2::plonk::circuit_builder::CircuitBuilder<F, D>,
        vars: StarkEvaluationTargets<D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        let one_ext = builder.one_extension();
        eval_round_flags_recursively(builder, vars, yield_constr);
        // The filter must be 0 or 1.
        let filter = vars.local_values[REG_FILTER];
        let constraint = builder.mul_sub_extension(filter, filter, filter);
        yield_constr.constraint(builder, constraint);

        // If this is not the final step, the filter must be off.
        let final_step = vars.local_values[reg_step(NUM_ROUNDS - 1)];
        let not_final_step = builder.sub_extension(one_ext, final_step);
        let constraint = builder.mul_extension(not_final_step, filter);
        yield_constr.constraint(builder, constraint);

        // eval pulse
        let pulse_positions = gen_keccak_pulse_positions(NUM_IO_PAIRS);
        eval_pulse_circuit(
            builder,
            yield_constr,
            vars.local_values,
            vars.next_values,
            NUM_COLUMNS,
            pulse_positions.clone(),
        );

        let start_pulse_col = NUM_COLUMNS;

        let mut input_flags = vec![];
        let mut output_flags = vec![];
        for i in 0..NUM_IO_PAIRS {
            input_flags.push(vars.local_values[get_pulse_col(start_pulse_col, 2 * i)]);
            output_flags.push(vars.local_values[get_pulse_col(start_pulse_col, 2 * i + 1)]);
        }

        // public inputs and outputs
        let pi = vars.public_inputs;
        let input = read_input_target(builder, vars.local_values);
        let output = read_output_target(builder, vars.local_values);
        let mut cur_col = 0;
        for i in 0..NUM_IO_PAIRS {
            let input_pi = read_state(pi, &mut cur_col);
            let output_pi = read_state(pi, &mut cur_col);
            state_eq_circuit(builder, yield_constr, input_flags[i], input, input_pi);
            state_eq_circuit(builder, yield_constr, output_flags[i], output, output_pi);
        }

        eval_keccak_round_circuit::<F, D, { Self::COLUMNS }, { Self::PUBLIC_INPUTS }>(
            builder,
            yield_constr,
            vars,
        );
    }

    fn constraint_degree(&self) -> usize {
        3
    }
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use anyhow::Result;
    use itertools::Itertools;
    use plonky2::field::polynomial::PolynomialValues;
    use plonky2::iop::witness::PartialWitness;
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};
    use plonky2::util::timing::TimingTree;
    use plonky2::util::transpose;
    use tiny_keccak::keccakf;

    use crate::config::StarkConfig;
    use crate::keccak::keccak_stark_multi::{KeccakStark, NUM_INPUTS, NUM_IO_PAIRS};
    use crate::keccak::pulse::generate_pulse;
    use crate::keccak::utils::gen_keccak_pulse_positions;
    use crate::prover::prove;
    use crate::recursive_verifier::{
        add_virtual_stark_proof_with_pis, set_stark_proof_with_pis_target,
        verify_stark_proof_circuit,
    };
    use crate::stark_testing::{test_stark_circuit_constraints, test_stark_low_degree};
    use crate::verifier::verify_stark_proof;

    #[test]
    fn test_stark_degree() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = KeccakStark<F, D>;

        let stark = S {
            f: Default::default(),
        };
        test_stark_low_degree(stark)
    }

    #[test]
    fn test_stark_circuit() -> Result<()> {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = KeccakStark<F, D>;

        let stark = S {
            f: Default::default(),
        };
        test_stark_circuit_constraints::<F, C, S, D>(stark)
    }

    #[test]
    fn test_keccak_multi() -> Result<()> {
        let inputs: [[u64; NUM_INPUTS]; NUM_IO_PAIRS] = (0..NUM_IO_PAIRS)
            .map(|_| {
                let r: [u64; NUM_INPUTS] = rand::random();
                r
            })
            .collect_vec()
            .try_into()
            .unwrap();

        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        type S = KeccakStark<F, D>;

        let stark = S {
            f: Default::default(),
        };

        let rows = stark.generate_trace_rows(inputs, 1000);
        let mut trace_cols = transpose(&rows.iter().map(|v| v.to_vec()).collect_vec());

        generate_pulse(&mut trace_cols, gen_keccak_pulse_positions(NUM_IO_PAIRS));

        let trace = trace_cols
            .into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect();

        let outputs = inputs.map(|input| {
            let mut state = input;
            keccakf(&mut state);
            state
        });

        let now = Instant::now();
        let inner_config = StarkConfig::standard_fast_config();
        let public_inputs = stark.generate_public_inputs(inputs, outputs);
        let inner_proof = prove::<F, C, S, D>(
            stark,
            &inner_config,
            trace,
            public_inputs,
            &mut TimingTree::default(),
        )?;
        println!("Stark proving time: {:?}", now.elapsed());
        verify_stark_proof(stark, inner_proof.clone(), &inner_config)?;

        let circuit_config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(circuit_config);
        let mut pw = PartialWitness::new();
        let degree_bits = inner_proof.proof.recover_degree_bits(&inner_config);
        let pt = add_virtual_stark_proof_with_pis(&mut builder, stark, &inner_config, degree_bits);
        set_stark_proof_with_pis_target(&mut pw, &pt, &inner_proof);
        verify_stark_proof_circuit::<F, C, S, D>(&mut builder, stark, &pt, &inner_config);
        let data = builder.build::<C>();
        let now = Instant::now();
        let proof = data.prove(pw)?;
        println!("Circuit proving time: {:?}", now.elapsed());
        data.verify(proof)?;

        Ok(())
    }
}
