use itertools::Itertools;
use plonky2::{
    field::{extension::Extendable, packed::PackedField, types::Field},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

pub fn get_pulse_col(start_pulse_col: usize, i: usize) -> usize {
    start_pulse_col + 1 + 2 * i + 1
}

pub fn get_witness_col(start_pulse_col: usize, i: usize) -> usize {
    start_pulse_col + 1 + 2 * i
}

/// Adds a pulse column of the given positions to trace_cols.
/// 1 + 2*pulse_positions.len() columns are added to trace_cols.
pub fn generate_pulse<F: RichField>(trace_cols: &mut Vec<Vec<F>>, pulse_positions: Vec<usize>) {
    let rows = trace_cols[0].len();
    assert!(trace_cols.iter().all(|col| col.len() == rows));
    assert!(pulse_positions.iter().all(|&pos| pos < rows));
    let counter = (0..rows).map(|x| F::from_canonical_usize(x)).collect_vec();
    trace_cols.push(counter.clone());
    for pos in pulse_positions {
        let witness = counter
            .iter()
            .map(|&x| {
                if x == F::from_canonical_usize(pos) {
                    F::ZERO
                } else {
                    let diff = x - F::from_canonical_usize(pos);
                    diff.inverse()
                }
            })
            .collect_vec();
        let mut pulse = vec![F::ZERO; rows];
        pulse[pos] = F::ONE;
        trace_cols.push(witness);
        trace_cols.push(pulse);
    }
}

pub fn eval_pulse<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    lv: &[P],
    nv: &[P],
    start_pulse_col: usize,
    pulse_positions: Vec<usize>,
) {
    let counter = lv[start_pulse_col];
    yield_constr.constraint_first_row(counter);
    let next_counter: P = nv[start_pulse_col];
    yield_constr.constraint_transition(next_counter - counter - P::ONES);
    for (i, &pos) in pulse_positions.iter().enumerate() {
        let counter_minus_pos = counter - P::Scalar::from_canonical_usize(pos);
        let witness = lv[get_witness_col(start_pulse_col, i)];
        let pulse = lv[get_pulse_col(start_pulse_col, i)];
        yield_constr.constraint(counter_minus_pos * witness + pulse - P::ONES); // pulse = 1 - (counter - pos) * witness
        yield_constr.constraint(counter_minus_pos * pulse);
    }
}

pub fn eval_pulse_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    lv: &[ExtensionTarget<D>],
    nv: &[ExtensionTarget<D>],
    start_pulse_col: usize,
    pulse_positions: Vec<usize>,
) {
    let one = builder.one_extension();
    let counter = lv[start_pulse_col];
    yield_constr.constraint_first_row(builder, counter);
    let next_counter = nv[start_pulse_col];
    {
        let diff = builder.sub_extension(next_counter, counter);
        let diff = builder.sub_extension(diff, one);
        yield_constr.constraint_transition(builder, diff);
    }
    for (i, &pos) in pulse_positions.iter().enumerate() {
        let pos = builder.constant_extension(F::Extension::from_canonical_usize(pos));
        let counter_minus_pos = builder.sub_extension(counter, pos);
        let witness = lv[get_witness_col(start_pulse_col, i)];
        let pulse = lv[get_pulse_col(start_pulse_col, i)];
        {
            let pulse_minus_one = builder.sub_extension(pulse, one);
            let t = builder.mul_add_extension(counter_minus_pos, witness, pulse_minus_one);
            yield_constr.constraint(builder, t);
        }
        {
            let t = builder.mul_extension(counter_minus_pos, pulse);
            yield_constr.constraint(builder, t);
        }
    }
}
