use crate::constraint_consumer::ConstraintConsumer;
use itertools::Itertools;
use plonky2::{
    field::{packed::PackedField, types::Field},
    hash::hash_types::RichField,
};

pub fn get_pulse_col(start_pulse_col: usize, i: usize) -> usize {
    start_pulse_col + 1 + 2 * i + 1
}

pub fn get_witness_col(start_pulse_col: usize, i: usize) -> usize {
    start_pulse_col + 1 + 2 * i
}

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

pub fn eval_pulse<P: PackedField, const N: usize>(
    yield_constr: &mut ConstraintConsumer<P>,
    lv: &[P; N],
    nv: &[P; N],
    start_pulse_col: usize,
    pulse_positions: Vec<usize>,
) {
    let counter = lv[start_pulse_col];
    yield_constr.constraint_first_row(counter);
    let next_counter = nv[start_pulse_col];
    yield_constr.constraint_transition(next_counter - counter - P::ONES);
    for (i, &pos) in pulse_positions.iter().enumerate() {
        let counter_minus_pos = counter - P::Scalar::from_canonical_usize(pos);
        let witness = lv[get_witness_col(start_pulse_col, i)];
        let pulse = nv[get_pulse_col(start_pulse_col, i)];
        yield_constr.constraint(counter_minus_pos * witness + pulse - P::ONES); // pulse = 1 - (counter - pos) * witness
        yield_constr.constraint(counter_minus_pos * pulse);
    }
}
