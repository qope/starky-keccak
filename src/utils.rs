use plonky2::{
    field::{extension::Extendable, packed::PackedField},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};

use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

use super::{
    columns::{reg_a, reg_a_prime_prime_prime},
    keccak_stark::NUM_ROUNDS,
};

pub fn split_lo_and_hi(input: [u64; 25]) -> [u32; 50] {
    let mut output = [0u32; 50];
    for i in 0..25 {
        let output_lo = (input[i] & 0xFFFFFFFF) as u32;
        let output_hi = (input[i] >> 32) as u32;
        output[2 * i] = output_lo;
        output[2 * i + 1] = output_hi;
    }
    output
}

pub fn read_state<F: Clone + core::fmt::Debug>(lv: &[F], cur_col: &mut usize) -> [F; 50] {
    let state = lv[*cur_col..*cur_col + 50].to_vec();
    *cur_col += 50;
    state.try_into().unwrap()
}

pub fn write_state<T: Copy>(lv: &mut [T], state: &[T; 50], cur_col: &mut usize) {
    lv[*cur_col..*cur_col + 50].copy_from_slice(state);
    *cur_col += 50;
}

// read reg_a of lv
pub fn read_input<T: Default + Copy>(lv: &[T]) -> [T; 50] {
    let mut input = [T::default(); 50];
    for x in 0..5 {
        for y in 0..5 {
            input[2 * (5 * y + x)] = lv[reg_a(x, y)]; // lo part
            input[2 * (5 * y + x) + 1] = lv[reg_a(x, y) + 1]; // hi part
        }
    }
    input
}

pub fn read_output<T: Default + Copy>(lv: &[T]) -> [T; 50] {
    let mut output = [T::default(); 50];
    for x in 0..5 {
        for y in 0..5 {
            output[2 * (5 * y + x)] = lv[reg_a_prime_prime_prime(x, y)]; // lo part
            output[2 * (5 * y + x) + 1] = lv[reg_a_prime_prime_prime(x, y) + 1];
            // hi part
        }
    }
    output
}

pub fn read_input_target<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    lv: &[ExtensionTarget<D>],
) -> [ExtensionTarget<D>; 50] {
    let zero = builder.zero_extension();
    let mut input = [zero; 50];
    for x in 0..5 {
        for y in 0..5 {
            input[2 * (5 * y + x)] = lv[reg_a(x, y)]; // lo part
            input[2 * (5 * y + x) + 1] = lv[reg_a(x, y) + 1]; // hi part
        }
    }
    input
}

pub fn read_output_target<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    lv: &[ExtensionTarget<D>],
) -> [ExtensionTarget<D>; 50] {
    let zero = builder.zero_extension();
    let mut output = [zero; 50];
    for x in 0..5 {
        for y in 0..5 {
            output[2 * (5 * y + x)] = lv[reg_a_prime_prime_prime(x, y)]; // lo part
            output[2 * (5 * y + x) + 1] = lv[reg_a_prime_prime_prime(x, y) + 1];
            // hi part
        }
    }
    output
}

pub fn state_eq<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    filter: P,
    state_a: [P; 50],
    state_b: [P; 50],
) {
    for i in 0..50 {
        let diff = state_a[i] - state_b[i];
        let t = diff * filter;
        yield_constr.constraint(t);
    }
}

pub fn state_eq_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    filter: ExtensionTarget<D>,
    state_a: [ExtensionTarget<D>; 50],
    state_b: [ExtensionTarget<D>; 50],
) {
    for i in 0..50 {
        let diff = builder.sub_extension(state_a[i], state_b[i]);
        let t = builder.mul_extension(diff, filter);
        yield_constr.constraint(builder, t);
    }
}

pub fn gen_keccak_pulse_positions(num_io_pairs: usize) -> Vec<usize> {
    (0..num_io_pairs)
        .flat_map(|i| vec![NUM_ROUNDS * i, NUM_ROUNDS * (i + 1) - 1])
        .collect()
}
