use itertools::Itertools;
use plonky2::{
    field::{extension::Extendable, packed::PackedField, types::Field},
    hash::hash_types::RichField,
    plonk::{circuit_builder::CircuitBuilder, plonk_common::reduce_with_powers_ext_circuit},
};

use starky::{
    constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
    vars::{StarkEvaluationTargets, StarkEvaluationVars},
};

use super::{
    columns::{
        reg_a, reg_a_prime, reg_a_prime_prime, reg_a_prime_prime_0_0_bit, reg_a_prime_prime_prime,
        reg_b, reg_c, reg_c_prime, reg_step, NUM_COLUMNS,
    },
    constants::{rc_value, rc_value_bit},
    keccak_stark::NUM_ROUNDS,
    logic::{
        andn, andn_gen, andn_gen_circuit, xor, xor3_gen, xor3_gen_circuit, xor_gen, xor_gen_circuit,
    },
};

pub fn generate_keccak_trace_row_for_round<F: RichField>(row: &mut [F; NUM_COLUMNS], round: usize) {
    row[reg_step(round)] = F::ONE;

    // Populate C[x] = xor(A[x, 0], A[x, 1], A[x, 2], A[x, 3], A[x, 4]).
    for x in 0..5 {
        for z in 0..64 {
            let is_high_limb = z / 32;
            let bit_in_limb = z % 32;
            let a = [0, 1, 2, 3, 4].map(|i| {
                let reg_a_limb = reg_a(x, i) + is_high_limb;
                let a_limb = row[reg_a_limb].to_canonical_u64() as u32;
                F::from_bool(((a_limb >> bit_in_limb) & 1) != 0)
            });
            row[reg_c(x, z)] = xor(a);
        }
    }

    // Populate C'[x, z] = xor(C[x, z], C[x - 1, z], C[x + 1, z - 1]).
    for x in 0..5 {
        for z in 0..64 {
            row[reg_c_prime(x, z)] = xor([
                row[reg_c(x, z)],
                row[reg_c((x + 4) % 5, z)],
                row[reg_c((x + 1) % 5, (z + 63) % 64)],
            ]);
        }
    }

    // Populate A'. To avoid shifting indices, we rewrite
    //     A'[x, y, z] = xor(A[x, y, z], C[x - 1, z], C[x + 1, z - 1])
    // as
    //     A'[x, y, z] = xor(A[x, y, z], C[x, z], C'[x, z]).
    for x in 0..5 {
        for y in 0..5 {
            for z in 0..64 {
                let is_high_limb = z / 32;
                let bit_in_limb = z % 32;
                let reg_a_limb = reg_a(x, y) + is_high_limb;
                let a_limb = row[reg_a_limb].to_canonical_u64() as u32;
                let a_bit = F::from_bool(((a_limb >> bit_in_limb) & 1) != 0);
                row[reg_a_prime(x, y, z)] = xor([a_bit, row[reg_c(x, z)], row[reg_c_prime(x, z)]]);
            }
        }
    }

    // Populate A''.
    // A''[x, y] = xor(B[x, y], andn(B[x + 1, y], B[x + 2, y])).
    for x in 0..5 {
        for y in 0..5 {
            let get_bit = |z| {
                xor([
                    row[reg_b(x, y, z)],
                    andn(row[reg_b((x + 1) % 5, y, z)], row[reg_b((x + 2) % 5, y, z)]),
                ])
            };

            let lo = (0..32)
                .rev()
                .fold(F::ZERO, |acc, z| acc.double() + get_bit(z));
            let hi = (32..64)
                .rev()
                .fold(F::ZERO, |acc, z| acc.double() + get_bit(z));

            let reg_lo = reg_a_prime_prime(x, y);
            let reg_hi = reg_lo + 1;
            row[reg_lo] = lo;
            row[reg_hi] = hi;
        }
    }

    // For the XOR, we split A''[0, 0] to bits.
    let val_lo = row[reg_a_prime_prime(0, 0)].to_canonical_u64();
    let val_hi = row[reg_a_prime_prime(0, 0) + 1].to_canonical_u64();
    let val = val_lo | (val_hi << 32);
    let bit_values: Vec<u64> = (0..64)
        .scan(val, |acc, _| {
            let tmp = *acc & 1;
            *acc >>= 1;
            Some(tmp)
        })
        .collect();
    for i in 0..64 {
        row[reg_a_prime_prime_0_0_bit(i)] = F::from_canonical_u64(bit_values[i]);
    }

    // A''[0, 0] is additionally xor'd with RC.
    let in_reg_lo = reg_a_prime_prime(0, 0);
    let in_reg_hi = in_reg_lo + 1;
    let out_reg_lo = reg_a_prime_prime_prime(0, 0);
    let out_reg_hi = out_reg_lo + 1;
    let rc_lo = rc_value(round) & ((1 << 32) - 1);
    let rc_hi = rc_value(round) >> 32;
    row[out_reg_lo] = F::from_canonical_u64(row[in_reg_lo].to_canonical_u64() ^ rc_lo);
    row[out_reg_hi] = F::from_canonical_u64(row[in_reg_hi].to_canonical_u64() ^ rc_hi);
}

pub fn eval_keccak_round<F: Field, P: PackedField<Scalar = F>, const D: usize>(
    yield_constr: &mut ConstraintConsumer<P>,
    vars: StarkEvaluationVars<F, P>,
) {
    // C'[x, z] = xor(C[x, z], C[x - 1, z], C[x + 1, z - 1]).
    for x in 0..5 {
        for z in 0..64 {
            let xor = xor3_gen(
                vars.local_values[reg_c(x, z)],
                vars.local_values[reg_c((x + 4) % 5, z)],
                vars.local_values[reg_c((x + 1) % 5, (z + 63) % 64)],
            );
            let c_prime = vars.local_values[reg_c_prime(x, z)];
            yield_constr.constraint(c_prime - xor);
        }
    }
    // Check that the input limbs are consistent with A' and D.
    // A[x, y, z] = xor(A'[x, y, z], D[x, y, z])
    //            = xor(A'[x, y, z], C[x - 1, z], C[x + 1, z - 1])
    //            = xor(A'[x, y, z], C[x, z], C'[x, z]).
    // The last step is valid based on the identity we checked above.
    // It isn't required, but makes this check a bit cleaner.
    for x in 0..5 {
        for y in 0..5 {
            let a_lo = vars.local_values[reg_a(x, y)];
            let a_hi = vars.local_values[reg_a(x, y) + 1];
            let get_bit = |z| {
                let a_prime = vars.local_values[reg_a_prime(x, y, z)];
                let c = vars.local_values[reg_c(x, z)];
                let c_prime = vars.local_values[reg_c_prime(x, z)];
                xor3_gen(a_prime, c, c_prime)
            };
            let computed_lo = (0..32)
                .rev()
                .fold(P::ZEROS, |acc, z| acc.doubles() + get_bit(z));
            let computed_hi = (32..64)
                .rev()
                .fold(P::ZEROS, |acc, z| acc.doubles() + get_bit(z));
            yield_constr.constraint(computed_lo - a_lo);
            yield_constr.constraint(computed_hi - a_hi);
        }
    }

    // xor_{i=0}^4 A'[x, i, z] = C'[x, z], so for each x, z,
    // diff * (diff - 2) * (diff - 4) = 0, where
    // diff = sum_{i=0}^4 A'[x, i, z] - C'[x, z]
    for x in 0..5 {
        for z in 0..64 {
            let sum: P = [0, 1, 2, 3, 4]
                .map(|i| vars.local_values[reg_a_prime(x, i, z)])
                .into_iter()
                .sum();
            let diff = sum - vars.local_values[reg_c_prime(x, z)];
            yield_constr.constraint(diff * (diff - F::TWO) * (diff - F::from_canonical_u8(4)));
        }
    }

    // A''[x, y] = xor(B[x, y], andn(B[x + 1, y], B[x + 2, y])).
    for x in 0..5 {
        for y in 0..5 {
            let get_bit = |z| {
                xor_gen(
                    vars.local_values[reg_b(x, y, z)],
                    andn_gen(
                        vars.local_values[reg_b((x + 1) % 5, y, z)],
                        vars.local_values[reg_b((x + 2) % 5, y, z)],
                    ),
                )
            };
            let reg_lo = reg_a_prime_prime(x, y);
            let reg_hi = reg_lo + 1;
            let lo = vars.local_values[reg_lo];
            let hi = vars.local_values[reg_hi];
            let computed_lo = (0..32)
                .rev()
                .fold(P::ZEROS, |acc, z| acc.doubles() + get_bit(z));
            let computed_hi = (32..64)
                .rev()
                .fold(P::ZEROS, |acc, z| acc.doubles() + get_bit(z));
            yield_constr.constraint(computed_lo - lo);
            yield_constr.constraint(computed_hi - hi);
        }
    }

    // A'''[0, 0] = A''[0, 0] XOR RC
    let a_prime_prime_0_0_bits = (0..64)
        .map(|i| vars.local_values[reg_a_prime_prime_0_0_bit(i)])
        .collect_vec();
    let computed_a_prime_prime_0_0_lo = (0..32)
        .rev()
        .fold(P::ZEROS, |acc, z| acc.doubles() + a_prime_prime_0_0_bits[z]);
    let computed_a_prime_prime_0_0_hi = (32..64)
        .rev()
        .fold(P::ZEROS, |acc, z| acc.doubles() + a_prime_prime_0_0_bits[z]);
    let a_prime_prime_0_0_lo = vars.local_values[reg_a_prime_prime(0, 0)];
    let a_prime_prime_0_0_hi = vars.local_values[reg_a_prime_prime(0, 0) + 1];
    yield_constr.constraint(computed_a_prime_prime_0_0_lo - a_prime_prime_0_0_lo);
    yield_constr.constraint(computed_a_prime_prime_0_0_hi - a_prime_prime_0_0_hi);

    let get_xored_bit = |i| {
        let mut rc_bit_i = P::ZEROS;
        for r in 0..NUM_ROUNDS {
            let this_round = vars.local_values[reg_step(r)];
            let this_round_constant = P::from(F::from_canonical_u32(rc_value_bit(r, i) as u32));
            rc_bit_i += this_round * this_round_constant;
        }

        xor_gen(a_prime_prime_0_0_bits[i], rc_bit_i)
    };

    let a_prime_prime_prime_0_0_lo = vars.local_values[reg_a_prime_prime_prime(0, 0)];
    let a_prime_prime_prime_0_0_hi = vars.local_values[reg_a_prime_prime_prime(0, 0) + 1];
    let computed_a_prime_prime_prime_0_0_lo = (0..32)
        .rev()
        .fold(P::ZEROS, |acc, z| acc.doubles() + get_xored_bit(z));
    let computed_a_prime_prime_prime_0_0_hi = (32..64)
        .rev()
        .fold(P::ZEROS, |acc, z| acc.doubles() + get_xored_bit(z));
    yield_constr.constraint(computed_a_prime_prime_prime_0_0_lo - a_prime_prime_prime_0_0_lo);
    yield_constr.constraint(computed_a_prime_prime_prime_0_0_hi - a_prime_prime_prime_0_0_hi);

    // Enforce that this round's output equals the next round's input.
    for x in 0..5 {
        for y in 0..5 {
            let output_lo = vars.local_values[reg_a_prime_prime_prime(x, y)];
            let output_hi = vars.local_values[reg_a_prime_prime_prime(x, y) + 1];
            let input_lo = vars.next_values[reg_a(x, y)];
            let input_hi = vars.next_values[reg_a(x, y) + 1];
            let is_last_round = vars.local_values[reg_step(NUM_ROUNDS - 1)];
            let not_last_round = P::ONES - is_last_round;
            yield_constr.constraint_transition(not_last_round * (output_lo - input_lo));
            yield_constr.constraint_transition(not_last_round * (output_hi - input_hi));
        }
    }
}

pub fn eval_keccak_round_circuit<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    vars: StarkEvaluationTargets<D>,
) {
    let two = builder.two();
    let two_ext = builder.two_extension();
    let four_ext = builder.constant_extension(F::Extension::from_canonical_u8(4));
    // C'[x, z] = xor(C[x, z], C[x - 1, z], C[x + 1, z - 1]).
    for x in 0..5 {
        for z in 0..64 {
            let xor = xor3_gen_circuit(
                builder,
                vars.local_values[reg_c(x, z)],
                vars.local_values[reg_c((x + 4) % 5, z)],
                vars.local_values[reg_c((x + 1) % 5, (z + 63) % 64)],
            );
            let c_prime = vars.local_values[reg_c_prime(x, z)];
            let diff = builder.sub_extension(c_prime, xor);
            yield_constr.constraint(builder, diff);
        }
    }

    // Check that the input limbs are consistent with A' and D.
    // A[x, y, z] = xor(A'[x, y, z], D[x, y, z])
    //            = xor(A'[x, y, z], C[x - 1, z], C[x + 1, z - 1])
    //            = xor(A'[x, y, z], C[x, z], C'[x, z]).
    // The last step is valid based on the identity we checked above.
    // It isn't required, but makes this check a bit cleaner.
    for x in 0..5 {
        for y in 0..5 {
            let a_lo = vars.local_values[reg_a(x, y)];
            let a_hi = vars.local_values[reg_a(x, y) + 1];
            let mut get_bit = |z| {
                let a_prime = vars.local_values[reg_a_prime(x, y, z)];
                let c = vars.local_values[reg_c(x, z)];
                let c_prime = vars.local_values[reg_c_prime(x, z)];
                xor3_gen_circuit(builder, a_prime, c, c_prime)
            };
            let bits_lo = (0..32).map(&mut get_bit).collect_vec();
            let bits_hi = (32..64).map(get_bit).collect_vec();
            let computed_lo = reduce_with_powers_ext_circuit(builder, &bits_lo, two);
            let computed_hi = reduce_with_powers_ext_circuit(builder, &bits_hi, two);
            let diff = builder.sub_extension(computed_lo, a_lo);
            yield_constr.constraint(builder, diff);
            let diff = builder.sub_extension(computed_hi, a_hi);
            yield_constr.constraint(builder, diff);
        }
    }

    // xor_{i=0}^4 A'[x, i, z] = C'[x, z], so for each x, z,
    // diff * (diff - 2) * (diff - 4) = 0, where
    // diff = sum_{i=0}^4 A'[x, i, z] - C'[x, z]
    for x in 0..5 {
        for z in 0..64 {
            let sum = builder.add_many_extension(
                [0, 1, 2, 3, 4].map(|i| vars.local_values[reg_a_prime(x, i, z)]),
            );
            let diff = builder.sub_extension(sum, vars.local_values[reg_c_prime(x, z)]);
            let diff_minus_two = builder.sub_extension(diff, two_ext);
            let diff_minus_four = builder.sub_extension(diff, four_ext);
            let constraint = builder.mul_many_extension([diff, diff_minus_two, diff_minus_four]);
            yield_constr.constraint(builder, constraint);
        }
    }

    // A''[x, y] = xor(B[x, y], andn(B[x + 1, y], B[x + 2, y])).
    for x in 0..5 {
        for y in 0..5 {
            let mut get_bit = |z| {
                let andn = andn_gen_circuit(
                    builder,
                    vars.local_values[reg_b((x + 1) % 5, y, z)],
                    vars.local_values[reg_b((x + 2) % 5, y, z)],
                );
                xor_gen_circuit(builder, vars.local_values[reg_b(x, y, z)], andn)
            };

            let reg_lo = reg_a_prime_prime(x, y);
            let reg_hi = reg_lo + 1;
            let lo = vars.local_values[reg_lo];
            let hi = vars.local_values[reg_hi];
            let bits_lo = (0..32).map(&mut get_bit).collect_vec();
            let bits_hi = (32..64).map(get_bit).collect_vec();
            let computed_lo = reduce_with_powers_ext_circuit(builder, &bits_lo, two);
            let computed_hi = reduce_with_powers_ext_circuit(builder, &bits_hi, two);
            let diff = builder.sub_extension(computed_lo, lo);
            yield_constr.constraint(builder, diff);
            let diff = builder.sub_extension(computed_hi, hi);
            yield_constr.constraint(builder, diff);
        }
    }

    // A'''[0, 0] = A''[0, 0] XOR RC
    let a_prime_prime_0_0_bits = (0..64)
        .map(|i| vars.local_values[reg_a_prime_prime_0_0_bit(i)])
        .collect_vec();
    let computed_a_prime_prime_0_0_lo =
        reduce_with_powers_ext_circuit(builder, &a_prime_prime_0_0_bits[0..32], two);
    let computed_a_prime_prime_0_0_hi =
        reduce_with_powers_ext_circuit(builder, &a_prime_prime_0_0_bits[32..64], two);
    let a_prime_prime_0_0_lo = vars.local_values[reg_a_prime_prime(0, 0)];
    let a_prime_prime_0_0_hi = vars.local_values[reg_a_prime_prime(0, 0) + 1];
    let diff = builder.sub_extension(computed_a_prime_prime_0_0_lo, a_prime_prime_0_0_lo);
    yield_constr.constraint(builder, diff);
    let diff = builder.sub_extension(computed_a_prime_prime_0_0_hi, a_prime_prime_0_0_hi);
    yield_constr.constraint(builder, diff);

    let mut get_xored_bit = |i| {
        let mut rc_bit_i = builder.zero_extension();
        for r in 0..NUM_ROUNDS {
            let this_round = vars.local_values[reg_step(r)];
            let this_round_constant =
                builder.constant_extension(F::from_canonical_u32(rc_value_bit(r, i) as u32).into());
            rc_bit_i = builder.mul_add_extension(this_round, this_round_constant, rc_bit_i);
        }

        xor_gen_circuit(builder, a_prime_prime_0_0_bits[i], rc_bit_i)
    };

    let a_prime_prime_prime_0_0_lo = vars.local_values[reg_a_prime_prime_prime(0, 0)];
    let a_prime_prime_prime_0_0_hi = vars.local_values[reg_a_prime_prime_prime(0, 0) + 1];
    let bits_lo = (0..32).map(&mut get_xored_bit).collect_vec();
    let bits_hi = (32..64).map(get_xored_bit).collect_vec();
    let computed_a_prime_prime_prime_0_0_lo =
        reduce_with_powers_ext_circuit(builder, &bits_lo, two);
    let computed_a_prime_prime_prime_0_0_hi =
        reduce_with_powers_ext_circuit(builder, &bits_hi, two);
    let diff = builder.sub_extension(
        computed_a_prime_prime_prime_0_0_lo,
        a_prime_prime_prime_0_0_lo,
    );
    yield_constr.constraint(builder, diff);
    let diff = builder.sub_extension(
        computed_a_prime_prime_prime_0_0_hi,
        a_prime_prime_prime_0_0_hi,
    );
    yield_constr.constraint(builder, diff);

    // Enforce that this round's output equals the next round's input.
    for x in 0..5 {
        for y in 0..5 {
            let output_lo = vars.local_values[reg_a_prime_prime_prime(x, y)];
            let output_hi = vars.local_values[reg_a_prime_prime_prime(x, y) + 1];
            let input_lo = vars.next_values[reg_a(x, y)];
            let input_hi = vars.next_values[reg_a(x, y) + 1];
            let is_last_round = vars.local_values[reg_step(NUM_ROUNDS - 1)];
            let diff = builder.sub_extension(input_lo, output_lo);
            let filtered_diff = builder.mul_sub_extension(is_last_round, diff, diff);
            yield_constr.constraint_transition(builder, filtered_diff);
            let diff = builder.sub_extension(input_hi, output_hi);
            let filtered_diff = builder.mul_sub_extension(is_last_round, diff, diff);
            yield_constr.constraint_transition(builder, filtered_diff);
        }
    }
}
