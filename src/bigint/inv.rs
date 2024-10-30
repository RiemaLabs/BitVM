use crate::dump::{RelOp, ValueExpr};
use crate::pseudo::OP_NDUP;
use crate::treepp::*;
use crate::{bigint::BigIntImpl, dump::ConstraintBuilder};
use core::ops::{Mul, Rem, Sub};
use num_bigint::BigUint;
use num_traits::Num;

impl<const N_BITS: u32, const LIMB_SIZE: u32> BigIntImpl<N_BITS, LIMB_SIZE> {
    pub fn div2() -> Script {
        script! {
            { Self::div2rem() }
            OP_DROP
        }
    }

    pub fn div2rem() -> Script {
        script! {
            { Self::N_LIMBS - 1 } OP_ROLL
            0
            { limb_shr1_carry(Self::HEAD) }

            for _ in 1..Self::N_LIMBS {
                { Self::N_LIMBS } OP_ROLL
                OP_SWAP
                { limb_shr1_carry(LIMB_SIZE) }
            }
        }
    }

    pub fn div3() -> Script {
        script! {
            { Self::div3rem() }
            OP_DROP
        }
    }

    pub fn div3_inv(builder: &ConstraintBuilder) -> Script {
        script! {
            { Self::div3rem_inv(builder) }
            OP_DROP
        }
    }

    pub fn div3rem() -> Script {
        script! {
            { Self::N_LIMBS - 1 } OP_ROLL
            0
            { limb_div3_carry(Self::HEAD) }

            for _ in 1..Self::N_LIMBS {
                { Self::N_LIMBS } OP_ROLL
                OP_SWAP
                { limb_div3_carry(LIMB_SIZE) }
            }
        }
    }

    pub fn div3rem_inv(builder: &ConstraintBuilder) -> Script {
        let mut index = 0;
        let head_inv_1 = builder.dump_assumption(
            builder.build_stack_rel(
                0,
                builder.build_mod_expr(
                    builder.build_symbolic_limb(0, Self::N_LIMBS as usize - 1),
                    builder.build_constant(3),
                ),
                RelOp::Eq,
            ),
            &mut index,
        );
        let head_inv_2 = builder.dump_assumption(
            builder.build_stack_rel(
                1,
                builder.build_div_expr(
                    builder.build_symbolic_limb(0, Self::N_LIMBS as usize - 1),
                    builder.build_constant(3),
                ),
                RelOp::Eq,
            ),
            &mut index,
        );
        let mut carry = builder.build_mod_expr(
            builder.build_symbolic_limb(0, Self::N_LIMBS as usize - 1),
            builder.build_constant(3),
        );
        fn new_inv(
            builder: &ConstraintBuilder,
            limb_index: usize,
            carry: &mut ValueExpr,
            index: &mut usize,
        ) -> Script {
            let new_expr = builder.build_add_expr(
                builder.build_mul_expr(carry.clone(), builder.build_constant(1 << 29)),
                builder.build_symbolic_limb(0, limb_index),
            );
            let inv_1 = builder.dump_assumption(
                builder.build_stack_rel(
                    0,
                    builder.build_mod_expr(new_expr.clone(), builder.build_constant(3)),
                    RelOp::Eq,
                ),
                index,
            );
            let inv_2 = builder.dump_assumption(
                builder.build_stack_rel(
                    1,
                    builder.build_div_expr(new_expr.clone(), builder.build_constant(3)),
                    RelOp::Eq,
                ),
                index,
            );
            *carry = builder.build_mod_expr(new_expr, builder.build_constant(3));
            script! {
                { inv_1 }
                { inv_2 }
            }
        }

        script! {
            { Self::N_LIMBS - 1 } OP_ROLL
            0
            { limb_div3_carry(Self::HEAD) }
            { head_inv_1 }
            { head_inv_2 }

            for i in 1..Self::N_LIMBS as usize {
                { Self::N_LIMBS } OP_ROLL
                OP_SWAP
                {
                    limb_div3_carry(LIMB_SIZE)
                }
                { new_inv(
                    builder,
                    Self::N_LIMBS as usize - i - 1,
                    &mut carry,
                    &mut index,
                )}
            }
        }
    }

    /// Input: a b
    ///  a is the modulus
    ///  b is the number
    ///
    /// The algorithm is from Constant Time Modular Inversion, Joppe W. Bos
    pub fn inv_stage1() -> Script {
        script! {
            { Self::push_zero() }
            { Self::roll(1) }
            { Self::push_one() }
            { Self::N_BITS } OP_NEGATE

            // The stack starts with
            //  u    N elements
            //  r    N elements
            //  v    N elements
            //  s    N elements
            //  k    1 element

            // send k to the altstack
            OP_TOALTSTACK

            // stack invariant for this loop: u, r, v, s | k
            for _ in 0..2 * Self::N_BITS {
                // copy u, v
                { Self::copy(3) }
                { Self::copy(2) }

                // check if u = v
                { Self::notequal(1, 0)}

                // if the algorithm has not terminated (u != v)
                OP_IF
                    // compute 2 * s
                    { Self::copy(0) }
                    { Self::double(0) }

                    // compute 2 * r
                    { Self::copy(3) }
                    { Self::double(0) }

                    // compute u/2
                    { Self::copy(5) }
                    { Self::div2rem() }

                    // current stack: u, r, v, s, 2 * s, 2 * r, u/2

                    // case 1: u = 0 mod 2
                    OP_NOTIF
                        // start stack: u, r, v, s, 2 * s, 2 * r, u/2 | k

                        // roll the 2 * s
                        { Self::roll(2) }
                        { Self::toaltstack() }

                        // roll the v
                        { Self::roll(3) }
                        { Self::toaltstack() }

                        // roll the r
                        { Self::roll(3) }
                        { Self::toaltstack() }
                        { Self::toaltstack() }

                        // remove the unused 2 * r
                        { Self::drop() }

                        // remove the unused s
                        { Self::drop() }

                        // remove the unused u
                        { Self::drop() }

                        { Self::fromaltstack() }
                        { Self::fromaltstack() }
                        { Self::fromaltstack() }
                        { Self::fromaltstack() }
                        // final stack: u/2, r, v, 2 * s | k
                    OP_ELSE
                        // compute v/2
                        { Self::copy(4) }
                        { Self::div2rem() }

                        // case 2: v = 0 mod 2
                        OP_NOTIF
                            // start stack: u, r, v, s, 2 * s, 2 * r, u/2, v/2 | k

                            { Self::toaltstack() }

                            // remove the unused u/2
                            { Self::drop() }
                            { Self::toaltstack() }

                            // remove the unused 2 * s
                            { Self::drop() }
                            { Self::toaltstack() }

                            // remove the unused v
                            { Self::drop() }

                            // remove the unused r
                            { Self::drop() }

                            { Self::fromaltstack() }
                            { Self::fromaltstack() }
                            { Self::fromaltstack() }
                            { Self::roll(2) }

                            // final stack: u, 2 * r, v/2, s | k
                        OP_ELSE
                            // copy u, v
                            { Self::copy(7) }
                            { Self::copy(6) }

                            // compute u > v
                            { Self::greaterthan(1, 0) }

                            // reorder u/2 and v/2 if u < v
                            OP_DUP OP_TOALTSTACK
                            OP_NOTIF
                                { Self::roll(1) }
                            OP_ENDIF

                            // compute (u - v)/2 (if u > v) or (v - u)/2 (if v > u)
                            { Self::sub(1, 0) }

                            // compute r + s
                            { Self::roll(5) }
                            { Self::roll(4) }
                            { Self::add(1, 0) }

                            OP_FROMALTSTACK

                            // case 3: u > v
                            OP_IF
                                // start stack: u, v, 2 * s, 2 * r, (u/2 - v/2), r + s | k

                                // roll the v
                                { Self::roll(4) }

                                // roll the 2 * s
                                { Self::roll(4) }

                                // remove the unused u
                                { Self::roll(5) }
                                { Self::drop() }

                                // remove the unused 2 * r
                                { Self::roll(4) }
                                { Self::drop() }

                                // final stack: (u/2 - v/2), r + s, v, 2 * s | k
                            OP_ELSE
                                // start stack: u, v, 2 * s, 2 * r, (v/2 - u/2), r + s | k

                                // remove the unused v
                                { Self::roll(4) }
                                { Self::drop() }

                                // remove the unused 2 * s
                                { Self::roll(3) }
                                { Self::drop() }

                                // final stack: u, 2 * r, (v/2 - u/2), r + s | k
                            OP_ENDIF
                        OP_ENDIF
                    OP_ENDIF

                    // increase k
                    OP_FROMALTSTACK
                    OP_1ADD
                    OP_TOALTSTACK
                OP_ENDIF
            }

            { Self::toaltstack() }
            { Self::drop() }
            { Self::drop() }
            { Self::drop() }
            { Self::fromaltstack() }
            OP_FROMALTSTACK

            // final stack: s k
        }
    }

    pub fn inv_stage2(modulus_hex: &str) -> Script {
        let modulus = BigUint::from_str_radix(modulus_hex, 16).unwrap();

        let inv_2 = BigUint::from(2u8).modpow(&modulus.clone().sub(BigUint::from(2u8)), &modulus);
        let inv_2k = inv_2.modpow(&BigUint::from(Self::N_BITS), &modulus);

        let mut inv_list = vec![];
        let mut cur = inv_2k;
        for _ in 0..=Self::N_BITS {
            inv_list.push(cur.clone());
            cur = cur.mul(&inv_2).rem(&modulus);
        }

        script! {
            { OP_NDUP(Self::N_BITS as usize) }
            for i in 0..=Self::N_BITS {
                { Self::N_BITS - i } OP_EQUAL OP_TOALTSTACK
            }
            { script! {
                for i in 0..=Self::N_BITS {
                    OP_FROMALTSTACK OP_IF
                        { Self::push_u32_le(&inv_list[i as usize].to_u32_digits()) }
                    OP_ENDIF
                }
            }.add_stack_hint(0, 9).add_altstack_hint(-(Self::N_BITS as i32) - 1, -(Self::N_BITS as i32) - 1)}
        }
    }
}

pub fn limb_shr1_carry(num_bits: u32) -> Script {
    let powers_of_2_script = if num_bits < 7 {
        script! {
            for i in 0..num_bits - 1 {
                { 2_u32.pow(i) }
            }
        }
    } else {
        script! {
            2 4 8 16 32 64              // 2^1 to 2^6
            for _ in 0..num_bits - 7 {
                OP_DUP OP_DUP OP_ADD
            }                           // 2^7 to 2^{num_bits - 1}
        }
    };

    script! {
        { powers_of_2_script }
        { num_bits - 1 } OP_ROLL
        OP_IF
            OP_DUP
        OP_ELSE
            0
        OP_ENDIF
        OP_TOALTSTACK

        { num_bits - 1 } OP_ROLL

        for _ in 0..num_bits - 2 {
            OP_2DUP OP_LESSTHANOREQUAL
            OP_IF
                OP_SWAP OP_SUB OP_SWAP OP_DUP OP_FROMALTSTACK OP_ADD OP_TOALTSTACK OP_SWAP
            OP_ELSE
                OP_NIP
            OP_ENDIF
        }

        OP_2DUP OP_LESSTHANOREQUAL
        OP_IF
            OP_SWAP OP_SUB OP_FROMALTSTACK OP_1ADD
        OP_ELSE
            OP_NIP OP_FROMALTSTACK
        OP_ENDIF
        OP_SWAP
    }
}

// divide limb by 3, also remainder
pub fn limb_div3_carry(limb_size: u32) -> Script {
    let max_limb = (1 << limb_size) as i64;

    let x_quotient = max_limb / 3;
    let x_remainder = max_limb % 3;

    let y_quotient = max_limb * 2 / 3;
    let y_remainder = max_limb * 2 % 3;

    let mut k = 0;
    let mut cur = 1;
    while cur < max_limb {
        k += 1;
        cur *= 3;
    }

    script! {
        1 2 3 6 9 18 27 54
        for _ in 0..k - 4 {
            OP_2DUP OP_ADD
            OP_DUP OP_DUP OP_ADD
        }

        { 2 * k } OP_ROLL OP_DUP
        0 OP_GREATERTHAN
        OP_IF
            OP_1SUB
            OP_IF
                { y_remainder } { y_quotient }
            OP_ELSE
                { x_remainder } { x_quotient }
            OP_ENDIF
        OP_ELSE
            0
        OP_ENDIF
        OP_TOALTSTACK

        { 2 * k + 1 } OP_ROLL OP_ADD

        for _ in 0..2 * k - 2 {
            OP_2DUP OP_LESSTHANOREQUAL
            OP_IF
                OP_SWAP OP_SUB 2 OP_PICK OP_FROMALTSTACK OP_ADD OP_TOALTSTACK
            OP_ELSE
                OP_NIP
            OP_ENDIF
        }

        OP_NIP OP_NIP OP_FROMALTSTACK OP_SWAP
    }
}

pub fn limb_div3_carry_inv(builder: &ConstraintBuilder, limb_size: u32) -> Script {
    let mut index = 0;
    let max_limb = (1 << limb_size) as i64;

    let x_quotient = max_limb / 3;
    let x_remainder = max_limb % 3;

    let y_quotient = max_limb * 2 / 3;
    let y_remainder = max_limb * 2 % 3;

    let mut k = 0;
    let mut cur = 1;
    while cur < max_limb {
        k += 1;
        cur *= 3;
    }
    let carry_script = builder.dump_assertion(
        builder.build_stack_rel(0, builder.build_symbolic(0), RelOp::Eq),
        &mut index,
    );
    let limb_script = builder.dump_assertion(
        builder.build_stack_rel(0, builder.build_symbolic(1), RelOp::Eq),
        &mut index,
    );
    let remainder = builder.build_if_expr(
        builder.build_rel(
            builder.build_symbolic(0),
            builder.build_constant(0),
            RelOp::Eq,
        ),
        builder.build_constant(0),
        builder.build_if_expr(
            builder.build_rel(
                builder.build_symbolic(0),
                builder.build_constant(1),
                RelOp::Eq,
            ),
            builder.build_constant(x_remainder as u128),
            builder.build_constant(y_remainder as u128),
        ),
    );
    let quotient = builder.build_if_expr(
        builder.build_rel(
            builder.build_symbolic(0),
            builder.build_constant(0),
            RelOp::Eq,
        ),
        builder.build_constant(0),
        builder.build_if_expr(
            builder.build_rel(
                builder.build_symbolic(0),
                builder.build_constant(1),
                RelOp::Eq,
            ),
            builder.build_constant(x_quotient as u128),
            builder.build_constant(y_quotient as u128),
        ),
    );
    let carry_res = builder.dump_assertion(
        builder.build_stack_rel(
            0,
            builder.build_add_expr(builder.build_symbolic(1), remainder),
            RelOp::Eq,
        ),
        &mut index,
    );
    let alt_res = builder.dump_assertion(
        builder.build_alt_stack_rel(0, quotient, RelOp::Eq),
        &mut index,
    );
    let inv1 = builder.dump_assertion(
        builder.build_rel(
            builder.build_add_expr(
                builder.build_mul_expr(builder.build_symbolic(0), builder.build_constant(1 << 29)),
                builder.build_symbolic(1),
            ),
            builder.build_add_expr(
                builder.build_mul_expr(builder.build_alt_stack(0), builder.build_constant(3)),
                builder.build_stack(0),
            ),
            RelOp::Eq,
        ),
        &mut index,
    );
    let inv2 = builder.dump_assertion(
        builder.build_rel(
            builder.build_stack(0),
            builder.build_mul_expr(builder.build_constant(2), builder.build_stack(1)),
            RelOp::Lt,
        ),
        &mut index,
    );

    let inv1_res = builder.dump_assumption(
        builder.build_rel(
            builder.build_add_expr(
                builder.build_mul_expr(builder.build_symbolic(0), builder.build_constant(1 << 29)),
                builder.build_symbolic(1),
            ),
            builder.build_add_expr(
                builder.build_mul_expr(builder.build_alt_stack(0), builder.build_constant(3)),
                builder.build_stack(0),
            ),
            RelOp::Eq,
        ),
        &mut index,
    );
    let inv2_res = builder.dump_assumption(
        builder.build_rel(
            builder.build_stack(0),
            builder.build_mul_expr(builder.build_constant(2), builder.build_stack(1)),
            RelOp::Lt,
        ),
        &mut index,
    );
    script! {
        1 2 3 6 9 18 27 54
        for _ in 0..k - 4 {
            OP_2DUP OP_ADD
            OP_DUP OP_DUP OP_ADD
        }

        { 2 * k } OP_ROLL
        { carry_script }
        OP_DUP
        0 OP_GREATERTHAN
        OP_IF
            OP_1SUB
            OP_IF
                { y_remainder } { y_quotient }
            OP_ELSE
                { x_remainder } { x_quotient }
            OP_ENDIF
        OP_ELSE
            0
        OP_ENDIF
        OP_TOALTSTACK

        { 2 * k + 1 } OP_ROLL
        { limb_script }
        OP_ADD
        { carry_res }
        { alt_res }
        // ignore basic range check, as it's obvious here.
        // check assumption 108 and 109 here (ref. div3_inner_inner.bs)
        { inv1 }
        { inv2 }
        for _ in 0..2 * k - 2 {
            OP_2DUP OP_LESSTHANOREQUAL
            OP_IF
                OP_SWAP OP_SUB 2 OP_PICK OP_FROMALTSTACK OP_ADD OP_TOALTSTACK
            OP_ELSE
                OP_NIP
            OP_ENDIF
        }
        { inv1_res }
        { inv2_res }
        OP_NIP OP_NIP OP_FROMALTSTACK OP_SWAP
    }
}

pub fn limb_div_carry_inner(builder: &ConstraintBuilder) -> Script {
    let mut index = 0;
    let remain1 = builder.dump_assertion(
        builder.build_stack_rel(1, builder.build_symbolic(2), RelOp::Eq),
        &mut index,
    );
    let remain2 = builder.dump_assertion(
        builder.build_stack_rel(2, builder.build_symbolic(3), RelOp::Eq),
        &mut index,
    );
    let stack_top = builder.dump_assertion(
        builder.build_stack_rel(
            0,
            builder.build_if_expr(
                builder.build_rel(
                    builder.build_symbolic(1),
                    builder.build_symbolic(0),
                    RelOp::Le,
                ),
                builder.build_sub_expr(builder.build_symbolic(0), builder.build_symbolic(1)),
                builder.build_symbolic(0),
            ),
            RelOp::Eq,
        ),
        &mut index,
    );
    let alt_stack = builder.dump_assertion(
        builder.build_alt_stack_rel(
            0,
            builder.build_if_expr(
                builder.build_rel(
                    builder.build_symbolic(1),
                    builder.build_symbolic(0),
                    RelOp::Le,
                ),
                builder.build_add_expr(builder.build_symbolic(4), builder.build_symbolic(3)),
                builder.build_symbolic(4),
            ),
            RelOp::Eq,
        ),
        &mut index,
    );
    let res_inv = builder.dump_assertion(
        builder.build_rel(
            builder.build_add_expr(
                builder.build_symbolic(0),
                builder.build_mul_expr(builder.build_constant(3), builder.build_symbolic(4)),
            ),
            builder.build_add_expr(
                builder.build_stack(0),
                builder.build_mul_expr(builder.build_alt_stack(0), builder.build_constant(3)),
            ),
            RelOp::Eq,
        ),
        &mut index,
    );
    let res_prop = builder.dump_assertion(
        builder.build_rel(builder.build_stack(0), builder.build_symbolic(1), RelOp::Lt),
        &mut index,
    );
    script! {
        OP_2DUP OP_LESSTHANOREQUAL
        OP_IF
            OP_SWAP OP_SUB 2 OP_PICK OP_FROMALTSTACK OP_ADD OP_TOALTSTACK
        OP_ELSE
            OP_NIP
        OP_ENDIF
        { remain1 }
        { remain2 }
        { stack_top }
        { alt_stack }
        { res_inv }
        { res_prop }
    }
}

#[cfg(test)]
mod test {
    use crate::bigint::inv::{limb_div3_carry, limb_shr1_carry};
    use crate::bigint::{U254, U64};
    use crate::treepp::*;
    // use bitcoin_script::analyzer::StackStatus;
    use core::ops::{Div, Shr};
    use num_bigint::{BigUint, RandomBits};
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    #[test]
    fn test_limb_shr1_carry() {
        println!("limb_shr1_carry: {} bytes", limb_shr1_carry(29).len());
        let mut prng = ChaCha20Rng::seed_from_u64(0);

        for _ in 0..100 {
            let mut a: u32 = prng.gen();
            a %= 1 << 29;

            let script = script! {
                { a }
                { 0 }
                { limb_shr1_carry(29) }
                { a & 1 } OP_EQUALVERIFY
                { a >> 1 } OP_EQUAL
            };

            run(script);
        }

        for _ in 0..100 {
            let mut a: u32 = prng.gen();
            a %= 1 << 29;

            let script = script! {
                { a }
                { 1 }
                { limb_shr1_carry(29) }
                { a & 1 } OP_EQUALVERIFY
                { (1 << 28) | (a >> 1) } OP_EQUAL
            };

            run(script);
        }
    }

    #[test]
    fn test_limb_div3_carry() {
        println!("limb_div3_carry: {} bytes", limb_div3_carry(29).len());
        let mut prng = ChaCha20Rng::seed_from_u64(0);

        for _ in 0..100 {
            let mut a: u32 = prng.gen();
            a %= 1 << 29;
            let k = 2_u32.pow(29);

            for r in 0..3 {
                let a2 = a + r * k;
                let b = a2 % 3;
                let c = a2 / 3;
                let script = script! {
                    { a }
                    { r }
                    { limb_div3_carry(29) }
                    { b } OP_EQUALVERIFY
                    { c } OP_EQUAL
                };

                run(script);
            }
        }
    }

    #[test]
    fn test_div2() {
        println!("U254.div2: {} bytes", U254::div2().len());
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        for _ in 0..100 {
            let a: BigUint = prng.sample(RandomBits::new(254));
            let c: BigUint = a.clone().shr(1);

            let script = script! {
                { U254::push_u32_le(&a.to_u32_digits()) }
                { U254::div2() }
                { U254::push_u32_le(&c.to_u32_digits()) }
                { U254::equalverify(1, 0) }
                OP_TRUE
            };
            run(script);
        }

        for _ in 0..100 {
            let a: BigUint = prng.sample(RandomBits::new(64));
            let c: BigUint = a.clone().shr(1);

            let script = script! {
                { U64::push_u32_le(&a.to_u32_digits()) }
                { U64::div2() }
                { U64::push_u32_le(&c.to_u32_digits()) }
                { U64::equalverify(1, 0) }
                OP_TRUE
            };
            run(script);
        }
    }

    #[test]
    fn test_div3() {
        println!("U254.div3: {} bytes", U254::div3().len());
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        for _ in 0..100 {
            let a: BigUint = prng.sample(RandomBits::new(254));
            let c: BigUint = a.clone().div(BigUint::from(3_u32));

            let script = script! {
                { U254::push_u32_le(&a.to_u32_digits()) }
                { U254::div3() }
                { U254::push_u32_le(&c.to_u32_digits()) }
                { U254::equalverify(1, 0) }
                OP_TRUE
            };
            run(script);
        }

        for _ in 0..100 {
            let a: BigUint = prng.sample(RandomBits::new(64));
            let c: BigUint = a.clone().div(BigUint::from(3_u32));

            let script = script! {
                { U64::push_u32_le(&a.to_u32_digits()) }
                { U64::div3() }
                { U64::push_u32_le(&c.to_u32_digits()) }
                { U64::equalverify(1, 0) }
                OP_TRUE
            };
            let stack = script.clone().analyze_stack();
            assert!(stack.is_valid_final_state_without_inputs());
            run(script);
        }
    }
}
