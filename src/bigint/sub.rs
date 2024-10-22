use bitcoin::opcodes::all::OP_ADD;

use crate::bigint::BigIntImpl;
use crate::dump::{ConstraintBuilder, RelOp, ValueExpr};
use crate::treepp::*;

impl<const N_BITS: u32, const LIMB_SIZE: u32> BigIntImpl<N_BITS, LIMB_SIZE> {
    /// Compute the difference of two BigInts
    pub fn sub(a: u32, b: u32) -> Script {
        script! {
            {Self::zip(a, b)}

            { 1 << LIMB_SIZE }

            // A0 - B0
            limb_sub_borrow OP_TOALTSTACK

            // from     A1      - (B1        + borrow_0)
            //   to     A{N-2}  - (B{N-2}    + borrow_{N-3})
            // stack shape: ai bi carry 1<<29 | stack[2] stack[3]...
            // stack new shape : ai+1 bi+1 carry' 1<<29 | alt[0]
            for _ in 0..Self::N_LIMBS - 2 {
                OP_ROT
                OP_ADD
                OP_SWAP
                limb_sub_borrow OP_TOALTSTACK
            }

            // A{N-1} - (B{N-1} + borrow_{N-2})
            OP_NIP
            OP_ADD
            { limb_sub_noborrow(Self::HEAD_OFFSET) }

            for _ in 0..Self::N_LIMBS - 1 {
                OP_FROMALTSTACK
            }
        }
    }

    pub fn sub_inv(builder: &ConstraintBuilder, a: u32, b: u32) -> Script {
        let mut index = 0;
        let mut carry = builder.build_if_expr(
            builder.build_rel(
                builder.build_sub_expr(
                    builder.build_symbolic_limb(0, 0),
                    builder.build_symbolic_limb(1, 0),
                ),
                builder.build_constant(0),
                RelOp::Lt,
            ),
            builder.build_constant(1),
            builder.build_constant(0),
        );
        fn sub_inv(
            builder: &ConstraintBuilder,
            i: usize,
            carry: &mut ValueExpr,
            index: &mut usize,
        ) -> Script {
            let value = builder.dump_assumption(
                builder.build_stack_rel(
                    0,
                    builder.build_add_expr(
                        builder.build_sub_expr(
                            builder.build_sub_expr(
                                builder.build_symbolic_limb(0, i),
                                builder.build_symbolic_limb(1, i),
                            ),
                            carry.clone(),
                        ),
                        builder.build_if_expr(
                            builder.build_rel(
                                builder.build_sub_expr(
                                    builder.build_sub_expr(
                                        builder.build_symbolic_limb(0, i),
                                        builder.build_symbolic_limb(1, i),
                                    ),
                                    carry.clone(),
                                ),
                                builder.build_constant(0),
                                RelOp::Lt,
                            ),
                            builder.build_constant(1 << 29),
                            builder.build_constant(0),
                        ),
                    ),
                    RelOp::Eq,
                ),
                index,
            );
            *carry = builder.build_if_expr(
                builder.build_rel(
                    builder.build_sub_expr(
                        builder.build_sub_expr(
                            builder.build_symbolic_limb(0, i),
                            builder.build_symbolic_limb(1, i),
                        ),
                        carry.clone(),
                    ),
                    builder.build_constant(0),
                    RelOp::Lt,
                ),
                builder.build_constant(1),
                builder.build_constant(0),
            );
            let carry_script = builder
                .dump_assumption(builder.build_stack_rel(1, carry.clone(), RelOp::Eq), index);
            script! {
                {value}
                {carry_script}
                {
                    builder.dump_assumption(
                        builder.build_stack_rel(
                            2,
                            builder.build_constant(1<<29),
                            RelOp::Eq
                        ),index)
                }
            }
        }

        script! {
            {Self::zip(a, b)}

            { 1 << LIMB_SIZE }

            // A0 - B0
            limb_sub_borrow
            {
                builder.dump_assumption(
                    builder.build_stack_rel(
                        0,
                        builder.build_add_expr(
                            builder.build_sub_expr(
                                builder.build_symbolic_limb(0, 0),
                                builder.build_symbolic_limb(1, 0),
                            ),
                            builder.build_if_expr(
                                builder.build_rel(
                                    builder.build_sub_expr(
                                        builder.build_symbolic_limb(0, 0),
                                        builder.build_symbolic_limb(1, 0),
                                    ),
                                    builder.build_constant(0),
                                    RelOp::Lt,
                                ),
                                builder.build_constant(1 << LIMB_SIZE),
                                builder.build_constant(0),
                            ),
                        ),
                        RelOp::Eq,
                    ),
                    &mut index,
                )
            }
            {
                builder.dump_assumption(
                    builder.build_stack_rel(
                        1,
                        carry.clone(),
                        RelOp::Eq,
                    ),
                    &mut index,
                )
            }
            {
                builder.dump_assumption(
                    builder.build_stack_rel(
                        2,
                        builder.build_constant(1<<LIMB_SIZE),
                        RelOp::Eq
                    ), &mut index
                )
            }
            OP_TOALTSTACK

            // from     A1      - (B1        + borrow_0)
            //   to     A{N-2}  - (B{N-2}    + borrow_{N-3})
            for i in 0..Self::N_LIMBS - 2 {
                OP_ROT
                OP_ADD
                OP_SWAP
                limb_sub_borrow
                {
                    sub_inv(builder, i as usize+1, &mut carry, &mut index)
                }
                OP_TOALTSTACK
            }

            // A{N-1} - (B{N-1} + borrow_{N-2})
            OP_NIP
            OP_ADD
            { limb_sub_noborrow(Self::HEAD_OFFSET) }
            {
                builder.dump_assumption(
                    builder.build_stack_rel(
                        0,
                        builder.build_add_expr(
                            builder.build_sub_expr(
                                builder.build_sub_expr(
                                    builder.build_symbolic_limb(0, Self::N_LIMBS as usize - 1),
                                    builder.build_symbolic_limb(1, Self::N_LIMBS as usize - 1),
                                ),
                                carry.clone(),
                            ),
                            builder.build_if_expr(
                                builder.build_rel(
                                    builder.build_sub_expr(
                                        builder.build_sub_expr(
                                            builder.build_symbolic_limb(0, Self::N_LIMBS as usize - 1),
                                            builder.build_symbolic_limb(1, Self::N_LIMBS as usize - 1),
                                        ),
                                        carry,
                                    ),
                                    builder.build_constant(0),
                                    RelOp::Lt,
                                ),
                                builder.build_constant(Self::HEAD_OFFSET as u128),
                                builder.build_constant(0),
                            ),
                        ),
                        RelOp::Eq,
                    ),
                    &mut index,
                )
            }
            for _ in 0..Self::N_LIMBS - 1 {
                OP_FROMALTSTACK
            }
        }
    }
}

/// Compute the difference of two limbs, including the carry bit
///
/// Author: @stillsaiko
pub fn limb_sub_borrow() -> Script {
    script! {
        OP_ROT OP_ROT
        OP_SUB
        OP_DUP
        0
        OP_LESSTHAN
        OP_TUCK
        OP_IF
            2 OP_PICK OP_ADD
        OP_ENDIF
    }
}

/// Compute the sum of two limbs, dropping the carry bit
///
/// Author: @weikengchen
pub fn limb_sub_noborrow(head_offset: u32) -> Script {
    script! {
        OP_SUB
        OP_DUP
        0
        OP_LESSTHAN
        OP_IF
            { head_offset }
            OP_ADD
        OP_ENDIF
    }
}

#[cfg(test)]
mod test {
    use crate::bigint::{U254, U64};
    use crate::{run_as_chunks, treepp::*};
    use core::ops::{Rem, Shl};
    use num_bigint::{BigUint, RandomBits};
    use num_traits::One;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    #[test]
    fn test_sub() {
        let mut prng = ChaCha20Rng::seed_from_u64(0);

        for _ in 0..100 {
            let a: BigUint = prng.sample(RandomBits::new(254));
            let b: BigUint = prng.sample(RandomBits::new(254));
            let mut c: BigUint = BigUint::one().shl(254) + &a - &b;
            c = c.rem(BigUint::one().shl(254));

            let script = script! {
                { U254::push_u32_le(&a.to_u32_digits()) }
                { U254::push_u32_le(&b.to_u32_digits()) }
                { U254::sub(1, 0) }
                { U254::push_u32_le(&c.to_u32_digits()) }
                { U254::equalverify(1, 0) }
                OP_TRUE
            };
            run(script);

            let script = script! {
                { U254::push_u32_le(&b.to_u32_digits()) }
                { U254::push_u32_le(&a.to_u32_digits()) }
                { U254::sub(0, 1) }
                { U254::push_u32_le(&c.to_u32_digits()) }
                { U254::equalverify(1, 0) }
                OP_TRUE
            };
            run(script);
        }

        for _ in 0..100 {
            let a: BigUint = prng.sample(RandomBits::new(64));
            let b: BigUint = prng.sample(RandomBits::new(64));
            let mut c: BigUint = BigUint::one().shl(64) + &a - &b;
            c = c.rem(BigUint::one().shl(64));

            let script = script! {
                { U64::push_u32_le(&a.to_u32_digits()) }
                { U64::push_u32_le(&b.to_u32_digits()) }
                { U64::sub(1, 0) }
                { U64::push_u32_le(&c.to_u32_digits()) }
                { U64::equalverify(1, 0) }
                OP_TRUE
            };
            run(script);

            let script = script! {
                { U64::push_u32_le(&b.to_u32_digits()) }
                { U64::push_u32_le(&a.to_u32_digits()) }
                { U64::sub(0, 1) }
                { U64::push_u32_le(&c.to_u32_digits()) }
                { U64::equalverify(1, 0) }
                OP_TRUE
            };
            run(script);
        }
    }

    #[test]
    fn test_sub_as_chunks() {
        let mut prng = ChaCha20Rng::seed_from_u64(0);

        let a: BigUint = prng.sample(RandomBits::new(254));
        let b: BigUint = prng.sample(RandomBits::new(254));
        let mut c: BigUint = BigUint::one().shl(254) + &a - &b;
        c = c.rem(BigUint::one().shl(254));

        let script = script! {
            { U254::push_u32_le(&a.to_u32_digits()) }
            { U254::push_u32_le(&b.to_u32_digits()) }
            { U254::sub(1, 0) }
            { U254::push_u32_le(&c.to_u32_digits()) }
            { U254::equalverify(1, 0) }
            OP_TRUE
        };
        run_as_chunks(script, 500000, 1000)
    }
}
