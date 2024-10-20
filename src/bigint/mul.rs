use std::array;

use serde_json::Value;

use crate::bigint::BigIntImpl;
use crate::dump::{ConstraintBuilder, RelOp, ValueExpr};
use crate::pseudo::push_to_stack;
use crate::treepp::{script, Script};

impl<const N_BITS: u32, const LIMB_SIZE: u32> BigIntImpl<N_BITS, LIMB_SIZE> {
    pub fn mul() -> Script {
        script! {
            { Self::convert_to_be_bits_toaltstack() }

            { push_to_stack(0,Self::N_LIMBS as usize) }


            OP_FROMALTSTACK
            OP_IF
                { Self::copy(1) }
                { Self::add(1, 0) }
            OP_ENDIF

            for _ in 1..N_BITS - 1 {
                { Self::roll(1) }
                { Self::double(0) }
                { Self::roll(1) }
                OP_FROMALTSTACK
                OP_IF
                    { Self::copy(1) }
                    { Self::add(1, 0) }
                OP_ENDIF
            }

            { Self::roll(1) }
            { Self::double(0) }
            OP_FROMALTSTACK
            OP_IF
                { Self::add(1, 0) }
            OP_ELSE
                { Self::drop() }
            OP_ENDIF
        }
    }

    pub fn mul_ver(builder: &ConstraintBuilder) -> Script {
        let mut index: usize = 0;
        let mut res_expr: [ValueExpr; 9] = array::from_fn(|_| ValueExpr::Constant(0)); // U254
        let mut carry = ValueExpr::Constant(0);
        fn init(
            builder: &ConstraintBuilder,
            i: usize,
            res_expr: &mut [ValueExpr; 9],
            index: &mut usize,
        ) -> Script {
            res_expr[i] = builder.build_if_expr(
                builder.build_rel(
                    builder.build_bit_of_symbolic_limb(0, 1),
                    builder.build_constant(1),
                    RelOp::Eq,
                ),
                builder.build_symbolic_limb(1, i),
                builder.build_constant(0),
            );
            builder.dump_assertion(
                builder.build_stack_rel(i, res_expr[i].clone(), RelOp::Eq),
                index,
            )
        }

        fn double_ver(
            builder: &ConstraintBuilder,
            i: usize,
            j: usize,
            index: &mut usize,
        ) -> Script {
            builder.dump_assertion(
                builder.build_lshift_symbolic_stack_limb(29, 1, i as u128, j - 9),
                index,
            )
        }

        fn add_res(
            builder: &ConstraintBuilder,
            i: usize,
            j: usize,
            index: &mut usize,
            carry: &mut ValueExpr,
            res_expr: &mut [ValueExpr; 9],
        ) -> Script {
            if j == 0 {
                *carry = ValueExpr::Constant(0);
            }
            let script = builder.dump_assertion(
                builder.build_stack_rel(
                    j,
                    builder.build_overflow_exp(
                        builder.build_add_expr(
                            builder.build_add_expr(
                                res_expr[j].clone(),
                                builder.build_if_expr(
                                    builder.build_rel(
                                        builder.build_bit_of_symbolic_limb(0, i as u128),
                                        builder.build_constant(1),
                                        RelOp::Eq,
                                    ),
                                    builder.build_stack(9 + j),
                                    builder.build_constant(0),
                                ),
                            ),
                            (*carry).clone(),
                        ),
                        if j == 8 { 22 } else { 29 },
                    ),
                    RelOp::Eq,
                ),
                index,
            );
            if j != 8 {
                *carry = builder.build_rshift_expr(
                    builder.build_add_expr(
                        builder.build_add_expr(
                            res_expr[j].clone(),
                            builder.build_if_expr(
                                builder.build_rel(
                                    builder.build_bit_of_symbolic_limb(0, i as u128),
                                    builder.build_constant(1),
                                    RelOp::Eq,
                                ),
                                builder.build_stack(9 + j),
                                builder.build_constant(0),
                            ),
                        ),
                        (*carry).clone(),
                    ),
                    builder.build_constant(29),
                );
            }
            res_expr[j] = builder.build_overflow_exp(
                builder.build_add_expr(
                    builder.build_add_expr(
                        res_expr[j].clone(),
                        builder.build_if_expr(
                            builder.build_rel(
                                builder.build_bit_of_symbolic_limb(0, i as u128),
                                builder.build_constant(1),
                                RelOp::Eq,
                            ),
                            builder.build_lshift_symbolic_limb(1, i as u128, j),
                            builder.build_constant(0),
                        ),
                    ),
                    (*carry).clone(),
                ),
                if j == 8 { 22 } else { 29 },
            );
            script
        }

        script! {
            { Self::convert_to_be_bits_toaltstack() }

            { push_to_stack(0,Self::N_LIMBS as usize) }


            OP_FROMALTSTACK
            OP_IF
                { Self::copy(1) }
                { Self::add(1, 0) }
            OP_ENDIF
            for i in 0..Self::N_LIMBS as usize {
                {
                    init(builder,i,&mut res_expr,&mut index)
                }
            }
            for i in Self::N_LIMBS as usize..(Self::N_LIMBS * 2) as usize{
                {
                    builder.dump_assertion(builder.build_stack_rel(
                        i,
                        builder.build_symbolic_limb(1, i - Self::N_LIMBS as usize),
                        RelOp::Eq,
                    ),&mut index)
                }
            }
            for i in 1..N_BITS - 1 {
                { Self::roll(1) }
                { Self::double(0) }
                { Self::roll(1) }
                OP_FROMALTSTACK
                OP_IF
                    { Self::copy(1) }
                    { Self::add(1, 0) }
                OP_ENDIF
                {
                    add_res(&builder, i as usize, 0, &mut index, &mut carry, &mut res_expr)
                }
                for j in 1..(Self::N_LIMBS as usize) {
                    {
                        add_res(&builder, i as usize, j, &mut index, &mut carry, &mut res_expr)
                    }
                }
                for j in Self::N_LIMBS as usize..(Self::N_LIMBS * 2) as usize {
                    {
                        double_ver(&builder, i as usize, j, &mut index)
                    }
                }
            }

            { Self::roll(1) }
            { Self::double(0) }
            OP_FROMALTSTACK
            OP_IF
                { Self::add(1, 0) }
            OP_ELSE
                { Self::drop() }
            OP_ENDIF
        }
    }
}

#[cfg(test)]
mod test {
    use crate::bigint::{U254, U64};
    use crate::{execute_script_as_chunks, treepp::*};
    use core::ops::{Mul, Rem, Shl};
    use num_bigint::{BigUint, RandomBits};
    use num_traits::One;
    use rand::{Rng, SeedableRng};
    use rand_chacha::ChaCha20Rng;

    #[test]
    fn test_mul() {
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        for _ in 0..3 {
            let a: BigUint = prng.sample(RandomBits::new(254));
            let b: BigUint = prng.sample(RandomBits::new(254));
            let c: BigUint = (a.clone().mul(b.clone())).rem(BigUint::one().shl(254));

            let script = script! {
                { U254::push_u32_le(&a.to_u32_digits()) }
                { U254::push_u32_le(&b.to_u32_digits()) }
                { U254::mul() }
                { U254::push_u32_le(&c.to_u32_digits()) }
                { U254::equalverify(1, 0) }
                OP_TRUE
            };
            run(script);
        }

        for _ in 0..3 {
            let a: BigUint = prng.sample(RandomBits::new(64));
            let b: BigUint = prng.sample(RandomBits::new(64));
            let c: BigUint = (a.clone().mul(b.clone())).rem(BigUint::one().shl(64));

            let script = script! {
                { U64::push_u32_le(&a.to_u32_digits()) }
                { U64::push_u32_le(&b.to_u32_digits()) }
                { U64::mul() }
                { U64::push_u32_le(&c.to_u32_digits()) }
                { U64::equalverify(1, 0) }
                OP_TRUE
            };
            run(script);
        }
    }

    #[test]
    fn test_mul_as_chunks() {
        let mut prng = ChaCha20Rng::seed_from_u64(0);
        let a: BigUint = prng.sample(RandomBits::new(254));
        let b: BigUint = prng.sample(RandomBits::new(254));
        let c: BigUint = (a.clone().mul(b.clone())).rem(BigUint::one().shl(254));

        let script = script! {
            { U254::push_u32_le(&a.to_u32_digits()) }
            { U254::push_u32_le(&b.to_u32_digits()) }
            { U254::mul() }
            { U254::push_u32_le(&c.to_u32_digits()) }
            { U254::equalverify(1, 0) }
            OP_TRUE
        };
        println!("compiled size: {:?}", script.clone().compile().len());
        let exec_result = execute_script_as_chunks(script, 20000, 400);
        println!("Execute info: {}", exec_result);
        assert!(exec_result.success);
    }
}
