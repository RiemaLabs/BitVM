use super::treepp::*;
use sha2::{Digest, Sha256};
use std::cmp::*;

#[allow(non_snake_case)]
pub fn OP_HINT() -> Script {
    script! {
        OP_DEPTH OP_1SUB OP_ROLL
    }
}

pub fn check_0_or_1() -> Script {
    script! {
        OP_DUP 0 OP_GREATERTHANOREQUAL OP_VERIFY
        OP_DUP 1 OP_LESSTHANOREQUAL OP_VERIFY
    }
}

pub fn decompose_positions_gadget(n: u32) -> Script {
    script! {
        // stack:
        // - pos
        // - bit hints
        // - remainder hint

        OP_DUP OP_TOALTSTACK

        for _ in 0..n - 1 {
            OP_DUP OP_ADD OP_SWAP check_0_or_1 OP_ADD OP_DUP OP_TOALTSTACK
        }

        OP_DUP OP_ADD OP_SWAP check_0_or_1 OP_ADD
        OP_EQUALVERIFY

        for _ in 0..n {
            OP_FROMALTSTACK
        }
    }
}

pub fn skip_one_and_extract_bits_gadget(n: u32) -> Script {
    script! {
        // stack:
        // - pos
        // - n+1 bits
        // - remainder

        for _ in 0..(n + 1) {
            OP_DUP OP_ADD
            OP_SWAP check_0_or_1 OP_ADD
        }

        OP_EQUALVERIFY
    }
}

pub fn qm31_reverse() -> Script {
    script! {
        OP_SWAP
        OP_2SWAP
        OP_SWAP
    }
}

pub fn copy_to_altstack_top_item_first_in_gadget(n: usize) -> Script {
    script! {
        if n > 0 {
            OP_DUP OP_TOALTSTACK
        }
        if n > 1 {
            OP_OVER OP_TOALTSTACK
        }
        for i in 2..n {
            { i } OP_PICK OP_TOALTSTACK
        }
    }
}

pub fn dup_m31_vec_gadget(len: usize) -> Script {
    if len == 1 {
        script! {
            OP_DUP
        }
    } else if len == 2 {
        script! {
            OP_2DUP
        }
    } else if len == 4 {
        script! {
            // A B C D
            OP_2SWAP
            // C D A B
            OP_2DUP
            // C D A B A B
            OP_2ROT
            // A B A B C D
            OP_2DUP
            // A B A B C D C D
            OP_2ROT
            // A B C D C D A B
            OP_2SWAP
            // A B C D A B C D
        }
    } else {
        script! {
            for _ in 0..len {
                { len - 1 } OP_PICK
            }
        }
    }
}

pub fn m31_vec_from_bottom_gadget(len: usize) -> Script {
    script! {
        for _ in 0..len {
            {OP_HINT()}
        }
    }
}

pub fn limb_to_le_bits_stark(num_bits: u32) -> Script {
    assert!(num_bits >= 2);
    let min_i = min(22, num_bits - 1);
    script! {
        // Push the powers of 2 onto the stack
        // First, all powers of 2 that we can push as 3-byte numbers
        for i in 0..min_i - 1  {
            { 2 << i } OP_TOALTSTACK
        }
        { 2 << (min_i - 1) }
        if num_bits - 1 > min_i {
            OP_DUP OP_TOALTSTACK

            // Then, we double powers of 2 to generate the 4-byte numbers
            for _ in min_i..num_bits - 2 {
                OP_DUP
                OP_ADD
                OP_DUP OP_TOALTSTACK
            }

            OP_DUP
            OP_ADD OP_TOALTSTACK
        } else {
            OP_TOALTSTACK
        }

        for _ in 0..num_bits - 2 {
            OP_FROMALTSTACK
            OP_2DUP OP_GREATERTHANOREQUAL
            OP_IF
                OP_SUB 1
            OP_ELSE
                OP_DROP 0
            OP_ENDIF
            OP_SWAP
        }

        OP_FROMALTSTACK
        OP_2DUP OP_GREATERTHANOREQUAL
        OP_IF
            OP_SUB 1
        OP_ELSE
            OP_DROP 0
        OP_ENDIF

        OP_SWAP
    }
}

pub fn limb_to_be_bits_toaltstack_common(num_bits: u32) -> Script {
    assert!(num_bits >= 2);
    let min_i = min(22, num_bits - 1);
    script! {
        OP_TOALTSTACK

        // Push the powers of 2 onto the stack
        // First, all powers of 2 that we can push as 3-byte numbers
        for i in 0..min_i  {
            { 2 << i }
        }
        // Then, we double powers of 2 to generate the 4-byte numbers
        for _ in min_i..num_bits - 1 {
            OP_DUP
            OP_DUP
            OP_ADD
        }

        OP_FROMALTSTACK

        for _ in 0..num_bits - 2 {
            OP_2DUP OP_LESSTHANOREQUAL
            OP_IF
                OP_SWAP OP_SUB 1
            OP_ELSE
                OP_NIP 0
            OP_ENDIF
            OP_TOALTSTACK
        }

        OP_2DUP OP_LESSTHANOREQUAL
        OP_IF
            OP_SWAP OP_SUB 1
        OP_ELSE
            OP_NIP 0
        OP_ENDIF
    }
}

pub fn limb_to_be_bits_toaltstack_except_lowest_1bit(num_bits: u32) -> Script {
    script! {
        { limb_to_be_bits_toaltstack_common(num_bits) }
        OP_TOALTSTACK OP_DROP
    }
}

pub fn limb_to_be_bits_toaltstack_except_lowest_2bits(num_bits: u32) -> Script {
    script! {
        { limb_to_be_bits_toaltstack_common(num_bits) }
        OP_DROP
        OP_DROP
    }
}

pub fn hash() -> Script {
    script! {
        OP_SHA256
    }
}

pub fn hash_m31_vec_gadget(len: usize) -> Script {
    if len == 0 {
        script! {
            { Sha256::new().finalize().to_vec() }
        }
    } else {
        script! {
            hash
            for _ in 1..len {
                OP_CAT hash
            }
        }
    }
}

pub(crate) fn query_and_verify_internal(len: usize, logn: usize) -> Script {
    script! {
        // left right path | root_hash pos_(logn-1 .. 1)
        { m31_vec_from_bottom_gadget(len) }
        // right path left_(3..0) | root_hash pos_(logn-1 .. 1)

        // duplicate the left
        { dup_m31_vec_gadget(len) }
        // right path left left | root_hash pos_(logn-1 .. 1)

        // hash the left and keep the hash in the altstack
        { hash_m31_vec_gadget(len) }
        hash
        // right path left left_hash | root_hash pos_(logn-1 .. 1)
        OP_TOALTSTACK

        { m31_vec_from_bottom_gadget(len) }

        { dup_m31_vec_gadget(len) }

        { hash_m31_vec_gadget(len) }
        hash
        // path left right right_hash | root_hash pos_(logn-1 .. 1)
        // put the left hash out and merge into the parent hash
        OP_FROMALTSTACK
        OP_SWAP OP_CAT hash
        // path left right hash_of_left&right | root_hash pos_(logn-1 .. 1)
        { verify(logn - 1) }
    }
}

pub fn query_and_verify(len: usize, logn: usize) -> Script {
    script! {
        // left right path root_hash pos
        OP_SWAP OP_TOALTSTACK
        // left right path pos | root_hash
        { limb_to_be_bits_toaltstack_except_lowest_1bit(logn as u32) }
        // left right path | root_hash pos_(logn-1 .. 1)
        { query_and_verify_internal(len, logn) }
    }
}

pub fn verify(path_len: usize) -> Script {
    script! {
        // path left right hash_of_left&right | root_hash pos_(logn-1 .. 1)
        for _ in 0..path_len {
            OP_HINT // origin_xx
            OP_FROMALTSTACK OP_IF OP_SWAP OP_ENDIF
            OP_CAT hash
        }

        OP_FROMALTSTACK
        OP_EQUALVERIFY
    }
}
