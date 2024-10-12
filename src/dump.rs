use std::fmt::format;
use std::fs;

use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;

use serde_json::Value;

static mut VERIFED_FILE_PATH: Option<String> = None;

pub fn writein_verified_meta(input: String) {
    unsafe {
        if let Some(ref path) = VERIFED_FILE_PATH {
            let path = Path::new(path);
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).expect("Failed to create directories");
            }
            let mut file = OpenOptions::new()
                .create(true)
                .append(true)
                .open(path)
                .expect("Failed to open file");
            writeln!(file, "{}", input).expect("Failed to write to file");
        }
    }
}

#[derive(Clone)]
pub enum MetaType {
    SymbolicVar(usize),
    Assertion(usize, BoolExpr),
}

#[derive(Clone)]
pub enum ValueExpr {
    RefSymbolVar(usize),
    RefSymbolLimb(usize, usize),
    RefStack(usize),    // offset in main stack
    RefAltStack(usize), // offset in alt stack
    Constant(u128),     // TODO: Constants within 2^254
    Add(Box<ValueExpr>, Box<ValueExpr>),
    Sub(Box<ValueExpr>, Box<ValueExpr>),
    Mul(Box<ValueExpr>, Box<ValueExpr>),
    IfElse(Box<BoolExpr>, Box<ValueExpr>, Box<ValueExpr>), // If-Else expression
}

#[derive(Clone)]
pub enum BoolExpr {
    Eq(Box<ValueExpr>, Box<ValueExpr>),
    Neq(Box<ValueExpr>, Box<ValueExpr>),
    Gt(Box<ValueExpr>, Box<ValueExpr>),
    Lt(Box<ValueExpr>, Box<ValueExpr>),
    Ge(Box<ValueExpr>, Box<ValueExpr>),
    Le(Box<ValueExpr>, Box<ValueExpr>),
    And(Box<BoolExpr>, Box<BoolExpr>),
    Or(Box<BoolExpr>, Box<BoolExpr>),
    Not(Box<BoolExpr>),
}

impl ValueExpr {
    pub fn to_string(&self) -> String {
        match self {
            ValueExpr::RefSymbolVar(i) => format!("v{}", i),
            ValueExpr::RefSymbolLimb(i, j) => format!("limbs{}[{}]", i, j),
            ValueExpr::RefStack(i) => format!("stack[{}]", i),
            ValueExpr::RefAltStack(i) => format!("altstack[{}]", i),
            ValueExpr::Constant(val) => format!("{}", val),
            ValueExpr::Add(lhs, rhs) => format!("({} + {})", lhs.to_string(), rhs.to_string()),
            ValueExpr::Sub(lhs, rhs) => format!("({} - {})", lhs.to_string(), rhs.to_string()),
            ValueExpr::Mul(lhs, rhs) => format!("({} * {})", lhs.to_string(), rhs.to_string()),
            ValueExpr::IfElse(cond, then_expr, else_expr) => format!(
                "(if {} then {} else {})",
                cond.to_string(),
                then_expr.to_string(),
                else_expr.to_string()
            ),
        }
    }
}

impl BoolExpr {
    pub fn to_string(&self) -> String {
        match self {
            BoolExpr::Eq(lhs, rhs) => format!("({} == {})", lhs.to_string(), rhs.to_string()),
            BoolExpr::Neq(lhs, rhs) => format!("({} != {})", lhs.to_string(), rhs.to_string()),
            BoolExpr::Gt(lhs, rhs) => format!("({} > {})", lhs.to_string(), rhs.to_string()),
            BoolExpr::Lt(lhs, rhs) => format!("({} < {})", lhs.to_string(), rhs.to_string()),
            BoolExpr::Ge(lhs, rhs) => format!("({} >= {})", lhs.to_string(), rhs.to_string()),
            BoolExpr::Le(lhs, rhs) => format!("({} <= {})", lhs.to_string(), rhs.to_string()),
            BoolExpr::And(lhs, rhs) => format!("({} && {})", lhs.to_string(), rhs.to_string()),
            BoolExpr::Or(lhs, rhs) => format!("({} || {})", lhs.to_string(), rhs.to_string()),
            BoolExpr::Not(expr) => format!("!({})", expr.to_string()),
        }
    }
}

#[allow(dead_code)]
#[derive(Clone)]
pub enum RelOp {
    Eq,
    Neq,
    Gt,
    Lt,
    Ge,
    Le,
}

#[allow(dead_code)]
pub struct ConstraintBuilder {
    assertions: Vec<BoolExpr>,
}

#[allow(dead_code)]
impl ConstraintBuilder {
    // Initialize a new builder
    pub fn new() -> Self {
        ConstraintBuilder {
            assertions: Vec::new(),
        }
    }

    // Build a relation expression for the main stack
    pub fn build_stack_rel(&self, index: usize, expr: ValueExpr, rel: RelOp) -> BoolExpr {
        let stack_expr = ValueExpr::RefStack(index);
        self.build_rel(stack_expr, expr, rel)
    }

    // Build a relation expression for the alternate stack
    pub fn build_alt_stack_rel(&self, index: usize, expr: ValueExpr, rel: RelOp) -> BoolExpr {
        let alt_stack_expr = ValueExpr::RefAltStack(index);
        self.build_rel(alt_stack_expr, expr, rel)
    }

    // Build a relation expression for a symbolic variable
    pub fn build_symbol_var_rel(&self, index: usize, expr: ValueExpr, rel: RelOp) -> BoolExpr {
        let symbol_var_expr = ValueExpr::RefSymbolVar(index);
        self.build_rel(symbol_var_expr, expr, rel)
    }

    pub fn build_mul_expr(&self, expr: ValueExpr, expr1: ValueExpr) -> ValueExpr {
        ValueExpr::Mul(Box::new(expr), Box::new(expr1))
    }

    pub fn build_add_expr(&self, expr: ValueExpr, expr1: ValueExpr) -> ValueExpr {
        ValueExpr::Add(Box::new(expr), Box::new(expr1))
    }

    pub fn build_sub_expr(&self, expr: ValueExpr, expr1: ValueExpr) -> ValueExpr {
        ValueExpr::Sub(Box::new(expr), Box::new(expr1))
    }

    pub fn build_if_expr(&self, cond: BoolExpr, expr: ValueExpr, expr1: ValueExpr) -> ValueExpr {
        ValueExpr::IfElse(Box::new(cond), Box::new(expr), Box::new(expr1))
    }
    pub fn build_check_top(&mut self) {
        let expr: BoolExpr = self.build_stack_rel(0, self.build_constant(1), RelOp::Eq);
        self.build_assertion(expr);
    }

    pub fn build_stack_symbolic_limb_eq(&mut self, sid: usize, sym_id: usize, n_limbs: u32) {
        let size: usize = n_limbs as usize;
        for i in sid..sid + size {
            let assertion =
                self.build_stack_rel(i, self.build_symbolic_limb(sym_id, i - sid), RelOp::Eq);
            self.build_assertion(assertion);
        }
    }

    pub fn build_alt_symbolic_limb_eq(&mut self, sid: usize, sym_id: usize, n_limbs: u32) {
        let size: usize = n_limbs as usize;
        for i in sid..sid + size {
            let assertion =
                self.build_alt_stack_rel(i, self.build_symbolic_limb(sym_id, i - sid), RelOp::Eq);
            self.build_assertion(assertion);
        }
    }

    pub fn build_if_symbol_cond_top<F>(&self, symbol_index: usize, expr_closure: F) -> BoolExpr
    where
        F: FnOnce(ValueExpr) -> BoolExpr,
    {
        let symbol_var = expr_closure(ValueExpr::RefSymbolVar(symbol_index));

        let if_else_expr = ValueExpr::IfElse(
            Box::new(symbol_var),
            Box::new(ValueExpr::Constant(1)),
            Box::new(ValueExpr::Constant(0)),
        );

        self.build_stack_rel(0, if_else_expr, RelOp::Eq)
    }

    fn build_rel(&self, lhs: ValueExpr, rhs: ValueExpr, rel: RelOp) -> BoolExpr {
        match rel {
            RelOp::Eq => BoolExpr::Eq(Box::new(lhs), Box::new(rhs)),
            RelOp::Neq => BoolExpr::Neq(Box::new(lhs), Box::new(rhs)),
            RelOp::Gt => BoolExpr::Gt(Box::new(lhs), Box::new(rhs)),
            RelOp::Lt => BoolExpr::Lt(Box::new(lhs), Box::new(rhs)),
            RelOp::Ge => BoolExpr::Ge(Box::new(lhs), Box::new(rhs)),
            RelOp::Le => BoolExpr::Le(Box::new(lhs), Box::new(rhs)),
        }
    }

    // Build a constant ValueExpr
    pub fn build_constant(&self, value: u128) -> ValueExpr { ValueExpr::Constant(value) }

    pub fn build_symbolic(&self, index: usize) -> ValueExpr { ValueExpr::RefSymbolVar(index) }

    pub fn build_symbolic_limb(&self, sym_index: usize, limb_index: usize) -> ValueExpr {
        ValueExpr::RefSymbolLimb(sym_index, limb_index)
    }
    pub fn build_assertion(&mut self, expr: BoolExpr) { self.assertions.push(expr); }

    // Get the total number of assertions
    pub fn get_assertions_len(&self) -> usize { self.assertions.len() }

    // Export the i-th assertion as MetaType::Assertion
    pub fn get_ith_assertion(&self, index: usize) -> Option<MetaType> {
        if index < self.assertions.len() {
            Some(MetaType::Assertion(index, self.assertions[index].clone()))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::bigint::U254;
    // use crate::pseudo::NMUL;
    use bitcoin_script::builder::Block;
    use bitcoin_script::Script;
    use bitcoin_script::*;
    use std::fs::File;

    static mut BS_FILE_PATH: Option<String> = None;
    fn writein_bs_meta(input: String) {
        unsafe {
            if let Some(ref path) = BS_FILE_PATH {
                let path = Path::new(path);
                if let Some(parent) = path.parent() {
                    fs::create_dir_all(parent).expect("Failed to create directories");
                }
                let mut file = OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(path)
                    .expect("Failed to open file");
                writeln!(file, "{}", input).expect("Failed to write to file");
            }
        }
    }

    fn expand_script(script: &Script) {
        for block in &script.blocks {
            match block {
                Block::Call(id) => {
                    let called_script = script
                        .script_map
                        .get(id)
                        .expect("Missing entry for a called script");
                    expand_script(called_script);
                }
                Block::Script(s) => {
                    let multi_line_str = format!("{:#?}", s);
                    // println!("{:?}", multi_line_str);
                    writein_bs_meta(multi_line_str);
                }
            }
        }
    }

    fn post_process() {
        unsafe {
            let bs_path = BS_FILE_PATH.as_ref().expect("BS_FILE_PATH is not set");
            let verified_path = VERIFED_FILE_PATH
                .as_ref()
                .expect("VERIFED_FILE_PATH is not set");

            // Read the BS file content
            let bs_content = fs::read_to_string(bs_path).expect("Failed to read BS file");

            // Initialize variables to store processed lines and count OP_SUBSTR
            let mut processed_bs_lines = Vec::new();
            let mut op_substr_count = 0;

            // Process each line in the BS file
            for line in bs_content.lines() {
                if line.starts_with("Script(") && line.ends_with(")") {
                    // Extract the content inside `Script(...)`
                    let inner = &line["Script(".len()..line.len() - 1];
                    processed_bs_lines.push(inner.to_string());
                } else {
                    processed_bs_lines.push(line.to_string());
                }
                // Count occurrences of `OP_SUBSTR` in the line
                op_substr_count += line.matches("OP_SUBSTR").count();
            }

            // Read the verified file content
            let verified_content = fs::read_to_string(verified_path).unwrap();
            let verified_lines: Vec<String> =
                verified_content.lines().map(|s| s.to_string()).collect();

            if verified_lines.len() != op_substr_count {
                panic!(
                    "Number of verified lines ({}) does not match number of OP_SUBSTR occurrences ({})",
                    verified_lines.len(),
                    op_substr_count
                );
            }

            let mut verified_iter = verified_lines.into_iter();
            let mut final_bs_content = String::new();
            // println!("{:?}", verified_iter.len());
            for line in processed_bs_lines {
                let mut replaced_line = line.clone();
                while replaced_line.find("OP_SUBSTR") != None {
                    replaced_line =
                        replaced_line.replace("OP_SUBSTR", &verified_iter.next().unwrap());
                }
                final_bs_content.push_str(&replaced_line);
                final_bs_content.push('\n');
            }

            fs::write(bs_path, final_bs_content).ok();
            fs::remove_file(verified_path).ok();
        }
    }
    fn pre_process(path: &str) {
        set_filepath(path);
        unsafe {
            let bs_path = BS_FILE_PATH.as_ref().expect("BS_FILE_PATH is not set");
            let verified_path = VERIFED_FILE_PATH
                .as_ref()
                .expect("VERIFED_FILE_PATH is not set");
            File::create(bs_path).ok();
            File::create(verified_path).ok();
        }
    }
    fn dump_script(script: &Script) {
        expand_script(&script);
        post_process();
    }

    fn set_filepath(relative_path: &str) {
        let target_path = Path::new(file!()).parent().unwrap().join(relative_path);
        let target_path_str = target_path.to_str().unwrap();
        unsafe {
            BS_FILE_PATH = Some(target_path_str.to_string());
            VERIFED_FILE_PATH = Some(target_path_str.replace(".bs", ".in").to_string());
        }
        // println!("Set file path to: {}", get_bs_filepath());
    }

    fn add_assertions(builder: &ConstraintBuilder) -> Script {
        script! {
            for i in 0..builder.get_assertions_len() {
                {U254::push_verification_meta(builder.get_ith_assertion(i).unwrap()) }
            }
        }
    }

    #[test]
    fn test_script() {
        pre_process("../data/test.bs");
        // let mut builder = ConstraintBuilder::new();
        // let assertion = builder.build_if_symbol_cond_top(0, |expr| {
        //     builder.build_rel(expr, builder.build_constant(0), RelOp::Eq)
        // });
        // builder.build_assertion(assertion);
        let script = script! {
            // { U254::push_verification_meta(MetaType::SymbolicVar(0)) }
            { U254::add_ref_stack() }
            // { add_assertions(&builder) }
        };
        dump_script(&script);
    }

    #[test]
    fn check_is_zero() {
        pre_process("../data/std/is_zero.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_constant(0), RelOp::Eq)
        });
        builder.build_assertion(assertion);
        let script = script! {
            { U254::push_verification_meta(MetaType::SymbolicVar(0)) }
            { U254::is_zero(0) }
            { add_assertions(&builder) }
        };
        dump_script(&script);
    }

    #[test]
    fn check_is_zero_keep_element() {
        pre_process("../data/std/is_zero_keep_element.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_constant(0), RelOp::Eq)
        });
        builder.build_assertion(assertion);
        for i in 1..U254::N_LIMBS + 1 {
            let index = i as usize;
            let assertion = builder.build_stack_rel(
                index,
                builder.build_symbolic_limb(0, index - 1),
                RelOp::Eq,
            );
            builder.build_assertion(assertion);
        }
        let script = script! {
            { U254::push_verification_meta(MetaType::SymbolicVar(0)) }
            { U254::is_zero_keep_element(0) }
            { add_assertions(&builder) }
        };
        dump_script(&script);
    }

    #[test]
    fn check_is_one() {
        pre_process("../data/std/is_one.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_constant(1), RelOp::Eq)
        });
        builder.build_assertion(assertion);
        let script = script! {
            { U254::push_verification_meta(MetaType::SymbolicVar(0)) }
            { U254::is_one(0) }
            { add_assertions(&builder) }
        };
        dump_script(&script);
    }

    #[test]
    fn check_is_one_keep_element() {
        pre_process("../data/std/is_one_keep_element.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_constant(1), RelOp::Eq)
        });
        builder.build_assertion(assertion);
        for i in 1..U254::N_LIMBS + 1 {
            let index = i as usize;
            let assertion = builder.build_stack_rel(
                index,
                builder.build_symbolic_limb(0, index - 1),
                RelOp::Eq,
            );
            builder.build_assertion(assertion);
        }
        let script = script! {
            { U254::push_verification_meta(MetaType::SymbolicVar(0)) }
            { U254::is_one_keep_element(0) }
            { add_assertions(&builder) }
        };
        dump_script(&script);
    }

    #[test]
    fn check_push_one() {
        pre_process("../data/push_one.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_stack_rel(0, builder.build_constant(1), RelOp::Eq);
        builder.build_assertion(assertion);
        let script = script! {
            { U254::push_one() }
            { add_assertions(&builder) }
        };
        dump_script(&script);
    }

    #[test]
    fn check_push_zero() {
        pre_process("../data/push_zero.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_stack_rel(0, builder.build_constant(0), RelOp::Eq);
        builder.build_assertion(assertion);
        let script = script! {
            {U254::push_zero()}
            { add_assertions(&builder) }
        };
        dump_script(&script);
    }

    #[test]
    fn check_drop() {
        pre_process("../data/std/drop.bs");
        let mut builder: ConstraintBuilder = ConstraintBuilder::new();
        builder.build_stack_symbolic_limb_eq(0, 0, U254::N_LIMBS);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::drop()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_toaltstack() {
        pre_process("../data/std/toaltstack.bs");
        let mut builder = ConstraintBuilder::new();
        for i in 0..U254::N_LIMBS {
            let index = i as usize;
            let assertion = builder.build_alt_stack_rel(
                index,
                builder.build_symbolic_limb(0, U254::N_LIMBS as usize - index - 1),
                RelOp::Eq,
            );
            builder.build_assertion(assertion);
        }

        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::toaltstack()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_fromaltstack() {
        pre_process("../data/std/fromaltstack.bs");
        let mut builder: ConstraintBuilder = ConstraintBuilder::new();
        builder.build_stack_symbolic_limb_eq(0, 0, U254::N_LIMBS);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::toaltstack()}
            {U254::fromaltstack()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_is_negative() {
        pre_process("../data/std/is_negative.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_constant(0), RelOp::Lt)
        });
        builder.build_assertion(assertion);

        let depth = 0;
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0)) }
            {U254::is_negative(depth)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_is_positive() {
        pre_process("../data/std/is_positive.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_constant(0), RelOp::Gt)
        });
        builder.build_assertion(assertion);
        let depth = 0;
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0)) }
            {U254::is_positive(depth)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_zip() {
        pre_process("../data/std/zip.bs");
        let mut builder = ConstraintBuilder::new();
        for i in 0..U254::N_LIMBS * 2 {
            let index = i as usize;
            let assertion = builder.build_stack_rel(
                index,
                builder.build_symbolic_limb(1 - index % 2, index / 2),
                RelOp::Eq,
            );
            builder.build_assertion(assertion);
        }
        let a = 1;
        let b = 0;
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::zip(a, b)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_copy_zip() {
        pre_process("../data/std/copy_zip.bs");
        let a = 1;
        let b = 0;
        let mut builder = ConstraintBuilder::new();
        for i in 0..U254::N_LIMBS * 2 {
            let index = i as usize;
            let assertion = builder.build_stack_rel(
                index,
                builder.build_symbolic_limb(
                    (1 - index % 2) * a.clone() + (index % 2) * b.clone(),
                    index / 2,
                ),
                RelOp::Eq,
            );
            builder.build_assertion(assertion);
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::copy_zip(a as u32, b as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_dup_zip() {
        pre_process("../data/std/dup_zip.bs");
        let a = 0;
        let mut builder = ConstraintBuilder::new();
        for i in 0..U254::N_LIMBS * 2 {
            let index = i as usize;
            let assertion = builder.build_stack_rel(
                index,
                builder.build_symbolic_limb(a.clone(), index / 2),
                RelOp::Eq,
            );
            builder.build_assertion(assertion);
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::dup_zip(a as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_copy() {
        pre_process("../data/std/copy.bs");
        let a = 1;
        let mut builder = ConstraintBuilder::new();
        let mut sid = 0;
        builder.build_stack_symbolic_limb_eq(sid, 0, U254::N_LIMBS);
        sid += U254::N_LIMBS as usize;
        builder.build_stack_symbolic_limb_eq(sid, 1, U254::N_LIMBS);
        sid += U254::N_LIMBS as usize;
        builder.build_stack_symbolic_limb_eq(sid, 0, U254::N_LIMBS);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::copy(a as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_copy_deep() {
        pre_process("../data/std/copy_deep.bs");
        let a = 16;
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_stack_rel(0, builder.build_symbolic(0), RelOp::Eq);
        builder.build_assertion(assertion);
        for i in 1..=a {
            let assertion = builder.build_stack_rel(i, builder.build_symbolic(a - i), RelOp::Eq);
            builder.build_assertion(assertion);
        }
        let script = script! {
            for i in 0..a {
                {U254::push_verification_meta(MetaType::SymbolicVar(i))}
            }
            {U254::copy(a as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_roll() {
        pre_process("../data/std/roll.bs");
        let a = 1;
        let mut builder = ConstraintBuilder::new();
        builder.build_stack_symbolic_limb_eq(0, 0, U254::N_LIMBS);
        builder.build_stack_symbolic_limb_eq(U254::N_LIMBS as usize, 1, U254::N_LIMBS);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::roll(a as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_resize_cut() {
        pre_process("../data/std/resize_1.bs");
        let mut builder = ConstraintBuilder::new();
        const T_BITS: u32 = 145;
        const LIMB_SIZE: u32 = 29;
        for i in 0..(T_BITS + LIMB_SIZE - 1) / LIMB_SIZE {
            let index = i as usize;
            let assertion =
                builder.build_stack_rel(index, builder.build_symbolic_limb(0, index), RelOp::Eq);
            builder.build_assertion(assertion);
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::resize::<T_BITS>()} // 145 = 29 * 5
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_resize_enlarge() {
        pre_process("../data/std/resize_2.bs");
        let mut builder = ConstraintBuilder::new();
        const T_BITS: u32 = 348;
        const LIMB_SIZE: u32 = 29;
        for i in 0..U254::N_LIMBS {
            let index = i as usize;
            let assertion =
                builder.build_stack_rel(index, builder.build_symbolic_limb(0, index), RelOp::Eq);
            builder.build_assertion(assertion);
        }
        for i in U254::N_LIMBS..(T_BITS + LIMB_SIZE - 1) / LIMB_SIZE {
            let index = i as usize;
            let assertion = builder.build_stack_rel(index, builder.build_constant(0), RelOp::Eq);
            builder.build_assertion(assertion);
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::resize::<T_BITS>()} // 348 = 29 * 12
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_equalverify() {
        pre_process("../data/equalverify.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_symbolic(1), RelOp::Eq)
        });
        builder.build_assertion(assertion);
        let a = 1;
        let b = 0;
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::equalverify(a, b)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_equal() {
        pre_process("../data/equal.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_symbolic(1), RelOp::Eq)
        });
        builder.build_assertion(assertion);
        let a = 1;
        let b = 0;
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::equal(a, b)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_notequal() {
        pre_process("../data/notequal.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_symbolic(1), RelOp::Neq)
        });
        builder.build_assertion(assertion);
        let a = 1;
        let b = 0;
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::notequal(a, b)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_lessthanorequal() {
        pre_process("../data/lessthanorequal.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_symbolic(1), RelOp::Le)
        });
        builder.build_assertion(assertion);
        let a = 1;
        let b = 0;
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::lessthanorequal(a, b)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_greaterthan() {
        pre_process("../data/greaterthan.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(1, |expr| {
            builder.build_rel(expr, builder.build_symbolic(0), RelOp::Lt)
        });
        builder.build_assertion(assertion);
        let a = 1;
        let b = 0;
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::greaterthan(a, b)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_greaterthanorequal() {
        pre_process("../data/greaterthanorequal.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(1, |expr| {
            builder.build_rel(expr, builder.build_symbolic(0), RelOp::Le)
        });
        builder.build_assertion(assertion);
        let a = 1;
        let b = 0;
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::greaterthanorequal(a, b)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_lessthan() {
        pre_process("../data/lessthan.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_symbolic(1), RelOp::Lt)
        });
        builder.build_assertion(assertion);
        let a = 1;
        let b = 0;
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::lessthan(a, b)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_double() {
        pre_process("../data/add/double.bs");
        let mut builder = ConstraintBuilder::new();
        let mut carry = ValueExpr::Constant(0);
        let mut limb_size: u32 = 29;
        for i in 0..U254::N_LIMBS {
            if i + 1 == U254::N_LIMBS {
                limb_size = 22;
            }
            let index = i as usize;
            let limb = builder.build_symbolic_limb(0, index);
            let value = builder.build_add_expr(builder.build_add_expr(limb.clone(), limb), carry);
            let assertion = builder.build_stack_rel(
                index,
                builder.build_sub_expr(
                    value.clone(),
                    builder.build_if_expr(
                        builder.build_rel(
                            value.clone(),
                            builder.build_constant(1 << limb_size),
                            RelOp::Gt,
                        ),
                        builder.build_constant(1 << limb_size),
                        builder.build_constant(0),
                    ),
                ),
                RelOp::Eq,
            );
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Gt),
                builder.build_constant(1),
                builder.build_constant(0),
            );
            builder.build_assertion(assertion);
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::double(0)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_add() {
        pre_process("../data/add/add.bs");
        let mut builder = ConstraintBuilder::new();
        let mut carry = ValueExpr::Constant(0);
        let mut limb_size: u32 = 29;
        for i in 0..U254::N_LIMBS {
            if i + 1 == U254::N_LIMBS {
                limb_size = 22;
            }
            let index = i as usize;
            let limba = builder.build_symbolic_limb(0, index);
            let limbb = builder.build_symbolic_limb(1, index);
            let value = builder.build_add_expr(builder.build_add_expr(limba, limbb), carry);
            let assertion = builder.build_stack_rel(
                index,
                builder.build_sub_expr(
                    value.clone(),
                    builder.build_if_expr(
                        builder.build_rel(
                            value.clone(),
                            builder.build_constant(1 << limb_size),
                            RelOp::Gt,
                        ),
                        builder.build_constant(1 << limb_size),
                        builder.build_constant(0),
                    ),
                ),
                RelOp::Eq,
            );
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Gt),
                builder.build_constant(1),
                builder.build_constant(0),
            );
            builder.build_assertion(assertion);
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::add(1,0)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_add1() {
        pre_process("../data/add/add1.bs");
        let mut builder = ConstraintBuilder::new();
        let mut carry = ValueExpr::Constant(0);
        let mut limb_size: u32 = 29;
        for i in 0..U254::N_LIMBS {
            if i + 1 == U254::N_LIMBS {
                limb_size = 22;
            }
            let index = i as usize;
            let limba = builder.build_symbolic_limb(0, index);
            let limbb = if i == 0 {
                builder.build_constant(1)
            } else {
                builder.build_constant(0)
            };
            let value = builder.build_add_expr(builder.build_add_expr(limba, limbb), carry);
            let assertion = builder.build_stack_rel(
                index,
                builder.build_sub_expr(
                    value.clone(),
                    builder.build_if_expr(
                        builder.build_rel(
                            value.clone(),
                            builder.build_constant(1 << limb_size),
                            RelOp::Gt,
                        ),
                        builder.build_constant(1 << limb_size),
                        builder.build_constant(0),
                    ),
                ),
                RelOp::Eq,
            );
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Gt),
                builder.build_constant(1),
                builder.build_constant(0),
            );
            builder.build_assertion(assertion);
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::add1()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_double_allow_overflow() {
        pre_process("../data/add/double_allow_overflow.bs");
        let mut builder = ConstraintBuilder::new();
        let mut carry = ValueExpr::Constant(0);
        let mut limb_size: u32 = 29;
        for i in 0..U254::N_LIMBS {
            if i + 1 == U254::N_LIMBS {
                limb_size = 22;
            }
            let index = i as usize;
            let limb = builder.build_symbolic_limb(0, index);
            let value = builder.build_add_expr(builder.build_add_expr(limb.clone(), limb), carry);
            let assertion = builder.build_stack_rel(
                index,
                builder.build_sub_expr(
                    value.clone(),
                    builder.build_if_expr(
                        builder.build_rel(
                            value.clone(),
                            builder.build_constant(1 << limb_size),
                            RelOp::Gt,
                        ),
                        builder.build_constant(1 << limb_size),
                        builder.build_constant(0),
                    ),
                ),
                RelOp::Eq,
            );
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Gt),
                builder.build_constant(1),
                builder.build_constant(0),
            );
            builder.build_assertion(assertion);
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::double_allow_overflow()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_double_allow_overflow_keep_element() {
        pre_process("../data/add/double_allow_overflow_keep_element.bs");
        let mut builder = ConstraintBuilder::new();
        let mut carry = ValueExpr::Constant(0);
        let mut limb_size: u32 = 29;
        for i in 0..U254::N_LIMBS {
            if i + 1 == U254::N_LIMBS {
                limb_size = 22;
            }
            let index = i as usize;
            let limb = builder.build_symbolic_limb(0, index);
            let value = builder.build_add_expr(builder.build_add_expr(limb.clone(), limb), carry);
            let assertion = builder.build_stack_rel(
                index,
                builder.build_sub_expr(
                    value.clone(),
                    builder.build_if_expr(
                        builder.build_rel(
                            value.clone(),
                            builder.build_constant(1 << limb_size),
                            RelOp::Gt,
                        ),
                        builder.build_constant(1 << limb_size),
                        builder.build_constant(0),
                    ),
                ),
                RelOp::Eq,
            );
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Gt),
                builder.build_constant(1),
                builder.build_constant(0),
            );
            builder.build_assertion(assertion);
        }
        builder.build_stack_symbolic_limb_eq(U254::N_LIMBS as usize, 0, U254::N_LIMBS);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::double_allow_overflow_keep_element(0)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_double_prevent_overflow() {
        pre_process("../data/add/double_prevent_overflow.bs");
        let mut builder = ConstraintBuilder::new();
        let mut carry = ValueExpr::Constant(0);
        let mut limb_size: u32 = 29;
        for i in 0..U254::N_LIMBS {
            if i + 1 == U254::N_LIMBS {
                limb_size = 22;
            }
            let index = i as usize;
            let limb = builder.build_symbolic_limb(0, index);
            let value =
                builder.build_add_expr(builder.build_add_expr(limb.clone(), limb.clone()), carry);
            let value_nlo = builder.build_sub_expr(
                value.clone(),
                builder.build_if_expr(
                    builder.build_rel(
                        value.clone(),
                        builder.build_constant(1 << limb_size),
                        RelOp::Gt,
                    ),
                    builder.build_constant(1 << limb_size),
                    builder.build_constant(0),
                ),
            );
            let assertion = builder.build_stack_rel(index, value_nlo.clone(), RelOp::Eq);
            builder.build_assertion(assertion);
            if i + 1 == U254::N_LIMBS {
                builder.build_assertion(builder.build_rel(
                    builder.build_if_expr(
                        builder.build_rel(builder.build_constant(1 << 21), value_nlo, RelOp::Lt),
                        builder.build_constant(1),
                        builder.build_constant(0),
                    ),
                    builder.build_if_expr(
                        builder.build_rel(limb, builder.build_constant(1 << 21), RelOp::Lt),
                        builder.build_constant(1),
                        builder.build_constant(0),
                    ),
                    RelOp::Eq,
                ));
            }
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Gt),
                builder.build_constant(1),
                builder.build_constant(0),
            );
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::double_prevent_overflow()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_add_ref_with_top() {
        pre_process("../data/add/add_ref_with_top.bs");
        let mut builder = ConstraintBuilder::new();
        let mut carry = ValueExpr::Constant(0);
        let mut limb_size: u32 = 29;
        let mut sid = U254::N_LIMBS;
        for i in 0..sid {
            if i + 1 == U254::N_LIMBS {
                limb_size = 22;
            }
            let index = i as usize;
            let limba = builder.build_symbolic_limb(0, index);
            let limbb = builder.build_symbolic_limb(1, index);
            let value =
                builder.build_add_expr(builder.build_add_expr(limba.clone(), limbb.clone()), carry);
            let value_nlo = builder.build_sub_expr(
                value.clone(),
                builder.build_if_expr(
                    builder.build_rel(
                        value.clone(),
                        builder.build_constant(1 << limb_size),
                        RelOp::Gt,
                    ),
                    builder.build_constant(1 << limb_size),
                    builder.build_constant(0),
                ),
            );
            let assertion = builder.build_stack_rel(index, value_nlo.clone(), RelOp::Eq);
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Gt),
                builder.build_constant(1),
                builder.build_constant(0),
            );
            builder.build_assertion(assertion);
            if i + 1 == U254::N_LIMBS {
                let sign_a = builder.build_if_expr(
                    builder.build_rel(builder.build_constant(1 << 21), limba, RelOp::Ge),
                    builder.build_constant(1),
                    builder.build_constant(0),
                );
                let sign_b = builder.build_if_expr(
                    builder.build_rel(limbb, builder.build_constant(1 << 21), RelOp::Lt),
                    builder.build_constant(1),
                    builder.build_constant(0),
                );
                let sign_i = builder.build_if_expr(
                    builder.build_rel(value_nlo, builder.build_constant(1 << 21), RelOp::Ge),
                    builder.build_constant(1),
                    builder.build_constant(0),
                );
                let sum = builder.build_add_expr(sign_a, builder.build_add_expr(sign_b, sign_i));
                builder.build_assertion(builder.build_rel(
                    sum.clone(),
                    builder.build_constant(1),
                    RelOp::Ge,
                ));
                builder.build_assertion(builder.build_rel(
                    sum,
                    builder.build_constant(2),
                    RelOp::Le,
                ));
            }
        }
        builder.build_stack_symbolic_limb_eq(sid as usize, 1, U254::N_LIMBS);
        sid += U254::N_LIMBS;
        builder.build_stack_symbolic_limb_eq(sid as usize, 0, U254::N_LIMBS);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::add_ref_with_top(1)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_add_ref() {
        pre_process("../data/add/add_ref.bs");
        let mut builder = ConstraintBuilder::new();
        let mut carry = ValueExpr::Constant(0);
        let mut limb_size: u32 = 29;
        let sid = U254::N_LIMBS;
        for i in 0..sid {
            if i + 1 == U254::N_LIMBS {
                limb_size = 22;
            }
            let index = i as usize;
            let limba = builder.build_symbolic_limb(0, index);
            let limbb = builder.build_symbolic_limb(1, index);
            let value =
                builder.build_add_expr(builder.build_add_expr(limba.clone(), limbb.clone()), carry);
            let value_nlo = builder.build_sub_expr(
                value.clone(),
                builder.build_if_expr(
                    builder.build_rel(
                        value.clone(),
                        builder.build_constant(1 << limb_size),
                        RelOp::Gt,
                    ),
                    builder.build_constant(1 << limb_size),
                    builder.build_constant(0),
                ),
            );
            let assertion = builder.build_stack_rel(index, value_nlo.clone(), RelOp::Eq);
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Gt),
                builder.build_constant(1),
                builder.build_constant(0),
            );
            builder.build_assertion(assertion);
            if i + 1 == U254::N_LIMBS {
                let sign_a = builder.build_if_expr(
                    builder.build_rel(builder.build_constant(1 << 21), limba, RelOp::Ge),
                    builder.build_constant(1),
                    builder.build_constant(0),
                );
                let sign_b = builder.build_if_expr(
                    builder.build_rel(limbb, builder.build_constant(1 << 21), RelOp::Lt),
                    builder.build_constant(1),
                    builder.build_constant(0),
                );
                let sign_i = builder.build_if_expr(
                    builder.build_rel(value_nlo, builder.build_constant(1 << 21), RelOp::Ge),
                    builder.build_constant(1),
                    builder.build_constant(0),
                );
                let sum = builder.build_add_expr(sign_a, builder.build_add_expr(sign_b, sign_i));
                builder.build_assertion(builder.build_rel(
                    sum.clone(),
                    builder.build_constant(1),
                    RelOp::Ge,
                ));
                builder.build_assertion(builder.build_rel(
                    sum,
                    builder.build_constant(2),
                    RelOp::Le,
                ));
            }
        }
        builder.build_stack_symbolic_limb_eq(sid as usize, 0, U254::N_LIMBS);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::add_ref(1)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_add_ref_stack() {
        pre_process("../data/add/add_ref_stack.bs");
        let mut builder = ConstraintBuilder::new();
        let mut carry = ValueExpr::Constant(0);
        let depth: u32 = 4; // depth > 0
        let mut limb_size: u32 = 29;
        let mut sid = U254::N_LIMBS;
        for i in 0..sid {
            if i + 1 == U254::N_LIMBS {
                limb_size = 22;
            }
            let index = i as usize;
            let limba = builder.build_symbolic_limb(0, index);
            let limbb = builder.build_symbolic_limb(depth as usize, index);
            let value =
                builder.build_add_expr(builder.build_add_expr(limba.clone(), limbb.clone()), carry);
            let value_nlo = builder.build_sub_expr(
                value.clone(),
                builder.build_if_expr(
                    builder.build_rel(
                        value.clone(),
                        builder.build_constant(1 << limb_size),
                        RelOp::Gt,
                    ),
                    builder.build_constant(1 << limb_size),
                    builder.build_constant(0),
                ),
            );
            let assertion = builder.build_stack_rel(index, value_nlo.clone(), RelOp::Eq);
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Gt),
                builder.build_constant(1),
                builder.build_constant(0),
            );
            builder.build_assertion(assertion);
            if i + 1 == U254::N_LIMBS {
                let sign_a = builder.build_if_expr(
                    builder.build_rel(builder.build_constant(1 << 21), limba, RelOp::Ge),
                    builder.build_constant(1),
                    builder.build_constant(0),
                );
                let sign_b = builder.build_if_expr(
                    builder.build_rel(limbb, builder.build_constant(1 << 21), RelOp::Lt),
                    builder.build_constant(1),
                    builder.build_constant(0),
                );
                let sign_i = builder.build_if_expr(
                    builder.build_rel(value_nlo, builder.build_constant(1 << 21), RelOp::Ge),
                    builder.build_constant(1),
                    builder.build_constant(0),
                );
                let sum = builder.build_add_expr(sign_a, builder.build_add_expr(sign_b, sign_i));
                builder.build_assertion(builder.build_rel(
                    sum.clone(),
                    builder.build_constant(1),
                    RelOp::Ge,
                ));
                builder.build_assertion(builder.build_rel(
                    sum,
                    builder.build_constant(2),
                    RelOp::Le,
                ));
            }
        }
        for id in 1..=depth {
            builder.build_stack_symbolic_limb_eq(sid as usize, id as usize, U254::N_LIMBS);
            sid += U254::N_LIMBS;
        }

        let script = script! {
            {depth}
            for id in (0..=depth).rev(){
                {U254::push_verification_meta(MetaType::SymbolicVar(id as usize))}
            }
            {U254::add_ref_stack()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }
}
