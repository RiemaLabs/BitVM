use std::fs;

use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;

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
            ValueExpr::RefStack(i) => format!("stack[{}]", i),
            ValueExpr::RefAltStack(i) => format!("alt[{}]", i),
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

    pub fn build_check_top(&mut self) {
        let expr: BoolExpr = self.build_stack_rel(0, self.build_constant(1), RelOp::Eq);
        self.build_assertion(expr);
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
    use crate::bigint::{U254, U64};
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
    fn check_is_zero() {
        pre_process("../data/is_zero.bs");
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
        pre_process("../data/drop.bs");
        // TODO : Extends Spec to support a representation of drop one symbolic variable?
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_stack_rel(0, builder.build_symbolic(0), RelOp::Eq);
        builder.build_assertion(assertion);
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
        pre_process("../data/toaltstack.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_alt_stack_rel(0, builder.build_symbolic(0), RelOp::Eq);
        builder.build_assertion(assertion);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::toaltstack()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_fromaltstack() {
        pre_process("../data/fromaltstack.bs");
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))} // TODO : push to alt stack
            {U254::fromaltstack()}
            // TODO : Add Assertion for the symbolic variable is moved to alt stack.
        };
        dump_script(&script);
    }

    #[test]
    fn check_is_negative() {
        pre_process("../data/is_negative.bs");
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
        pre_process("../data/is_positive.bs");
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
        pre_process("../data/zip.bs");
        let a = 1;
        let b = 0;
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::zip(a, b)}
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
}
