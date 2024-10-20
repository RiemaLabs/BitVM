// use std::fmt::format;
use std::fs;

use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;

use bitcoin_script::Script;
use serde_json::Value;

use crate::bigint::U254;
use crate::hash::blake3::S;

// use serde_json::Value;

const U254_POWERS: [&str; 9] = [
    "1",
    "536870912",
    "288230376151711744",
    "154742504910672534362390528",
    "83076749736557242056487941267521536",
    "44601490397061246283071436545296723011960832",
    "23945242826029513411849172299223580994042798784118784",
    "12855504354071922204335696738729300820177623950262342682411008",
    "6901746346790563787434755862277025452451108972170386555162524223799296",
];

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
    Assumption(usize, BoolExpr),
}

#[derive(Clone)]
pub enum ValueExpr {
    RefSymbolVar(usize),
    RefSymbolLimb(usize, usize),
    RefStack(usize),    // offset in main stack
    RefAltStack(usize), // offset in alt stack
    Constant(u128),     // TODO: Constants within 2^254
    BigConstant(String),
    Add(Box<ValueExpr>, Box<ValueExpr>),
    Sub(Box<ValueExpr>, Box<ValueExpr>),
    Mul(Box<ValueExpr>, Box<ValueExpr>),
    Div(Box<ValueExpr>, Box<ValueExpr>),
    Mod(Box<ValueExpr>, Box<ValueExpr>),
    LShift(Box<ValueExpr>, Box<ValueExpr>),
    RShift(Box<ValueExpr>, Box<ValueExpr>),
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
            ValueExpr::BigConstant(string) => string.clone(),
            ValueExpr::Add(lhs, rhs) => format!("({} + {})", lhs.to_string(), rhs.to_string()),
            ValueExpr::Sub(lhs, rhs) => format!("({} - {})", lhs.to_string(), rhs.to_string()),
            ValueExpr::Mul(lhs, rhs) => format!("({} * {})", lhs.to_string(), rhs.to_string()),
            ValueExpr::Div(lhs, rhs) => format!("({} / {})", lhs.to_string(), rhs.to_string()),
            ValueExpr::Mod(lhs, rhs) => format!("({} % {})", lhs.to_string(), rhs.to_string()),
            ValueExpr::LShift(expr, shift) => {
                format!("({} << {})", expr.to_string(), shift.to_string())
            }
            ValueExpr::RShift(expr, shift) => {
                format!("({} >> {})", expr.to_string(), shift.to_string())
            }
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
    assumptions: Vec<BoolExpr>,
}

#[allow(dead_code)]
impl ConstraintBuilder {
    // Initialize a new builder
    pub fn new() -> Self {
        ConstraintBuilder {
            assertions: Vec::new(),
            assumptions: Vec::new(),
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

    pub fn build_mod_expr(&self, expr: ValueExpr, expr1: ValueExpr) -> ValueExpr {
        ValueExpr::Mod(Box::new(expr), Box::new(expr1))
    }

    pub fn build_div_expr(&self, expr: ValueExpr, expr1: ValueExpr) -> ValueExpr {
        ValueExpr::Div(Box::new(expr), Box::new(expr1))
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

    pub fn build_lshift_expr(&self, expr: ValueExpr, expr1: ValueExpr) -> ValueExpr {
        ValueExpr::LShift(Box::new(expr), Box::new(expr1))
    }

    pub fn build_rshift_expr(&self, expr: ValueExpr, expr1: ValueExpr) -> ValueExpr {
        ValueExpr::RShift(Box::new(expr), Box::new(expr1))
    }

    pub fn build_if_expr(&self, cond: BoolExpr, expr: ValueExpr, expr1: ValueExpr) -> ValueExpr {
        ValueExpr::IfElse(Box::new(cond), Box::new(expr), Box::new(expr1))
    }

    pub fn build_and_rel(&self, cond: BoolExpr, cond1: BoolExpr) -> BoolExpr {
        BoolExpr::And(Box::new(cond), Box::new(cond1))
    }

    pub fn build_or_rel(&self, cond: BoolExpr, cond1: BoolExpr) -> BoolExpr {
        BoolExpr::Or(Box::new(cond), Box::new(cond1))
    }
    pub fn build_check_top(&mut self) {
        let expr: BoolExpr = self.build_stack_rel(0, self.build_constant(1), RelOp::Eq);
        self.build_assertion(expr);
    }
    pub fn build_overflow_exp(&self, expr: ValueExpr, limb_size: usize) -> ValueExpr {
        self.build_sub_expr(
            expr.clone(),
            self.build_if_expr(
                self.build_rel(
                    expr.clone(),
                    self.build_constant(1 << limb_size as u128),
                    RelOp::Ge,
                ),
                self.build_lshift_expr(
                    self.build_rshift_expr(expr, self.build_constant(limb_size as u128)),
                    self.build_constant(limb_size as u128),
                ),
                self.build_constant(0),
            ),
        )
    }
    pub fn build_lshift_symbolic_limb(
        &self,
        sym_index: usize,
        bit: u128,
        limb_index: usize,
    ) -> ValueExpr {
        let mut limb_size = 29;
        let ignore_bound = bit as usize / limb_size;
        if limb_index == U254::N_LIMBS as usize - 1 {
            limb_size = 22;
        }
        if limb_index < ignore_bound {
            self.build_constant(0)
        } else {
            let cur_index = limb_index - ignore_bound;
            let shift = bit % 29 as u128;
            if cur_index == 0 {
                if (shift as usize) < limb_size {
                    self.build_overflow_exp(
                        self.build_lshift_expr(
                            self.build_symbolic_limb(sym_index, cur_index),
                            self.build_constant(shift),
                        ),
                        limb_size,
                    )
                } else {
                    self.build_constant(0)
                }
            } else {
                if limb_size == 29 {
                    self.build_add_expr(
                        self.build_overflow_exp(
                            self.build_lshift_expr(
                                self.build_symbolic_limb(sym_index, cur_index),
                                self.build_constant(shift),
                            ),
                            limb_size,
                        ),
                        self.build_rshift_expr(
                            self.build_symbolic_limb(sym_index, cur_index - 1),
                            self.build_constant(29 - shift),
                        ),
                    )
                } else {
                    if (shift as usize) >= limb_size {
                        self.build_overflow_exp(
                            self.build_rshift_expr(
                                self.build_symbolic_limb(sym_index, cur_index - 1),
                                self.build_constant(29 - shift),
                            ),
                            limb_size,
                        )
                    } else {
                        self.build_add_expr(
                            self.build_overflow_exp(
                                self.build_lshift_expr(
                                    self.build_symbolic_limb(sym_index, cur_index),
                                    self.build_constant(shift),
                                ),
                                limb_size,
                            ),
                            self.build_rshift_expr(
                                self.build_symbolic_limb(sym_index, cur_index - 1),
                                self.build_constant(29 - shift),
                            ),
                        )
                    }
                }
            }
        }
    }

    pub fn build_lshift_symbolic_stack_limb(
        &self,
        sid: usize,
        sym_index: usize,
        bit: u128,
        limb_index: usize,
    ) -> BoolExpr {
        self.build_stack_rel(
            sid + limb_index,
            self.build_lshift_symbolic_limb(sym_index, bit, limb_index),
            RelOp::Eq,
        )
    }
    pub fn build_stack_symbolic_limb_eq(&mut self, sid: usize, sym_id: usize, n_limbs: u32) {
        let size: usize = n_limbs as usize;
        for i in sid..sid + size {
            let assertion =
                self.build_stack_rel(i, self.build_symbolic_limb(sym_id, i - sid), RelOp::Eq);
            self.build_assertion(assertion);
        }
    }

    pub fn build_stack_eq_u254_variable(&self, sid: usize) -> ValueExpr {
        let mut expr = self.build_stack(sid);
        for i in 1..9 {
            let cons = U254_POWERS[i].to_string();
            expr = self.build_add_expr(
                expr.clone(),
                self.build_mul_expr(self.build_stack(sid + i), ValueExpr::BigConstant(cons)),
            );
        }
        expr
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

    pub fn build_rel(&self, lhs: ValueExpr, rhs: ValueExpr, rel: RelOp) -> BoolExpr {
        match rel {
            RelOp::Eq => BoolExpr::Eq(Box::new(lhs), Box::new(rhs)),
            RelOp::Neq => BoolExpr::Neq(Box::new(lhs), Box::new(rhs)),
            RelOp::Gt => BoolExpr::Gt(Box::new(lhs), Box::new(rhs)),
            RelOp::Lt => BoolExpr::Lt(Box::new(lhs), Box::new(rhs)),
            RelOp::Ge => BoolExpr::Ge(Box::new(lhs), Box::new(rhs)),
            RelOp::Le => BoolExpr::Le(Box::new(lhs), Box::new(rhs)),
        }
    }

    pub fn build_constant(&self, value: u128) -> ValueExpr { ValueExpr::Constant(value) }

    pub fn build_big_constant(&self, value: String) -> ValueExpr { ValueExpr::BigConstant(value) }

    pub fn build_bn254_mod(&self) -> ValueExpr {
        ValueExpr::BigConstant(
            "21888242871839275222246405745257275088696311157297823662689037894645226208583"
                .to_string(),
        )
    }

    pub fn build_bn254_one_mont(&self) -> ValueExpr {
        ValueExpr::BigConstant(
            "6233810253280740994628949329533561314962923717165850268195284058176919227425"
                .to_string(),
        )
    }

    pub fn build_symbolic(&self, index: usize) -> ValueExpr { ValueExpr::RefSymbolVar(index) }

    pub fn build_bit_of_symbolic(&self, sym_index: usize, bit: u128) -> ValueExpr {
        self.build_sub_expr(
            self.build_symbolic(sym_index),
            self.build_lshift_expr(
                self.build_rshift_expr(self.build_symbolic(sym_index), self.build_constant(bit)),
                self.build_constant(bit),
            ),
        )
    }

    pub fn build_bit_of_symbolic_limb(&self, sym_index: usize, bit: u128) -> ValueExpr {
        let limb_index = bit / 29; // U254 : 29
        let shift = bit % 29;
        if shift == 1 {
            self.build_sub_expr(
                self.build_symbolic_limb(sym_index, limb_index as usize),
                self.build_lshift_expr(
                    self.build_rshift_expr(
                        self.build_symbolic_limb(sym_index, limb_index as usize),
                        self.build_constant(1),
                    ),
                    self.build_constant(1),
                ),
            )
        } else {
            self.build_sub_expr(
                self.build_rshift_expr(
                    self.build_symbolic_limb(sym_index, limb_index as usize),
                    self.build_constant(shift - 1),
                ),
                self.build_lshift_expr(
                    self.build_rshift_expr(
                        self.build_symbolic_limb(sym_index, limb_index as usize),
                        self.build_constant(shift),
                    ),
                    self.build_constant(1),
                ),
            )
        }
    }

    pub fn build_stack(&self, index: usize) -> ValueExpr { ValueExpr::RefStack(index) }

    pub fn build_alt_stack(&self, index: usize) -> ValueExpr { ValueExpr::RefAltStack(index) }

    pub fn build_symbolic_limb(&self, sym_index: usize, limb_index: usize) -> ValueExpr {
        ValueExpr::RefSymbolLimb(sym_index, limb_index)
    }
    pub fn build_assertion(&mut self, expr: BoolExpr) { self.assertions.push(expr); }

    pub fn dump_assertion(&self, expr: BoolExpr, index: &mut usize) -> Script {
        let script = { U254::push_verification_meta(MetaType::Assertion(*index, expr)) };
        *index += 1;
        script
    }

    pub fn build_assumption(&mut self, expr: BoolExpr) { self.assumptions.push(expr); }
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

    pub fn get_assumptions_len(&self) -> usize { self.assumptions.len() }

    // Export the i-th assertion as MetaType::Assertion
    pub fn get_ith_assumption(&self, index: usize) -> Option<MetaType> {
        if index < self.assumptions.len() {
            Some(MetaType::Assumption(index, self.assumptions[index].clone()))
        } else {
            None
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::bigint::U254;
    use crate::bn254::fp254impl::Fp254Impl;
    use crate::bn254::fq::Fq;
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

    fn add_assumptions(builder: &ConstraintBuilder) -> Script {
        script! {
            for i in 0..builder.get_assumptions_len() {
                {U254::push_verification_meta(builder.get_ith_assumption(i).unwrap()) }
            }
        }
    }

    #[test]
    fn test_script() {
        pre_process("../data/bigint/test.bs");
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
        pre_process("../data/bigint/std/is_zero.bs");
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
        pre_process("../data/bigint/std/is_zero_keep_element.bs");
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
    fn check_bn254_is_zero_keep_element() {
        pre_process("../data/bn254/fp254impl/is_zero_keep_element.bs");
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
            { Fq::is_zero_keep_element(0) }
            { add_assertions(&builder) }
        };
        dump_script(&script);
    }

    #[test]
    fn check_is_one() {
        pre_process("../data/bigint/std/is_one.bs");
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
        pre_process("../data/bigint/std/is_one_keep_element.bs");
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
        pre_process("../data/bigint/push_one.bs");
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
    fn check_bn254_push_one() {
        pre_process("../data/bn254/fp254impl/push_one.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_stack_rel(0, builder.build_constant(1), RelOp::Eq);
        builder.build_assertion(assertion);
        let script = script! {
            { Fq::push_one_not_montgomery() }
            { add_assertions(&builder) }
        };
        dump_script(&script);
    }

    #[test]
    fn check_push_zero() {
        pre_process("../data/bigint/push_zero.bs");
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
    fn check_bn254_push_zero() {
        pre_process("../data/bn254/fp254impl/push_zero.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_stack_rel(0, builder.build_constant(0), RelOp::Eq);
        builder.build_assertion(assertion);
        let script = script! {
            {Fq::push_zero()}
            {add_assertions(&builder) }
        };
        dump_script(&script);
    }

    #[test]
    fn check_drop() {
        pre_process("../data/bigint/std/drop.bs");
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
    fn check_bn254_drop() {
        pre_process("../data/bn254/fp254impl/drop.bs");
        let mut builder: ConstraintBuilder = ConstraintBuilder::new();
        builder.build_stack_symbolic_limb_eq(0, 0, U254::N_LIMBS);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {Fq::drop()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_toaltstack() {
        pre_process("../data/bigint/std/toaltstack.bs");
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
    fn check_bn254_toaltstack() {
        pre_process("../data/bn254/fp254impl/toaltstack.bs");
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
            {Fq::toaltstack()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_fromaltstack() {
        pre_process("../data/bigint/std/fromaltstack.bs");
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
    fn check_bn254_fromaltstack() {
        pre_process("../data/bn254/fp254impl/fromaltstack.bs");
        let mut builder: ConstraintBuilder = ConstraintBuilder::new();
        builder.build_stack_symbolic_limb_eq(0, 0, U254::N_LIMBS);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {Fq::toaltstack()}
            {Fq::fromaltstack()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_is_negative() {
        pre_process("../data/bigint/std/is_negative.bs");
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
        pre_process("../data/bigint/std/is_positive.bs");
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
        pre_process("../data/bigint/std/zip.bs");
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
    fn check_bn254_zip() {
        pre_process("../data/bn254/fp254impl/zip.bs");
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
            {Fq::zip(a, b)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_copy_zip() {
        pre_process("../data/bigint/std/copy_zip.bs");
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
        pre_process("../data/bigint/std/dup_zip.bs");
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
        pre_process("../data/bigint/std/copy.bs");
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
    fn check_bn254_copy() {
        pre_process("../data/bn254/fp254impl/copy.bs");
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
            {Fq::copy(a as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_copy_deep() {
        pre_process("../data/bigint/std/copy_deep.bs");
        let a = 16;
        let mut builder = ConstraintBuilder::new();
        builder.build_stack_symbolic_limb_eq(0, 0, U254::N_LIMBS);
        for i in 1..=a {
            builder.build_stack_symbolic_limb_eq(
                (i * U254::N_LIMBS) as usize,
                (a - i) as usize,
                U254::N_LIMBS,
            );
        }
        let script = script! {
            for i in 0..=a {
                {U254::push_verification_meta(MetaType::SymbolicVar(i as usize))}
            }
            {U254::copy(a as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_copy_deep() {
        pre_process("../data/bn254/fp254impl/copy_deep.bs");
        let a = 16;
        let mut builder = ConstraintBuilder::new();
        builder.build_stack_symbolic_limb_eq(0, 0, U254::N_LIMBS);
        for i in 1..=a {
            builder.build_stack_symbolic_limb_eq(
                (i * U254::N_LIMBS) as usize,
                (a - i) as usize,
                U254::N_LIMBS,
            );
        }
        let script = script! {
            for i in 0..a {
                {U254::push_verification_meta(MetaType::SymbolicVar(i as usize))}
            }
            {Fq::copy(a as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_roll() {
        pre_process("../data/bigint/std/roll.bs");
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
    fn check_bn254_roll() {
        pre_process("../data/bn254/fp254impl/roll.bs");
        let a = 1;
        let mut builder = ConstraintBuilder::new();
        builder.build_stack_symbolic_limb_eq(0, 0, U254::N_LIMBS);
        builder.build_stack_symbolic_limb_eq(U254::N_LIMBS as usize, 1, U254::N_LIMBS);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {Fq::roll(a as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_resize_cut() {
        pre_process("../data/bigint/std/resize_1.bs");
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
        pre_process("../data/bigint/std/resize_2.bs");
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
        pre_process("../data/bigint/equalverify.bs");
        let mut builder = ConstraintBuilder::new();
        builder.build_assertion(builder.build_rel(
            builder.build_symbolic(0),
            builder.build_symbolic(1),
            RelOp::Eq,
        ));
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
    fn check_bn254_equalverify() {
        pre_process("../data/bn254/fp254impl/equalverify.bs");
        let mut builder = ConstraintBuilder::new();
        builder.build_assertion(builder.build_rel(
            builder.build_symbolic(0),
            builder.build_symbolic(1),
            RelOp::Eq,
        ));
        let a = 1;
        let b = 0;
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {Fq::equalverify(a, b)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_equal() {
        pre_process("../data/bigint/equal.bs");
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
    fn check_bn254_equal() {
        pre_process("../data/bn254/fp254impl/equal.bs");
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
            {Fq::equal(a, b)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_notequal() {
        pre_process("../data/bigint/notequal.bs");
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
        pre_process("../data/bigint/lessthanorequal.bs");
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
        pre_process("../data/bigint/greaterthan.bs");
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
        pre_process("../data/bigint/greaterthanorequal.bs");
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
        pre_process("../data/bigint/lessthan.bs");
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
        pre_process("../data/bigint/add/double.bs");
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
                            RelOp::Ge,
                        ),
                        builder.build_constant(1 << limb_size),
                        builder.build_constant(0),
                    ),
                ),
                RelOp::Eq,
            );
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Ge),
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
        pre_process("../data/bigint/add/add.bs");
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
                            RelOp::Ge,
                        ),
                        builder.build_constant(1 << limb_size),
                        builder.build_constant(0),
                    ),
                ),
                RelOp::Eq,
            );
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Ge),
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
    fn check_lshift_prevent_overflow() {
        pre_process("../data/bigint/add/lshift_prevent_overflow.bs");
        let mut builder = ConstraintBuilder::new();
        let shift_bits = 30;
        let mut limb_size = 29;
        let mut carry = vec![];
        for i in 0..U254::N_LIMBS {
            if i + 1 == U254::N_LIMBS {
                limb_size = 22;
            }
            let shift_outer_offset = shift_bits / limb_size;
            let shift_inner_offset = shift_bits % limb_size;
            let limb = builder.build_symbolic_limb(0, i as usize);
            let left_expr = builder.build_rshift_expr(
                limb.clone(),
                builder.build_constant((limb_size - shift_inner_offset) as u128),
            );
            carry.push((shift_outer_offset + 1, left_expr.clone()));
            let right_expr = builder.build_lshift_expr(
                builder.build_sub_expr(
                    limb,
                    builder.build_lshift_expr(
                        left_expr,
                        builder.build_constant((limb_size - shift_inner_offset) as u128),
                    ),
                ),
                builder.build_constant(shift_inner_offset as u128),
            );
            carry.push((shift_outer_offset, right_expr));
            let mut res_expr = ValueExpr::Constant(0);
            let mut new_carry = Vec::with_capacity(carry.len());
            for (counter, expr) in carry.iter_mut() {
                // println!("counter:{}\n  expr: {}", *counter, expr.to_string());
                if *counter == 0 {
                    res_expr = builder.build_add_expr(res_expr.clone(), expr.clone());
                } else {
                    *counter -= 1;
                    new_carry.push((*counter, expr.clone()));
                }
            }
            carry = new_carry;
            builder.build_assertion(builder.build_stack_rel(i as usize, res_expr, RelOp::Eq));
        }
        let mut restrict_line = shift_bits;
        for i in (0..U254::N_LIMBS).rev() {
            let index = i as usize;
            let expr: BoolExpr;
            if i == U254::N_LIMBS - 1 {
                if restrict_line >= 22 {
                    expr = builder.build_rel(
                        builder.build_symbolic_limb(0, index),
                        builder.build_constant(0),
                        RelOp::Eq,
                    );
                    restrict_line -= 22;
                } else {
                    expr = builder.build_rel(
                        builder.build_symbolic_limb(0, index),
                        builder.build_constant(1 << (22 - restrict_line)),
                        RelOp::Le,
                    );
                    restrict_line = 0;
                }
            } else {
                if restrict_line >= 29 {
                    expr = builder.build_rel(
                        builder.build_symbolic_limb(0, index),
                        builder.build_constant(0),
                        RelOp::Eq,
                    );
                    restrict_line -= 29;
                } else {
                    expr = builder.build_rel(
                        builder.build_symbolic_limb(0, index),
                        builder.build_constant(1 << (29 - restrict_line)),
                        RelOp::Le,
                    );
                    restrict_line = 0;
                }
            }
            builder.build_assertion(expr);
            if restrict_line == 0 {
                break;
            }
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::lshift_prevent_overflow(shift_bits)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_add1() {
        pre_process("../data/bigint/add/add1.bs");
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
                            RelOp::Ge,
                        ),
                        builder.build_constant(1 << limb_size),
                        builder.build_constant(0),
                    ),
                ),
                RelOp::Eq,
            );
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Ge),
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
        pre_process("../data/bigint/add/double_allow_overflow.bs");
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
                            RelOp::Ge,
                        ),
                        builder.build_constant(1 << limb_size),
                        builder.build_constant(0),
                    ),
                ),
                RelOp::Eq,
            );
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Ge),
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
        pre_process("../data/bigint/add/double_allow_overflow_keep_element.bs");
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
                            RelOp::Ge,
                        ),
                        builder.build_constant(1 << limb_size),
                        builder.build_constant(0),
                    ),
                ),
                RelOp::Eq,
            );
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Ge),
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
        pre_process("../data/bigint/add/double_prevent_overflow.bs");
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
                        RelOp::Ge,
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
                    RelOp::Neq,
                ));
            }
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Ge),
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
        pre_process("../data/bigint/add/add_ref_with_top.bs");
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
                        RelOp::Ge,
                    ),
                    builder.build_constant(1 << limb_size),
                    builder.build_constant(0),
                ),
            );
            let assertion = builder.build_stack_rel(index, value_nlo.clone(), RelOp::Eq);
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Ge),
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
        pre_process("../data/bigint/add/add_ref.bs");
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
                        RelOp::Ge,
                    ),
                    builder.build_constant(1 << limb_size),
                    builder.build_constant(0),
                ),
            );
            let assertion = builder.build_stack_rel(index, value_nlo.clone(), RelOp::Eq);
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Ge),
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
        pre_process("../data/bigint/add/add_ref_stack.bs");
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
                        RelOp::Ge,
                    ),
                    builder.build_constant(1 << limb_size),
                    builder.build_constant(0),
                ),
            );
            let assertion = builder.build_stack_rel(index, value_nlo.clone(), RelOp::Eq);
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(1 << limb_size), RelOp::Ge),
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
            for id in (0..=depth).rev(){
                {U254::push_verification_meta(MetaType::SymbolicVar(id as usize))}
            }
            {depth}
            {U254::add_ref_stack()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_sub() {
        pre_process("../data/bigint/sub/sub.bs");
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
            let value = builder.build_sub_expr(builder.build_sub_expr(limba, limbb), carry);
            let assertion = builder.build_stack_rel(
                index,
                builder.build_add_expr(
                    value.clone(),
                    builder.build_if_expr(
                        builder.build_rel(value.clone(), builder.build_constant(0), RelOp::Lt),
                        builder.build_constant(1 << limb_size),
                        builder.build_constant(0),
                    ),
                ),
                RelOp::Eq,
            );
            carry = builder.build_if_expr(
                builder.build_rel(value, builder.build_constant(0), RelOp::Lt),
                builder.build_constant(1),
                builder.build_constant(0),
            );
            builder.build_assertion(assertion);
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::sub(1,0)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_mul() {
        use std::array;
        pre_process("../data/bigint/mul/mul.bs");
        let mut builder = ConstraintBuilder::new();
        let mut exprs: [ValueExpr; 9] = array::from_fn(|_| ValueExpr::Constant(0));
        for i in 0..U254::N_LIMBS as usize {
            let mut limb_size = 29;
            for j in 0..U254::N_LIMBS as usize {
                if i + j >= U254::N_LIMBS as usize {
                    break;
                } else if i + j + 1 == U254::N_LIMBS as usize {
                    limb_size = 22;
                }
                let limba = builder.build_symbolic_limb(0, i);
                let limbb = builder.build_symbolic_limb(1, j);
                exprs[i + j] = builder.build_add_expr(
                    exprs[i + j].clone(),
                    builder.build_mod_expr(
                        builder.build_mul_expr(limba.clone(), limbb.clone()),
                        builder.build_constant(1 << limb_size),
                    ),
                );
                if i + j + 1 < U254::N_LIMBS as usize {
                    if i + j + 1 == U254::N_LIMBS as usize - 1 {
                        exprs[i + j + 1] = builder.build_add_expr(
                            exprs[i + j + 1].clone(),
                            builder.build_mod_expr(
                                builder.build_rshift_expr(
                                    builder.build_mul_expr(limba, limbb),
                                    builder.build_constant(29),
                                ),
                                builder.build_constant(1 << 22),
                            ),
                        );
                    } else {
                        exprs[i + j + 1] = builder.build_add_expr(
                            exprs[i + j + 1].clone(),
                            builder.build_rshift_expr(
                                builder.build_mul_expr(limba, limbb),
                                builder.build_constant(29),
                            ),
                        );
                    }
                }
            }
        }
        let mut limb_size = 29;
        for i in 0..U254::N_LIMBS as usize {
            if i == U254::N_LIMBS as usize - 1 {
                limb_size = 22;
            }
            builder.build_assertion(builder.build_stack_rel(
                i,
                builder.build_mod_expr(exprs[i].clone(), builder.build_constant(1 << limb_size)),
                RelOp::Eq,
            ));
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::mul()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_mul_ver() {
        use std::array;
        pre_process("../data/bigint/mul/mul_ver.bs");
        let mut builder = ConstraintBuilder::new();
        let mut exprs: [ValueExpr; 9] = array::from_fn(|_| ValueExpr::Constant(0));
        for i in 0..U254::N_LIMBS as usize {
            let mut limb_size = 29;
            for j in 0..U254::N_LIMBS as usize {
                if i + j >= U254::N_LIMBS as usize {
                    break;
                } else if i + j + 1 == U254::N_LIMBS as usize {
                    limb_size = 22;
                }
                let limba = builder.build_symbolic_limb(0, i);
                let limbb = builder.build_symbolic_limb(1, j);
                exprs[i + j] = builder.build_add_expr(
                    exprs[i + j].clone(),
                    builder.build_mod_expr(
                        builder.build_mul_expr(limba.clone(), limbb.clone()),
                        builder.build_constant(1 << limb_size),
                    ),
                );
                if i + j + 1 < U254::N_LIMBS as usize {
                    if i + j + 1 == U254::N_LIMBS as usize - 1 {
                        exprs[i + j + 1] = builder.build_add_expr(
                            exprs[i + j + 1].clone(),
                            builder.build_mod_expr(
                                builder.build_rshift_expr(
                                    builder.build_mul_expr(limba, limbb),
                                    builder.build_constant(29),
                                ),
                                builder.build_constant(1 << 22),
                            ),
                        );
                    } else {
                        exprs[i + j + 1] = builder.build_add_expr(
                            exprs[i + j + 1].clone(),
                            builder.build_rshift_expr(
                                builder.build_mul_expr(limba, limbb),
                                builder.build_constant(29),
                            ),
                        );
                    }
                }
            }
        }
        let mut limb_size = 29;
        for i in 0..U254::N_LIMBS as usize {
            if i == U254::N_LIMBS as usize - 1 {
                limb_size = 22;
            }
            builder.build_assertion(builder.build_stack_rel(
                i,
                builder.build_mod_expr(exprs[i].clone(), builder.build_constant(1 << limb_size)),
                RelOp::Eq,
            ));
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::mul_ver(&builder)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_convert_to_be_bits() {
        pre_process("../data/bigint/bits/convert_to_be_bits.bs");
        let mut builder = ConstraintBuilder::new();
        let mut limb_size: u32 = 22;
        let mut index = 0;
        for i in 0..U254::N_LIMBS {
            if i != 0 {
                limb_size = 29;
            }
            let mut expr = ValueExpr::Constant(0);
            for j in 0..limb_size {
                expr = builder.build_add_expr(
                    expr.clone(),
                    builder.build_mul_expr(
                        builder.build_stack((index + j) as usize),
                        builder.build_constant(1 << (limb_size - j - 1) as u128),
                    ),
                );
                builder.build_assertion(builder.build_rel(
                    builder.build_mul_expr(
                        builder.build_sub_expr(
                            builder.build_stack((index + j) as usize),
                            builder.build_constant(0),
                        ),
                        builder.build_sub_expr(
                            builder.build_stack((index + j) as usize),
                            builder.build_constant(1),
                        ),
                    ),
                    builder.build_constant(0),
                    RelOp::Eq,
                ));
            }
            builder.build_assertion(builder.build_rel(
                builder.build_symbolic_limb(0, (U254::N_LIMBS - i - 1) as usize),
                expr,
                RelOp::Eq,
            ));
            index += limb_size;
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::convert_to_be_bits()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_convert_to_be_bits() {
        pre_process("../data/bn254/fp254impl/convert_to_be_bits.bs");
        let mut builder = ConstraintBuilder::new();
        let mut limb_size: u32 = 22;
        let mut index = 0;
        for i in 0..U254::N_LIMBS {
            if i != 0 {
                limb_size = 29;
            }
            let mut expr = ValueExpr::Constant(0);
            for j in 0..limb_size {
                expr = builder.build_add_expr(
                    expr.clone(),
                    builder.build_mul_expr(
                        builder.build_stack((index + j) as usize),
                        builder.build_constant(1 << (limb_size - j - 1) as u128),
                    ),
                );
                builder.build_assertion(builder.build_rel(
                    builder.build_mul_expr(
                        builder.build_sub_expr(
                            builder.build_stack((index + j) as usize),
                            builder.build_constant(0),
                        ),
                        builder.build_sub_expr(
                            builder.build_stack((index + j) as usize),
                            builder.build_constant(1),
                        ),
                    ),
                    builder.build_constant(0),
                    RelOp::Eq,
                ));
            }
            builder.build_assertion(builder.build_rel(
                builder.build_symbolic_limb(0, (U254::N_LIMBS - i - 1) as usize),
                expr,
                RelOp::Eq,
            ));
            index += limb_size;
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {Fq::convert_to_be_bits()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_convert_to_le_bits() {
        pre_process("../data/bigint/bits/convert_to_le_bits.bs");
        let mut builder = ConstraintBuilder::new();
        let mut limb_size: u32 = 29;
        let mut index = 0;
        for i in 0..U254::N_LIMBS {
            if i + 1 == U254::N_LIMBS {
                limb_size = 22;
            }
            let mut expr = ValueExpr::Constant(0);
            for j in 0..limb_size {
                expr = builder.build_add_expr(
                    expr.clone(),
                    builder.build_mul_expr(
                        builder.build_stack((index + j) as usize),
                        builder.build_constant(1 << j as u128),
                    ),
                );
                builder.build_assertion(builder.build_rel(
                    builder.build_mul_expr(
                        builder.build_sub_expr(
                            builder.build_stack((index + j) as usize),
                            builder.build_constant(0),
                        ),
                        builder.build_sub_expr(
                            builder.build_stack((index + j) as usize),
                            builder.build_constant(1),
                        ),
                    ),
                    builder.build_constant(0),
                    RelOp::Eq,
                ));
            }
            builder.build_assertion(builder.build_rel(
                builder.build_symbolic_limb(0, i as usize),
                expr,
                RelOp::Eq,
            ));
            index += limb_size;
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::convert_to_le_bits()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_convert_to_le_bits() {
        pre_process("../data/bn254/fp254impl/convert_to_le_bits.bs");
        let mut builder = ConstraintBuilder::new();
        let mut limb_size: u32 = 29;
        let mut index = 0;
        for i in 0..U254::N_LIMBS {
            if i + 1 == U254::N_LIMBS {
                limb_size = 22;
            }
            let mut expr = ValueExpr::Constant(0);
            for j in 0..limb_size {
                expr = builder.build_add_expr(
                    expr.clone(),
                    builder.build_mul_expr(
                        builder.build_stack((index + j) as usize),
                        builder.build_constant(1 << j as u128),
                    ),
                );
                builder.build_assertion(builder.build_rel(
                    builder.build_mul_expr(
                        builder.build_sub_expr(
                            builder.build_stack((index + j) as usize),
                            builder.build_constant(0),
                        ),
                        builder.build_sub_expr(
                            builder.build_stack((index + j) as usize),
                            builder.build_constant(1),
                        ),
                    ),
                    builder.build_constant(0),
                    RelOp::Eq,
                ));
            }
            builder.build_assertion(builder.build_rel(
                builder.build_symbolic_limb(0, i as usize),
                expr,
                RelOp::Eq,
            ));
            index += limb_size;
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {Fq::convert_to_le_bits()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_convert_to_be_bits_toaltstack() {
        pre_process("../data/bigint/bits/convert_to_be_bits_toaltstack.bs");
        let mut builder = ConstraintBuilder::new();
        let mut limb_size: u32 = 29;
        let mut index = 0;
        for i in 0..U254::N_LIMBS {
            if i + 1 == U254::N_LIMBS {
                limb_size = 22;
            }
            let mut expr = ValueExpr::Constant(0);
            for j in 0..limb_size {
                expr = builder.build_add_expr(
                    expr.clone(),
                    builder.build_mul_expr(
                        builder.build_alt_stack((index + j) as usize),
                        builder.build_constant(1 << j as u128),
                    ),
                );
                builder.build_assertion(builder.build_rel(
                    builder.build_mul_expr(
                        builder.build_sub_expr(
                            builder.build_alt_stack((index + j) as usize),
                            builder.build_constant(0),
                        ),
                        builder.build_sub_expr(
                            builder.build_alt_stack((index + j) as usize),
                            builder.build_constant(1),
                        ),
                    ),
                    builder.build_constant(0),
                    RelOp::Eq,
                ));
            }
            builder.build_assertion(builder.build_rel(
                builder.build_symbolic_limb(0, i as usize),
                expr,
                RelOp::Eq,
            ));
            index += limb_size;
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::convert_to_be_bits_toaltstack()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_convert_to_be_bits_toaltstack() {
        pre_process("../data/bn254/fp254impl/convert_to_be_bits_toaltstack.bs");
        let mut builder = ConstraintBuilder::new();
        let mut limb_size: u32 = 29;
        let mut index = 0;
        for i in 0..U254::N_LIMBS {
            if i + 1 == U254::N_LIMBS {
                limb_size = 22;
            }
            let mut expr = ValueExpr::Constant(0);
            for j in 0..limb_size {
                expr = builder.build_add_expr(
                    expr.clone(),
                    builder.build_mul_expr(
                        builder.build_alt_stack((index + j) as usize),
                        builder.build_constant(1 << j as u128),
                    ),
                );
                builder.build_assertion(builder.build_rel(
                    builder.build_mul_expr(
                        builder.build_sub_expr(
                            builder.build_alt_stack((index + j) as usize),
                            builder.build_constant(0),
                        ),
                        builder.build_sub_expr(
                            builder.build_alt_stack((index + j) as usize),
                            builder.build_constant(1),
                        ),
                    ),
                    builder.build_constant(0),
                    RelOp::Eq,
                ));
            }
            builder.build_assertion(builder.build_rel(
                builder.build_symbolic_limb(0, i as usize),
                expr,
                RelOp::Eq,
            ));
            index += limb_size;
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {Fq::convert_to_be_bits_toaltstack()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_convert_to_le_bits_toaltstack() {
        pre_process("../data/bigint/bits/convert_to_le_bits_toaltstack.bs");
        let mut builder = ConstraintBuilder::new();
        let mut limb_size: u32 = 22;
        let mut index = 0;
        for i in 0..U254::N_LIMBS {
            if i != 0 {
                limb_size = 29;
            }
            let mut expr = ValueExpr::Constant(0);
            for j in 0..limb_size {
                expr = builder.build_add_expr(
                    expr.clone(),
                    builder.build_mul_expr(
                        builder.build_alt_stack((index + j) as usize),
                        builder.build_constant(1 << (limb_size - j - 1) as u128),
                    ),
                );
                builder.build_assertion(builder.build_rel(
                    builder.build_mul_expr(
                        builder.build_sub_expr(
                            builder.build_alt_stack((index + j) as usize),
                            builder.build_constant(0),
                        ),
                        builder.build_sub_expr(
                            builder.build_alt_stack((index + j) as usize),
                            builder.build_constant(1),
                        ),
                    ),
                    builder.build_constant(0),
                    RelOp::Eq,
                ));
            }
            builder.build_assertion(builder.build_rel(
                builder.build_symbolic_limb(0, (U254::N_LIMBS - i - 1) as usize),
                expr,
                RelOp::Eq,
            ));
            index += limb_size;
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::convert_to_le_bits_toaltstack()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_convert_to_le_bits_toaltstack() {
        pre_process("../data/bn254/fp254impl/convert_to_le_bits_toaltstack.bs");
        let mut builder = ConstraintBuilder::new();
        let mut limb_size: u32 = 22;
        let mut index = 0;
        for i in 0..U254::N_LIMBS {
            if i != 0 {
                limb_size = 29;
            }
            let mut expr = ValueExpr::Constant(0);
            for j in 0..limb_size {
                expr = builder.build_add_expr(
                    expr.clone(),
                    builder.build_mul_expr(
                        builder.build_alt_stack((index + j) as usize),
                        builder.build_constant(1 << (limb_size - j - 1) as u128),
                    ),
                );
                builder.build_assertion(builder.build_rel(
                    builder.build_mul_expr(
                        builder.build_sub_expr(
                            builder.build_alt_stack((index + j) as usize),
                            builder.build_constant(0),
                        ),
                        builder.build_sub_expr(
                            builder.build_alt_stack((index + j) as usize),
                            builder.build_constant(1),
                        ),
                    ),
                    builder.build_constant(0),
                    RelOp::Eq,
                ));
            }
            builder.build_assertion(builder.build_rel(
                builder.build_symbolic_limb(0, (U254::N_LIMBS - i - 1) as usize),
                expr,
                RelOp::Eq,
            ));
            index += limb_size;
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {Fq::convert_to_le_bits_toaltstack()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_limb_from_bytes() {
        pre_process("../data/bigint/bits/limb_from_bytes.bs");
        let mut builder = ConstraintBuilder::new();
        for i in 0..4 {
            builder.build_assumption(builder.build_stack_rel(
                i as usize,
                builder.build_constant(255),
                RelOp::Le,
            ));
            builder.build_assumption(builder.build_stack_rel(
                i as usize,
                builder.build_constant(0),
                RelOp::Ge,
            ));
        }
        let mut expr = ValueExpr::Constant(0);
        for i in 0..4 {
            expr = builder.build_add_expr(
                expr.clone(),
                builder.build_mul_expr(
                    builder.build_symbolic(i as usize),
                    builder.build_constant(1 << (i * 8) as u128),
                ),
            );
        }
        builder.build_assertion(builder.build_stack_rel(0, expr, RelOp::Eq));
        let script = script! {
            for i in (0..4).rev(){
                {U254::push_verification_meta(MetaType::SymbolicVar(i))}
            }
            {add_assumptions(&builder)}
            {U254::limb_from_bytes()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_from_bytes() {
        pre_process("../data/bigint/bits/from_bytes.bs");
        let mut builder = ConstraintBuilder::new();
        for i in 0..4 * U254::N_LIMBS {
            builder.build_assumption(builder.build_stack_rel(
                i as usize,
                builder.build_constant(255),
                RelOp::Le,
            ));
            builder.build_assumption(builder.build_stack_rel(
                i as usize,
                builder.build_constant(0),
                RelOp::Ge,
            ));
        }
        for i in 0..U254::N_LIMBS {
            let mut expr = ValueExpr::Constant(0);
            for j in 0..4 {
                expr = builder.build_add_expr(
                    expr.clone(),
                    builder.build_mul_expr(
                        builder.build_symbolic((i * U254::N_LIMBS + j) as usize),
                        builder.build_constant(1 << (j * 8) as u128),
                    ),
                );
            }
            builder.build_assertion(builder.build_stack_rel(i as usize, expr, RelOp::Eq));
        }
        let script = script! {
            for i in (0..4*U254::N_LIMBS).rev(){
                {U254::push_verification_meta(MetaType::SymbolicVar(i as usize))}
            }
            {add_assumptions(&builder)}
            {U254::from_bytes()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_div2() {
        pre_process("../data/bigint/inv/div2.bs");
        let mut builder = ConstraintBuilder::new();
        let mut carry = ValueExpr::Constant(0);
        for i in (0..U254::N_LIMBS).rev() {
            builder.build_assertion(builder.build_stack_rel(
                i as usize,
                builder.build_add_expr(
                    builder.build_rshift_expr(
                        builder.build_symbolic_limb(0, i as usize),
                        builder.build_constant(1),
                    ),
                    builder.build_mul_expr(carry, builder.build_constant(1 << 28)),
                ),
                RelOp::Eq,
            ));
            carry = builder.build_mod_expr(
                builder.build_symbolic_limb(0, i as usize),
                builder.build_constant(2),
            );
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::div2()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_div2rem() {
        pre_process("../data/bigint/inv/div2rem.bs");
        let mut builder = ConstraintBuilder::new();
        let mut carry = ValueExpr::Constant(0);

        for i in (0..U254::N_LIMBS).rev() {
            builder.build_assertion(builder.build_stack_rel(
                (i + 1) as usize,
                builder.build_add_expr(
                    builder.build_rshift_expr(
                        builder.build_symbolic_limb(0, i as usize),
                        builder.build_constant(1),
                    ),
                    builder.build_mul_expr(carry, builder.build_constant(1 << 28)),
                ),
                RelOp::Eq,
            ));
            carry = builder.build_mod_expr(
                builder.build_symbolic_limb(0, i as usize),
                builder.build_constant(2),
            );
        }
        builder.build_assertion(builder.build_stack_rel(0, carry, RelOp::Eq));
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::div2rem()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_div3() {
        pre_process("../data/bigint/inv/div3.bs");
        let mut builder = ConstraintBuilder::new();
        builder.build_assertion(builder.build_rel(
            builder.build_div_expr(builder.build_symbolic(0), builder.build_constant(3)),
            builder.build_stack_eq_u254_variable(0),
            RelOp::Eq,
        ));
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::div3()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_div3rem() {
        pre_process("../data/bigint/inv/div3rem.bs");
        let mut builder = ConstraintBuilder::new();
        let mut carry = ValueExpr::Constant(0);
        for i in (0..U254::N_LIMBS).rev() {
            builder.build_assertion(builder.build_stack_rel(
                (i + 1) as usize,
                builder.build_add_expr(
                    builder.build_div_expr(
                        builder.build_symbolic_limb(0, i as usize),
                        builder.build_constant(3),
                    ),
                    builder.build_div_expr(
                        builder.build_mul_expr(carry, builder.build_constant(1 << 29)),
                        builder.build_constant(3),
                    ),
                ),
                RelOp::Eq,
            ));
            carry = builder.build_mod_expr(
                builder.build_symbolic_limb(0, i as usize),
                builder.build_constant(3),
            );
        }
        builder.build_assertion(builder.build_stack_rel(0, carry, RelOp::Eq));
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::div3rem()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_inv_stage1() {
        pre_process("../data/bigint/inv/inv_stage1.bs");
        let mut builder = ConstraintBuilder::new();
        builder.build_assertion(builder.build_rel(
            builder.build_mod_expr(
                builder.build_add_expr(
                    builder.build_lshift_expr(builder.build_constant(1), builder.build_stack(0)),
                    builder.build_mul_expr(
                        builder.build_sub_expr(
                            builder.build_symbolic(0),
                            builder.build_stack_eq_u254_variable(1),
                        ),
                        builder.build_symbolic(1),
                    ),
                ),
                builder.build_symbolic(0),
            ),
            builder.build_constant(0),
            RelOp::Eq,
        ));
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))} // modulus
            {U254::push_verification_meta(MetaType::SymbolicVar(1))} // number
            {U254::inv_stage1()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_is_zero() {
        pre_process("../data/bn254/fp254impl/is_zero.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_constant(0), RelOp::Eq)
        });
        builder.build_assertion(assertion);
        let script = script! {
            { U254::push_verification_meta(MetaType::SymbolicVar(0)) }
            { Fq::is_zero(0) }
            { add_assertions(&builder) }
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_push_modulus() {
        pre_process("../data/bn254/fp254impl/push_modulus.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_rel(
            builder.build_big_constant(
                "21888242871839275222246405745257275088696311157297823662689037894645226208583"
                    .to_string(),
            ),
            builder.build_stack_eq_u254_variable(0),
            RelOp::Eq,
        );
        builder.build_assertion(assertion);
        let script = script! {
            { Fq::push_modulus() }
            { add_assertions(&builder) }
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_push_one_montgomory() {
        pre_process("../data/bn254/fp254impl/push_one_montgomory.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_rel(
            builder.build_bn254_one_mont(),
            builder.build_stack_eq_u254_variable(0),
            RelOp::Eq,
        );
        builder.build_assertion(assertion);
        let script = script! {
            { Fq::push_one() }
            { add_assertions(&builder) }
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_add() {
        pre_process("../data/bn254/fp254impl/add.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_rel(
            builder.build_mod_expr(
                builder.build_add_expr(builder.build_symbolic(0), builder.build_symbolic(1)),
                builder.build_bn254_mod(),
            ),
            builder.build_stack_eq_u254_variable(0),
            RelOp::Eq,
        );
        builder.build_assertion(assertion);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {Fq::add(1,0)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_neg() {
        pre_process("../data/bn254/fp254impl/neg.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_rel(
            builder.build_mod_expr(
                builder.build_add_expr(
                    builder.build_stack_eq_u254_variable(0),
                    builder.build_symbolic(0),
                ),
                builder.build_bn254_mod(),
            ),
            builder.build_constant(0),
            RelOp::Eq,
        );
        builder.build_assertion(assertion);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {Fq::neg(0)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_sub() {
        pre_process("../data/bn254/fp254impl/sub.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_rel(
            builder.build_mod_expr(
                builder.build_sub_expr(
                    builder.build_add_expr(builder.build_symbolic(0), builder.build_bn254_mod()),
                    builder.build_symbolic(1),
                ),
                builder.build_bn254_mod(),
            ),
            builder.build_stack_eq_u254_variable(0),
            RelOp::Eq,
        );
        builder.build_assertion(assertion);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {Fq::sub(1,0)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_double() {
        pre_process("../data/bn254/fp254impl/double.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_rel(
            builder.build_mod_expr(
                builder.build_add_expr(
                    builder.build_mod_expr(builder.build_symbolic(0), builder.build_bn254_mod()),
                    builder.build_mod_expr(builder.build_symbolic(0), builder.build_bn254_mod()),
                ),
                builder.build_bn254_mod(),
            ),
            builder.build_stack_eq_u254_variable(0),
            RelOp::Eq,
        );
        builder.build_assertion(assertion);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {Fq::double(0)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_is_one() {
        pre_process("../data/bn254/fp254impl/is_one.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_bn254_one_mont(), RelOp::Eq)
        });

        builder.build_assertion(assertion);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {Fq::is_one(0)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_is_one_keep_element() {
        pre_process("../data/bn254/fp254impl/is_one_keep_element.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_bn254_one_mont(), RelOp::Eq)
        });
        builder.build_assertion(assertion);
        builder.build_stack_symbolic_limb_eq(1, 0, U254::N_LIMBS);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {Fq::is_one_keep_element(0)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_is_one_not_montgomery() {
        pre_process("../data/bn254/fp254impl/is_one_not_montgomery.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_constant(1), RelOp::Eq)
        });

        builder.build_assertion(assertion);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {Fq::is_one_not_montgomery()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_is_one_keep_element_not_montgomery() {
        pre_process("../data/bn254/fp254impl/is_one_keep_element_not_montgomery.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_rel(expr, builder.build_constant(1), RelOp::Eq)
        });
        builder.build_assertion(assertion);
        builder.build_stack_symbolic_limb_eq(1, 0, U254::N_LIMBS);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {Fq::is_one_keep_element_not_montgomery(0)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_is_field() {
        pre_process("../data/bn254/fp254impl/is_field.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_if_symbol_cond_top(0, |expr| {
            builder.build_and_rel(
                builder.build_rel(
                    builder.build_symbolic(0),
                    builder.build_bn254_mod(),
                    RelOp::Lt,
                ),
                builder.build_rel(
                    builder.build_symbolic(0),
                    builder.build_constant(0),
                    RelOp::Ge,
                ),
            )
        });
        builder.build_assertion(assertion);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {Fq::is_field()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_bn254_square() {
        pre_process("../data/bn254/fp254impl/square.bs");
        let mut builder = ConstraintBuilder::new();
        let assertion = builder.build_rel(
            builder.build_mod_expr(
                builder.build_mul_expr(
                    builder.build_mod_expr(builder.build_symbolic(0), builder.build_bn254_mod()),
                    builder.build_mod_expr(builder.build_symbolic(0), builder.build_bn254_mod()),
                ),
                builder.build_bn254_mod(),
            ),
            builder.build_stack_eq_u254_variable(0),
            RelOp::Eq,
        );
        builder.build_assertion(assertion);
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {Fq::square()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    // #[test]
    // fn check_bn254_div2() {
    //     pre_process("../data/bn254/fp254impl/div2.bs");
    //     let mut builder = ConstraintBuilder::new();
    //     builder.build_assertion(expr);
    //     let script = script! {
    //         {U254::push_verification_meta(MetaType::SymbolicVar(0))}
    //         {Fq::div2()}
    //         {add_assertions(&builder)}
    //     };
    //     dump_script(&script);
    // }
}
