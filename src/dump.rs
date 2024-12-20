// use std::fmt::format;
use std::fs;

use std::fs::OpenOptions;
use std::io::Write;
use std::path::Path;

use crate::bigint::U254;
use bitcoin_script::Script;

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
    SingleSymbolicVar(usize),
    InternalVar(usize, ValueExpr),
    Assertion(usize, BoolExpr),
    Assumption(usize, BoolExpr),
}

#[derive(Clone)]
pub enum ValueExpr {
    RefSymbolVar(usize),
    RefSymbolLimb(usize, usize),
    RefInternalVar(usize),
    RefSymbolLimbBit(usize, usize, usize),
    RefStack(usize),    // offset in main stack
    RefAltStack(usize), // offset in alt stack
    Constant(u128),     // TODO: Constants within 2^254
    BigConstant(String),
    OpSha256(Box<ValueExpr>),
    App(Box<ValueExpr>, Box<ValueExpr>),
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
            ValueExpr::RefInternalVar(i) => format!("i{}", i),
            ValueExpr::RefSymbolLimb(i, j) => format!("limbs{}[{}]", i, j),
            ValueExpr::RefSymbolLimbBit(i, j, k) => format!("limbs{}[{}].({})", i, j, k),
            ValueExpr::RefStack(i) => format!("stack[{}]", i),
            ValueExpr::RefAltStack(i) => format!("altstack[{}]", i),
            ValueExpr::Constant(val) => format!("{}", val),
            ValueExpr::BigConstant(string) => string.clone(),
            ValueExpr::App(lhs, rhs) => format!("({} ++ {})", lhs.to_string(), rhs.to_string()),
            ValueExpr::Add(lhs, rhs) => format!("({} + {})", lhs.to_string(), rhs.to_string()),
            ValueExpr::Sub(lhs, rhs) => format!("({} - {})", lhs.to_string(), rhs.to_string()),
            ValueExpr::Mul(lhs, rhs) => format!("({} * {})", lhs.to_string(), rhs.to_string()),
            ValueExpr::Div(lhs, rhs) => format!("({} / {})", lhs.to_string(), rhs.to_string()),
            ValueExpr::Mod(lhs, rhs) => format!("({} % {})", lhs.to_string(), rhs.to_string()),
            ValueExpr::OpSha256(expr) => format!("(sha256 {})", expr.to_string()),
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
    internal_cnt: usize,
}

#[allow(dead_code)]
impl ConstraintBuilder {
    // Initialize a new builder
    pub fn new() -> Self {
        ConstraintBuilder {
            assertions: Vec::new(),
            assumptions: Vec::new(),
            internal_cnt: 0,
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

    pub fn build_internal_var_subtitute_expr(&mut self, expr: ValueExpr) -> (ValueExpr, Script) {
        self.internal_cnt += 1;
        (
            ValueExpr::RefInternalVar(self.internal_cnt),
            U254::push_verification_meta(MetaType::InternalVar(self.internal_cnt, expr)),
        )
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

    pub fn build_app_expr(&self, expr: ValueExpr, expr1: ValueExpr) -> ValueExpr {
        ValueExpr::App(Box::new(expr), Box::new(expr1))
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

    pub fn build_sha256(&self, expr: ValueExpr) -> ValueExpr { ValueExpr::OpSha256(Box::new(expr)) }

    pub fn build_check_top(&mut self) {
        let expr: BoolExpr = self.build_stack_rel(0, self.build_constant(1), RelOp::Eq);
        self.build_assertion(expr);
    }
    pub fn build_overflow_exp(&self, expr: ValueExpr, limb_size: usize) -> ValueExpr {
        self.build_mod_expr(expr.clone(), self.build_constant(1 << limb_size as u128))
    }

    pub fn build_overflow_exp_shift(&self, expr: ValueExpr, limb_size: usize) -> ValueExpr {
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
            let shift: u128 = bit % 29 as u128;
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
            self.build_rshift_expr(self.build_symbolic(sym_index), self.build_constant(bit)),
            self.build_lshift_expr(
                self.build_rshift_expr(
                    self.build_symbolic(sym_index),
                    self.build_constant(bit + 1),
                ),
                self.build_constant(1),
            ),
        )
    }

    pub fn build_symbolic_limb_bit(
        &self,
        sym_index: usize,
        limb_index: usize,
        shift: usize,
    ) -> ValueExpr {
        ValueExpr::RefSymbolLimbBit(sym_index, limb_index, shift)
    }

    pub fn build_bit_of_symbolic_limb(&self, sym_index: usize, bit: u128) -> ValueExpr {
        let limb_index = bit / 29;
        let shift = bit % 29;

        ValueExpr::RefSymbolLimbBit(sym_index, limb_index as usize, shift as usize)
    }

    pub fn build_bit_of_symbolic_limb_shiftver(&self, sym_index: usize, bit: u128) -> ValueExpr {
        let limb_index = bit / 29;
        let shift = bit % 29;

        self.build_sub_expr(
            self.build_rshift_expr(
                self.build_symbolic_limb(sym_index, limb_index as usize),
                self.build_constant(shift),
            ),
            self.build_lshift_expr(
                self.build_rshift_expr(
                    self.build_symbolic_limb(sym_index, limb_index as usize),
                    self.build_constant(shift + 1),
                ),
                self.build_constant(1),
            ),
        )
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

    pub fn dump_assumption(&self, expr: BoolExpr, index: &mut usize) -> Script {
        let script = { U254::push_verification_meta(MetaType::Assumption(*index, expr)) };
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
    use crate::bigint::bits::{
        limb_to_be_bits, limb_to_be_bits_toaltstack, limb_to_le_bits, limb_to_le_bits_toaltstack,
    };
    use crate::bigint::inv::{limb_div3_carry_inv, limb_div_carry_inner};
    use crate::bigint::sub::{limb_sub_borrow, limb_sub_noborrow};
    use crate::bigint::U254;
    use crate::bn254::curves::G1Projective;
    use crate::bn254::fp254impl::Fp254Impl;
    use crate::bn254::fq::Fq;
    use crate::stark::*;
    use bitcoin::opcodes::all::OP_TOALTSTACK;
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
        for i in 0..=a {
            builder.build_stack_symbolic_limb_eq(
                ((i + 1) * U254::N_LIMBS) as usize,
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
        for i in 0..=a {
            builder.build_stack_symbolic_limb_eq(
                ((i + 1) * U254::N_LIMBS) as usize,
                (a - i) as usize,
                U254::N_LIMBS,
            );
        }
        let script = script! {
            for i in 0..=a {
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
        fn normal() {
            pre_process("../data/bigint/sub/sub.bs");
            let mut builder = ConstraintBuilder::new();
            let mut carry = ValueExpr::Constant(0);
            let mut limb_size: u32 = 29;
            for i in 0..U254::N_LIMBS {
                if i + 1 == U254::N_LIMBS {
                    limb_size = 22;
                }
                let index: usize = i as usize;
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

        fn inv() {
            pre_process("../data/bigint/sub/sub_inv.bs");
            let mut builder = ConstraintBuilder::new();
            let mut carry = ValueExpr::Constant(0);
            let mut limb_size: u32 = 29;
            for i in 0..U254::N_LIMBS {
                if i + 1 == U254::N_LIMBS {
                    limb_size = 22;
                }
                let index: usize = i as usize;
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
                {U254::sub_inv(&builder,1,0)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inner() {
            pre_process("../data/bigint/sub/sub_inner.bs");
            let mut builder = ConstraintBuilder::new();
            builder.build_assertion(
                builder.build_stack_rel(
                    0,
                    builder.build_if_expr(
                        builder.build_rel(
                            builder.build_sub_expr(
                                builder.build_symbolic(0),
                                builder.build_symbolic(1),
                            ),
                            builder.build_constant(0),
                            RelOp::Lt,
                        ),
                        builder.build_add_expr(
                            builder.build_sub_expr(
                                builder.build_symbolic(0),
                                builder.build_symbolic(1),
                            ),
                            builder.build_symbolic(2),
                        ),
                        builder
                            .build_sub_expr(builder.build_symbolic(0), builder.build_symbolic(1)),
                    ),
                    RelOp::Eq,
                ),
            );
            builder.build_assertion(
                builder.build_stack_rel(
                    1,
                    builder.build_if_expr(
                        builder.build_rel(
                            builder.build_sub_expr(
                                builder.build_symbolic(0),
                                builder.build_symbolic(1),
                            ),
                            builder.build_constant(0),
                            RelOp::Lt,
                        ),
                        builder.build_constant(1),
                        builder.build_constant(0),
                    ),
                    RelOp::Eq,
                ),
            );
            builder.build_assertion(builder.build_stack_rel(
                2,
                builder.build_symbolic(2),
                RelOp::Eq,
            ));

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(1))}
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(2))}
                {limb_sub_borrow()}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inner_1() {
            pre_process("../data/bigint/sub/sub_inner_1.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 22;
            builder.build_assertion(
                builder.build_stack_rel(
                    0,
                    builder.build_if_expr(
                        builder.build_rel(
                            builder.build_sub_expr(
                                builder.build_symbolic(0),
                                builder.build_symbolic(1),
                            ),
                            builder.build_constant(0),
                            RelOp::Lt,
                        ),
                        builder.build_add_expr(
                            builder.build_sub_expr(
                                builder.build_symbolic(0),
                                builder.build_symbolic(1),
                            ),
                            builder.build_constant(1 << limb_size as u128),
                        ),
                        builder
                            .build_sub_expr(builder.build_symbolic(0), builder.build_symbolic(1)),
                    ),
                    RelOp::Eq,
                ),
            );
            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(1))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(1),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(1),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_sub_noborrow(1<<limb_size)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        normal();
        inv();
        inner();
        inner_1();
    }

    #[test]
    fn check_mul() {
        fn mul_ver() {
            pre_process("../data/bigint/mul/mul.bs");
            let mut builder = ConstraintBuilder::new();
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(1))}
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::mul_ver(&mut builder)}
            };
            dump_script(&script);
        }

        fn mul_inv() {
            pre_process("../data/bigint/mul/mul_inv.bs");
            let mut builder = ConstraintBuilder::new();
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(1))}
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::mul_inv(&mut builder)}
            };
            dump_script(&script);
        }

        fn mul_inv_inner_1() {
            pre_process("../data/bigint/mul/mul_inv_inner_1.bs");
            let mut builder = ConstraintBuilder::new();
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(1))}
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(2))}
                {
                    builder.dump_assumption(
                        builder.build_or_rel(
                            builder.build_rel(
                                builder.build_symbolic(2),
                                builder.build_constant(0),
                                RelOp::Eq,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(2),
                                builder.build_constant(1),
                                RelOp::Eq,
                            ),
                        ),
                        &mut 0,
                    )
                }
                OP_TOALTSTACK
                {U254::mul_inv_inner_1(&mut builder)}
            };
            dump_script(&script);
        }

        mul_ver();
        mul_inv();
        mul_inv_inner_1();
    }

    #[test]
    fn check_convert_to_be_bits() {
        fn normal() {
            pre_process("../data/bigint/bits/convert_to_be_bits.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_stack_rel(
                    (U254::N_BITS - i - 1) as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::convert_to_be_bits()}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inv() {
            pre_process("../data/bigint/bits/convert_to_be_bits_inv.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_stack_rel(
                    (U254::N_BITS - i - 1) as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::convert_to_be_bits_inv(&builder)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inner_1() {
            pre_process("../data/bigint/bits/convert_to_be_bits_inner_1.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 29;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_stack_rel(
                    limb_size - i - 1,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_be_bits(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        fn inner_2() {
            pre_process("../data/bigint/bits/convert_to_be_bits_inner_2.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 22;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_stack_rel(
                    limb_size - i - 1,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_be_bits(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        normal();
        inv();
        inner_1();
        inner_2();
    }

    #[test]
    fn check_bn254_convert_to_be_bits() {
        fn normal() {
            pre_process("../data/bn254/fp254impl/convert_to_be_bits.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_stack_rel(
                    (U254::N_BITS - i - 1) as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {Fq::convert_to_be_bits()}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inv() {
            pre_process("../data/bn254/fp254impl/convert_to_be_bits_inv.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_stack_rel(
                    (U254::N_BITS - i - 1) as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {Fq::convert_to_be_bits_inv(&builder)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inner_1() {
            pre_process("../data/bn254/fp254impl/convert_to_be_bits_inner_1.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 29;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_stack_rel(
                    limb_size - i - 1,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_be_bits(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        fn inner_2() {
            pre_process("../data/bn254/fp254impl/convert_to_be_bits_inner_2.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 22;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_stack_rel(
                    limb_size - i - 1,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_be_bits(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        normal();
        inv();
        inner_1();
        inner_2();
    }

    #[test]
    fn check_convert_to_le_bits() {
        fn normal() {
            pre_process("../data/bigint/bits/convert_to_le_bits.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_stack_rel(
                    i as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::convert_to_le_bits()}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inv() {
            pre_process("../data/bigint/bits/convert_to_le_bits_inv.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_stack_rel(
                    i as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::convert_to_le_bits_inv(&builder)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inner_1() {
            pre_process("../data/bigint/bits/convert_to_le_bits_inner_1.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 29;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_stack_rel(
                    i,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_le_bits(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        fn inner_2() {
            pre_process("../data/bigint/bits/convert_to_le_bits_inner_2.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 22;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_stack_rel(
                    i,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_le_bits(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        normal();
        inv();
        inner_1();
        inner_2();
    }

    #[test]
    fn check_bn254_convert_to_le_bits() {
        fn normal() {
            pre_process("../data/bn254/fp254impl/convert_to_le_bits.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_stack_rel(
                    i as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {Fq::convert_to_le_bits()}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inv() {
            pre_process("../data/bn254/fp254impl/convert_to_le_bits_inv.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_stack_rel(
                    i as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {Fq::convert_to_le_bits_inv(&builder)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inner_1() {
            pre_process("../data/bn254/fp254impl/convert_to_le_bits_inner_1.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 29;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_stack_rel(
                    i,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_le_bits(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        fn inner_2() {
            pre_process("../data/bn254/fp254impl/convert_to_le_bits_inner_2.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 22;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_stack_rel(
                    i,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_le_bits(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        normal();
        inv();
        inner_1();
        inner_2();
    }

    #[test]
    fn check_bn254_convert_to_be_bits_toaltstack() {
        fn normal() {
            pre_process("../data/bn254/fp254impl/convert_to_be_bits_toaltstack.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_alt_stack_rel(
                    i as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {Fq::convert_to_be_bits_toaltstack()}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inv() {
            pre_process("../data/bn254/fp254impl/convert_to_be_bits_toaltstack_inv.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_alt_stack_rel(
                    i as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {Fq::convert_to_be_bits_toaltstack_inv(&builder)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inner_1() {
            pre_process("../data/bn254/fp254impl/convert_to_be_bits_toaltstack_inner_1.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 29;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_alt_stack_rel(
                    i,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_be_bits_toaltstack(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        fn inner_2() {
            pre_process("../data/bn254/fp254impl/convert_to_be_bits_toaltstack_inner_2.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 22;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_alt_stack_rel(
                    i,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_be_bits_toaltstack(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        normal();
        inv();
        inner_1();
        inner_2();
    }

    #[test]
    fn check_convert_to_be_bits_toaltstack() {
        fn normal() {
            pre_process("../data/bigint/bits/convert_to_be_bits_toaltstack.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_alt_stack_rel(
                    i as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::convert_to_be_bits_toaltstack()}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inv() {
            pre_process("../data/bigint/bits/convert_to_be_bits_toaltstack_inv.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_alt_stack_rel(
                    i as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::convert_to_be_bits_toaltstack_inv(&builder)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inner_1() {
            pre_process("../data/bigint/bits/convert_to_be_bits_toaltstack_inner_1.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 29;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_alt_stack_rel(
                    i,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_be_bits_toaltstack(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        fn inner_2() {
            pre_process("../data/bigint/bits/convert_to_be_bits_toaltstack_inner_2.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 22;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_alt_stack_rel(
                    i,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_be_bits_toaltstack(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        normal();
        inv();
        inner_1();
        inner_2();
    }

    #[test]
    fn check_convert_to_le_bits_toaltstack() {
        fn normal() {
            pre_process("../data/bigint/bits/convert_to_le_bits_toaltstack.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_alt_stack_rel(
                    (U254::N_BITS - i - 1) as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::convert_to_le_bits_toaltstack()}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inv() {
            pre_process("../data/bigint/bits/convert_to_le_bits_toaltstack_inv.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_alt_stack_rel(
                    (U254::N_BITS - i - 1) as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::convert_to_le_bits_toaltstack_inv(&builder)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inner_1() {
            pre_process("../data/bigint/bits/convert_to_le_bits_toaltstack_inner_1.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 29;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_alt_stack_rel(
                    limb_size - i - 1,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_le_bits_toaltstack(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        fn inner_2() {
            pre_process("../data/bigint/bits/convert_to_le_bits_toaltstack_inner_2.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 22;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_alt_stack_rel(
                    limb_size - i - 1,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_le_bits_toaltstack(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        normal();
        inv();
        inner_1();
        inner_2();
    }

    #[test]
    fn check_bn254_convert_to_le_bits_toaltstack() {
        fn normal() {
            pre_process("../data/bn254/fp254impl/convert_to_le_bits_toaltstack.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_alt_stack_rel(
                    (U254::N_BITS - i - 1) as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {Fq::convert_to_le_bits_toaltstack()}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inv() {
            pre_process("../data/bn254/fp254impl/convert_to_le_bits_toaltstack_inv.bs");
            let mut builder = ConstraintBuilder::new();
            for i in 0..U254::N_BITS {
                builder.build_assertion(builder.build_alt_stack_rel(
                    (U254::N_BITS - i - 1) as usize,
                    builder.build_bit_of_symbolic_limb(0, i as u128),
                    RelOp::Eq,
                ));
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {Fq::convert_to_le_bits_toaltstack_inv(&builder)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inner_1() {
            pre_process("../data/bn254/fp254impl/convert_to_le_bits_toaltstack_inner_1.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 29;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_alt_stack_rel(
                    limb_size - i - 1,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_le_bits_toaltstack(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        fn inner_2() {
            pre_process("../data/bn254/fp254impl/convert_to_le_bits_toaltstack_inner_2.bs");
            let mut builder = ConstraintBuilder::new();
            let limb_size = 22;
            for i in 0..limb_size {
                builder.build_assertion(builder.build_alt_stack_rel(
                    limb_size - i - 1,
                    builder.build_bit_of_symbolic(0, i as u128),
                    RelOp::Eq,
                ));
            }

            let mut index = 0;

            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {
                    builder.dump_assumption(
                        builder.build_and_rel(
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(1 << limb_size),
                                RelOp::Lt,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(0),
                                builder.build_constant(0),
                                RelOp::Ge,
                            ),
                        ),
                        &mut index,
                    )
                }
                {limb_to_le_bits_toaltstack(limb_size as u32)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        normal();
        inv();
        inner_1();
        inner_2();
    }

    #[test]
    fn check_limb_from_bytes() {
        pre_process("../data/bigint/bits/limb_from_bytes.bs");
        let mut builder = ConstraintBuilder::new();
        for i in 0..4 {
            builder.build_assumption(builder.build_rel(
                builder.build_symbolic(i),
                builder.build_constant(255),
                RelOp::Le,
            ));
            builder.build_assumption(builder.build_rel(
                builder.build_symbolic(i),
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
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(i))}
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
        for i in 0..4 * U254::N_LIMBS as usize {
            builder.build_assumption(builder.build_rel(
                builder.build_symbolic(i),
                builder.build_constant(255),
                RelOp::Le,
            ));
            builder.build_assumption(builder.build_rel(
                builder.build_symbolic(i),
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
                        builder.build_symbolic((i * 4 + j) as usize),
                        builder.build_constant(1 << (j * 8) as u128),
                    ),
                );
            }
            builder.build_assertion(builder.build_stack_rel(i as usize, expr, RelOp::Eq));
        }
        let script = script! {
            for i in (0..4*U254::N_LIMBS).rev(){
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(i as usize))}
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
    fn check_bn254_div2() {
        fn normal() {
            pre_process("../data/bn254/fp254impl/div2.bs");
            let mut builder = ConstraintBuilder::new();
            builder.build_assertion(
            builder.build_rel(
                builder.build_stack_eq_u254_variable(0),
                builder.build_if_expr(
                    builder.build_rel(
                        builder.build_mod_expr(
                            builder.build_symbolic_limb(0, 0),
                            builder.build_constant(2),
                        ),
                        builder.build_constant(0),
                        RelOp::Eq,
                    ),
                    builder.build_rshift_expr(builder.build_symbolic(0), builder.build_constant(1)),
                    builder.build_mod_expr(
                        builder.build_add_expr(
                            builder.build_rshift_expr(
                                builder.build_symbolic(0),
                                builder.build_constant(1),
                            ),
                            builder.build_big_constant(
                                "0x183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c3e7ea4"
                                    .to_string(),
                            ),
                        ),
                        builder.build_bn254_mod(),
                    ),
                ),
                RelOp::Eq,
            ),
        );
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {Fq::div2()}
                { add_assertions(&builder) }
            };
            dump_script(&script);
        }
        fn inv() {
            pre_process("../data/bn254/fp254impl/div2_inv.bs");
            let mut builder = ConstraintBuilder::new();
            builder.build_assertion(
            builder.build_rel(
                builder.build_stack_eq_u254_variable(0),
                builder.build_if_expr(
                    builder.build_rel(
                        builder.build_mod_expr(
                            builder.build_symbolic_limb(0, 0),
                            builder.build_constant(2),
                        ),
                        builder.build_constant(0),
                        RelOp::Eq,
                    ),
                    builder.build_rshift_expr(builder.build_symbolic(0), builder.build_constant(1)),
                    builder.build_mod_expr(
                        builder.build_add_expr(
                            builder.build_rshift_expr(
                                builder.build_symbolic(0),
                                builder.build_constant(1),
                            ),
                            builder.build_big_constant(
                                "0x183227397098d014dc2822db40c0ac2ecbc0b548b438e5469e10460b6c3e7ea4"
                                    .to_string(),
                            ),
                        ),
                        builder.build_bn254_mod(),
                    ),
                ),
                RelOp::Eq,
            ),
        );
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {Fq::div2_inv(&builder)}
                { add_assertions(&builder) }
            };
            dump_script(&script);
        }
        normal();
        inv();
    }

    #[test]
    fn check_bn254_div3() {
        fn normal(){
            pre_process("../data/bn254/fp254impl/div3.bs");
            let mut builder = ConstraintBuilder::new();
            builder.build_assertion(
                builder.build_rel(
                    builder.build_stack_eq_u254_variable(0),
                    builder.build_if_expr(
                        builder.build_rel(
                            builder.build_mod_expr(builder.build_symbolic(0), builder.build_constant(3)),
                            builder.build_constant(0),
                            RelOp::Eq,
                        ),
                        builder.build_div_expr(builder.build_symbolic(0), builder.build_constant(3)),
                        builder.build_if_expr(
                            builder.build_rel(
                                builder.build_mod_expr(builder.build_symbolic(0), builder.build_constant(3)),
                                builder.build_constant(1),
                                RelOp::Eq,
                            ),
                            builder.build_mod_expr(
                                builder.build_add_expr(
                                    builder.build_div_expr(
                                        builder.build_symbolic(0),
                                        builder.build_constant(3),
                                    ),
                                    builder.build_big_constant(
                                        "0x2042def740cbc01bd03583cf0100e593ba56470b9af68708d2c05d6490535385"
                                            .to_string(),
                                    ),
                                ),
                                builder.build_bn254_mod(),
                            ),
                            builder.build_mod_expr(
                                builder.build_add_expr(
                                    builder.build_div_expr(
                                        builder.build_symbolic(0),
                                        builder.build_constant(3),
                                    ),
                                    builder.build_big_constant(
                                        "0x10216f7ba065e00de81ac1e7808072c9dd2b2385cd7b438469602eb24829a9c3"
                                            .to_string(),
                                    ),
                                ),
                                builder.build_bn254_mod(),
                            )
                        )
                        
                    ),
                    RelOp::Eq,
                ),
            );
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {Fq::div3()}
                { add_assertions(&builder) }
            };
            dump_script(&script);
        }
        fn inv(){
            pre_process("../data/bn254/fp254impl/div3_inv.bs");
            let mut builder = ConstraintBuilder::new();
            builder.build_assertion(
                builder.build_rel(
                    builder.build_stack_eq_u254_variable(0),
                    builder.build_if_expr(
                        builder.build_rel(
                            builder.build_mod_expr(builder.build_symbolic(0), builder.build_constant(3)),
                            builder.build_constant(0),
                            RelOp::Eq,
                        ),
                        builder.build_div_expr(builder.build_symbolic(0), builder.build_constant(3)),
                        builder.build_if_expr(
                            builder.build_rel(
                                builder.build_mod_expr(builder.build_symbolic(0), builder.build_constant(3)),
                                builder.build_constant(1),
                                RelOp::Eq,
                            ),
                            builder.build_mod_expr(
                                builder.build_add_expr(
                                    builder.build_div_expr(
                                        builder.build_symbolic(0),
                                        builder.build_constant(3),
                                    ),
                                    builder.build_big_constant(
                                        "0x2042def740cbc01bd03583cf0100e593ba56470b9af68708d2c05d6490535385"
                                            .to_string(),
                                    ),
                                ),
                                builder.build_bn254_mod(),
                            ),
                            builder.build_mod_expr(
                                builder.build_add_expr(
                                    builder.build_div_expr(
                                        builder.build_symbolic(0),
                                        builder.build_constant(3),
                                    ),
                                    builder.build_big_constant(
                                        "0x10216f7ba065e00de81ac1e7808072c9dd2b2385cd7b438469602eb24829a9c3"
                                            .to_string(),
                                    ),
                                ),
                                builder.build_bn254_mod(),
                            )
                        )
                        
                    ),
                    RelOp::Eq,
                ),
            );
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {Fq::div3_inv(&builder)}
                { add_assertions(&builder) }
            };
            dump_script(&script);
        }
        normal();
        inv();
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
        fn normal() {
            pre_process("../data/bigint/inv/div3.bs");
            let mut builder = ConstraintBuilder::new();
            let mut carry = ValueExpr::Constant(0);
            for i in (0..U254::N_LIMBS as usize).rev() {
                let expr = if i == U254::N_LIMBS as usize - 1 {
                    builder.build_symbolic_limb(0, i)
                } else {
                    builder.build_add_expr(
                        builder.build_symbolic_limb(0, i),
                        builder.build_mul_expr(carry, builder.build_constant(1 << 29)),
                    )
                };
                builder.build_assertion(builder.build_stack_rel(
                    i,
                    builder.build_div_expr(expr.clone(), builder.build_constant(3)),
                    RelOp::Eq,
                ));
                carry = builder.build_mod_expr(expr, builder.build_constant(3))
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::div3()}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inv() {
            pre_process("../data/bigint/inv/div3_inv.bs");
            let mut builder = ConstraintBuilder::new();
            let mut carry = ValueExpr::Constant(0);
            for i in (0..U254::N_LIMBS as usize).rev() {
                let expr = if i == U254::N_LIMBS as usize - 1 {
                    builder.build_symbolic_limb(0, i)
                } else {
                    builder.build_add_expr(
                        builder.build_symbolic_limb(0, i),
                        builder.build_mul_expr(carry, builder.build_constant(1 << 29)),
                    )
                };
                builder.build_assertion(builder.build_stack_rel(
                    i,
                    builder.build_div_expr(expr.clone(), builder.build_constant(3)),
                    RelOp::Eq,
                ));
                carry = builder.build_mod_expr(expr, builder.build_constant(3))
            }
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::div3_inv(&builder)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inner() {
            pre_process("../data/bigint/inv/div3_inner.bs");
            let mut builder = ConstraintBuilder::new();
            let mut index = 100;
            let origin_value = builder.build_add_expr(
                builder.build_mul_expr(builder.build_symbolic(0), builder.build_constant(1 << 29)),
                builder.build_symbolic(1),
            );
            builder.build_assertion(builder.build_stack_rel(
                0,
                builder.build_mod_expr(origin_value.clone(), builder.build_constant(3)),
                RelOp::Eq,
            )); // res_mod
            builder.build_assertion(builder.build_stack_rel(
                1,
                builder.build_div_expr(origin_value, builder.build_constant(3)),
                RelOp::Eq,
            )); // res_div
            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(1))}
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                { builder.dump_assumption(
                    builder.build_and_rel(
                        builder.build_rel(
                            builder.build_symbolic(0),
                            builder.build_constant(0),
                            RelOp::Ge,
                        ),
                        builder.build_rel(
                            builder.build_symbolic(0),
                            builder.build_constant(2),
                            RelOp::Le,
                        ),
                    ),
                    &mut index,
                ) }
                { builder.dump_assumption(
                    builder.build_and_rel(
                        builder.build_rel(
                            builder.build_symbolic(1),
                            builder.build_constant(0),
                            RelOp::Ge,
                        ),
                        builder.build_rel(
                            builder.build_symbolic(1),
                            builder.build_constant(1<<29),
                            RelOp::Le,
                        ),
                    ),
                    &mut index,
                ) }
                {limb_div3_carry_inv(&builder,29)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        fn inner_inner() {
            pre_process("../data/bigint/inv/div3_inner_inner.bs");
            let builder = ConstraintBuilder::new();
            let mut index = 100;
            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(3))}
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(2))}
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(1))}
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(4))}
                OP_TOALTSTACK
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(0), builder.build_constant(1<<29), RelOp::Lt), &mut index)}
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(1), builder.build_constant(1<<29), RelOp::Lt), &mut index)}
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(2), builder.build_constant(1<<29), RelOp::Lt), &mut index)}
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(3), builder.build_constant(1<<29), RelOp::Lt), &mut index)}
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(0), builder.build_constant(0), RelOp::Ge), &mut index)}
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(1), builder.build_constant(0), RelOp::Ge), &mut index)}
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(2), builder.build_constant(0), RelOp::Ge), &mut index)}
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(3), builder.build_constant(0), RelOp::Ge), &mut index)}
                {builder.dump_assumption(
                    builder.build_rel(
                        builder.build_symbolic(1),
                        builder.build_mul_expr(builder.build_symbolic(3), builder.build_constant(3)),
                        RelOp::Eq,
                    ),
                    &mut index,
                )}
                {
                    builder.dump_assumption(
                        builder.build_rel(
                            builder.build_symbolic(0),
                            builder.build_mul_expr(builder.build_constant(2), builder.build_symbolic(1)),
                            RelOp::Lt,
                        ),
                        &mut index,
                    )
                }
                {limb_div_carry_inner(&builder)}
            };
            dump_script(&script);
        }
        normal();
        inv();
        inner();
        inner_inner();
    }

    #[test]
    fn check_div3_rem() {
        fn normal() {
            pre_process("../data/bigint/inv/div3_rem.bs");
            let mut builder = ConstraintBuilder::new();
            let mut carry = ValueExpr::Constant(0);
            for i in (0..U254::N_LIMBS as usize).rev() {
                let expr = if i == U254::N_LIMBS as usize - 1 {
                    builder.build_symbolic_limb(0, i)
                } else {
                    builder.build_add_expr(
                        builder.build_symbolic_limb(0, i),
                        builder.build_mul_expr(carry, builder.build_constant(1 << 29)),
                    )
                };
                builder.build_assertion(builder.build_stack_rel(
                    i + 1,
                    builder.build_div_expr(expr.clone(), builder.build_constant(3)),
                    RelOp::Eq,
                ));
                carry = builder.build_mod_expr(expr, builder.build_constant(3))
            }
            builder.build_assertion(builder.build_stack_rel(0, carry, RelOp::Eq));
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::div3rem()}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inv() {
            pre_process("../data/bigint/inv/div3_rem_inv.bs");
            let mut builder = ConstraintBuilder::new();
            let mut carry = ValueExpr::Constant(0);
            for i in (0..U254::N_LIMBS as usize).rev() {
                let expr = if i == U254::N_LIMBS as usize - 1 {
                    builder.build_symbolic_limb(0, i)
                } else {
                    builder.build_add_expr(
                        builder.build_symbolic_limb(0, i),
                        builder.build_mul_expr(carry, builder.build_constant(1 << 29)),
                    )
                };
                builder.build_assertion(builder.build_stack_rel(
                    i + 1,
                    builder.build_div_expr(expr.clone(), builder.build_constant(3)),
                    RelOp::Eq,
                ));
                carry = builder.build_mod_expr(expr, builder.build_constant(3))
            }
            builder.build_assertion(builder.build_stack_rel(0, carry, RelOp::Eq));
            builder.build_assertion(builder.build_stack_rel(0, builder.build_mod_expr(builder.build_symbolic(0), builder.build_constant(3)), RelOp::Eq));
            let script = script! {
                {U254::push_verification_meta(MetaType::SymbolicVar(0))}
                {U254::div3rem_inv(&builder)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }

        fn inner() {
            pre_process("../data/bigint/inv/div3_rem_inner.bs");
            let mut builder = ConstraintBuilder::new();
            let mut index = 100;
            let origin_value = builder.build_add_expr(
                builder.build_mul_expr(builder.build_symbolic(0), builder.build_constant(1 << 29)),
                builder.build_symbolic(1),
            );
            builder.build_assertion(builder.build_stack_rel(
                0,
                builder.build_mod_expr(origin_value.clone(), builder.build_constant(3)),
                RelOp::Eq,
            )); // res_mod
            builder.build_assertion(builder.build_stack_rel(
                1,
                builder.build_div_expr(origin_value, builder.build_constant(3)),
                RelOp::Eq,
            )); // res_div
            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(1))}
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                { builder.dump_assumption(
                    builder.build_and_rel(
                        builder.build_rel(
                            builder.build_symbolic(0),
                            builder.build_constant(0),
                            RelOp::Ge,
                        ),
                        builder.build_rel(
                            builder.build_symbolic(0),
                            builder.build_constant(2),
                            RelOp::Le,
                        ),
                    ),
                    &mut index,
                ) }
                { builder.dump_assumption(
                    builder.build_and_rel(
                        builder.build_rel(
                            builder.build_symbolic(1),
                            builder.build_constant(0),
                            RelOp::Ge,
                        ),
                        builder.build_rel(
                            builder.build_symbolic(1),
                            builder.build_constant(1<<29),
                            RelOp::Le,
                        ),
                    ),
                    &mut index,
                ) }
                {limb_div3_carry_inv(&builder,29)}
                {add_assertions(&builder)}
            };
            dump_script(&script);
        }
        fn inner_inner() {
            pre_process("../data/bigint/inv/div3_rem_inner_inner.bs");
            let builder = ConstraintBuilder::new();
            let mut index = 100;
            let script = script! {
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(3))}
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(2))}
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(1))}
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(4))}
                OP_TOALTSTACK
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(0), builder.build_constant(1<<29), RelOp::Lt), &mut index)}
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(1), builder.build_constant(1<<29), RelOp::Lt), &mut index)}
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(2), builder.build_constant(1<<29), RelOp::Lt), &mut index)}
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(3), builder.build_constant(1<<29), RelOp::Lt), &mut index)}
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(0), builder.build_constant(0), RelOp::Ge), &mut index)}
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(1), builder.build_constant(0), RelOp::Ge), &mut index)}
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(2), builder.build_constant(0), RelOp::Ge), &mut index)}
                {builder.dump_assumption(builder.build_rel(builder.build_symbolic(3), builder.build_constant(0), RelOp::Ge), &mut index)}
                {builder.dump_assumption(
                    builder.build_rel(
                        builder.build_symbolic(1),
                        builder.build_mul_expr(builder.build_symbolic(3), builder.build_constant(3)),
                        RelOp::Eq,
                    ),
                    &mut index,
                )}
                {
                    builder.dump_assumption(
                        builder.build_rel(
                            builder.build_symbolic(0),
                            builder.build_mul_expr(builder.build_constant(2), builder.build_symbolic(1)),
                            RelOp::Lt,
                        ),
                        &mut index,
                    )
                }
                {limb_div_carry_inner(&builder)}
            };
            dump_script(&script);
        }
        normal();
        inv();
        inner();
        inner_inner();
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
        let assertion = builder.build_if_symbol_cond_top(0, |_| {
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
    fn check_curves_neg() {
        pre_process("../data/bn254/curves/neg.bs");
        let mut builder = ConstraintBuilder::new();
        builder.build_assertion(builder.build_rel(
            builder.build_stack_eq_u254_variable(0),
            builder.build_symbolic(0),
            RelOp::Eq,
        ));
        builder.build_assertion(builder.build_rel(
            builder.build_stack_eq_u254_variable(2 * U254::N_LIMBS as usize),
            builder.build_symbolic(2),
            RelOp::Eq,
        ));
        builder.build_assertion(builder.build_rel(
            builder.build_constant(0),
            builder.build_mod_expr(
                builder.build_add_expr(
                    builder.build_stack_eq_u254_variable(U254::N_LIMBS as usize),
                    builder.build_symbolic(1),
                ),
                builder.build_bn254_mod(),
            ),
            RelOp::Eq,
        ));
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(2))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {G1Projective::neg()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_curves_copy() {
        pre_process("../data/bn254/curves/copy.bs");
        let mut builder = ConstraintBuilder::new();
        for i in 0..=2 {
            builder.build_assertion(builder.build_rel(
                builder.build_stack_eq_u254_variable(i * U254::N_LIMBS as usize),
                builder.build_symbolic(i + 6),
                RelOp::Eq,
            ));
        }
        for i in 0..=8 {
            builder.build_assertion(builder.build_rel(
                builder.build_stack_eq_u254_variable((i + 3) * U254::N_LIMBS as usize),
                builder.build_symbolic(i),
                RelOp::Eq,
            ));
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(8))}
            {U254::push_verification_meta(MetaType::SymbolicVar(7))}
            {U254::push_verification_meta(MetaType::SymbolicVar(6))}
            {U254::push_verification_meta(MetaType::SymbolicVar(5))}
            {U254::push_verification_meta(MetaType::SymbolicVar(4))}
            {U254::push_verification_meta(MetaType::SymbolicVar(3))}
            {U254::push_verification_meta(MetaType::SymbolicVar(2))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {G1Projective::copy(2)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_curves_drop() {
        pre_process("../data/bn254/curves/drop.bs");
        let mut builder = ConstraintBuilder::new();

        for i in 3..=8 {
            builder.build_assertion(builder.build_rel(
                builder.build_stack_eq_u254_variable((i - 3) * U254::N_LIMBS as usize),
                builder.build_symbolic(i),
                RelOp::Eq,
            ));
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(8))}
            {U254::push_verification_meta(MetaType::SymbolicVar(7))}
            {U254::push_verification_meta(MetaType::SymbolicVar(6))}
            {U254::push_verification_meta(MetaType::SymbolicVar(5))}
            {U254::push_verification_meta(MetaType::SymbolicVar(4))}
            {U254::push_verification_meta(MetaType::SymbolicVar(3))}
            {U254::push_verification_meta(MetaType::SymbolicVar(2))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {G1Projective::drop()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_curves_toaltstack() {
        pre_process("../data/bn254/curves/toaltstack.bs");
        let mut builder = ConstraintBuilder::new();

        for i in 0..3 * U254::N_LIMBS as usize {
            let assertion = builder.build_alt_stack_rel(
                i,
                builder.build_symbolic_limb(
                    i / (U254::N_LIMBS as usize),
                    U254::N_LIMBS as usize - (i % U254::N_LIMBS as usize) - 1,
                ),
                RelOp::Eq,
            );
            builder.build_assertion(assertion);
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::push_verification_meta(MetaType::SymbolicVar(2))}
            {G1Projective::toaltstack()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_curves_fromaltstack() {
        pre_process("../data/bn254/curves/fromaltstack.bs");
        let mut builder = ConstraintBuilder::new();

        for i in 0..3 * U254::N_LIMBS as usize {
            let assertion = builder.build_stack_rel(
                i,
                builder.build_symbolic_limb(i / U254::N_LIMBS as usize, i % U254::N_LIMBS as usize),
                RelOp::Eq,
            );
            builder.build_assertion(assertion);
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(2))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {G1Projective::toaltstack()}
            {G1Projective::fromaltstack()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_curves_roll() {
        pre_process("../data/bn254/curves/roll.bs");
        let mut builder = ConstraintBuilder::new();
        for i in 0..=2 {
            builder.build_assertion(builder.build_rel(
                builder.build_stack_eq_u254_variable(i * U254::N_LIMBS as usize),
                builder.build_symbolic(i + 6),
                RelOp::Eq,
            ));
        }
        for i in 0..=5 {
            builder.build_assertion(builder.build_rel(
                builder.build_stack_eq_u254_variable((i + 3) * U254::N_LIMBS as usize),
                builder.build_symbolic(i),
                RelOp::Eq,
            ));
        }
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(8))}
            {U254::push_verification_meta(MetaType::SymbolicVar(7))}
            {U254::push_verification_meta(MetaType::SymbolicVar(6))}
            {U254::push_verification_meta(MetaType::SymbolicVar(5))}
            {U254::push_verification_meta(MetaType::SymbolicVar(4))}
            {U254::push_verification_meta(MetaType::SymbolicVar(3))}
            {U254::push_verification_meta(MetaType::SymbolicVar(2))}
            {U254::push_verification_meta(MetaType::SymbolicVar(1))}
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            {G1Projective::roll(2)}
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

    #[test]
    fn check_stark_hint() {
        pre_process("../data/stark/hint.bs");
        let mut builder = ConstraintBuilder::new();
        let depth = 16;
        builder.build_assertion(builder.build_stack_rel(0, builder.build_symbolic(0), RelOp::Eq));
        for i in 1..=depth {
            builder.build_assertion(builder.build_stack_rel(
                i,
                builder.build_symbolic(depth - i + 1),
                RelOp::Eq,
            ));
        }
        let script = script! {
            for i in 0..=depth{
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(i))}
            }
            {OP_HINT()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_is_0_or_1() {
        pre_process("../data/stark/check_0_or_1.bs");
        let mut builder = ConstraintBuilder::new();
        builder.build_assertion(builder.build_or_rel(
            builder.build_rel(
                builder.build_symbolic(0),
                builder.build_constant(0),
                RelOp::Eq,
            ),
            builder.build_rel(
                builder.build_symbolic(0),
                builder.build_constant(1),
                RelOp::Eq,
            ),
        ));
        let script = script! {
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
            {check_0_or_1()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_decompose_positions_gadget() {
        pre_process("../data/stark/decompose_positions_gadget.bs");
        let mut builder = ConstraintBuilder::new();
        let bits = 29;
        let mut expr = builder.build_symbolic(0);
        builder.build_assertion(builder.build_stack_rel(0, expr.clone(), RelOp::Eq));
        for i in 1..=bits {
            expr = builder.build_add_expr(
                builder.build_mul_expr(builder.build_constant(2), expr.clone()),
                builder.build_symbolic(i),
            );
            builder.build_assertion(builder.build_or_rel(
                builder.build_rel(
                    builder.build_symbolic(i),
                    builder.build_constant(0),
                    RelOp::Eq,
                ),
                builder.build_rel(
                    builder.build_symbolic(i),
                    builder.build_constant(1),
                    RelOp::Eq,
                ),
            ));
            if i != bits {
                builder.build_assertion(builder.build_stack_rel(i, expr.clone(), RelOp::Eq));
            }
        }
        builder.build_assertion(builder.build_rel(
            builder.build_symbolic(bits + 1),
            expr.clone(),
            RelOp::Eq,
        ));
        let script = script! {
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(bits+1))}
            for i in (1..=bits).rev(){
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(i))}
            }
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
            {decompose_positions_gadget(bits as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_skip_one_and_extract_bits_gadget() {
        pre_process("../data/stark/skip_one_and_extract_bits_gadget.bs");
        let mut builder = ConstraintBuilder::new();
        let bits = 29;
        let mut expr = builder.build_symbolic(0);
        for i in 1..=bits + 1 {
            expr = builder.build_add_expr(
                builder.build_mul_expr(builder.build_constant(2), expr.clone()),
                builder.build_symbolic(i),
            );
            builder.build_assertion(builder.build_or_rel(
                builder.build_rel(
                    builder.build_symbolic(i),
                    builder.build_constant(0),
                    RelOp::Eq,
                ),
                builder.build_rel(
                    builder.build_symbolic(i),
                    builder.build_constant(1),
                    RelOp::Eq,
                ),
            ));
        }
        builder.build_assertion(builder.build_rel(
            builder.build_symbolic(bits + 2),
            expr.clone(),
            RelOp::Eq,
        ));
        let script = script! {
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(bits+2))}
            for i in (1..=bits+1).rev(){
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(i))}
            }
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
            {skip_one_and_extract_bits_gadget(bits as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_qm31_reverse() {
        pre_process("../data/stark/qm31_reverse.bs");
        let mut builder = ConstraintBuilder::new();
        builder.build_assertion(builder.build_stack_rel(0, builder.build_symbolic(0), RelOp::Eq));
        builder.build_assertion(builder.build_stack_rel(1, builder.build_symbolic(1), RelOp::Eq));
        builder.build_assertion(builder.build_stack_rel(2, builder.build_symbolic(2), RelOp::Eq));
        builder.build_assertion(builder.build_stack_rel(3, builder.build_symbolic(3), RelOp::Eq));
        let script = script! {
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(1))}
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(2))}
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(3))}
            {qm31_reverse()}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_copy_to_altstack_top_item_first_in_gadget() {
        pre_process("../data/stark/copy_to_altstack_top_item_first_in_gadget.bs");
        let mut builder = ConstraintBuilder::new();
        let depth = 10;
        for i in 0..depth {
            builder.build_assertion(builder.build_alt_stack_rel(
                i,
                builder.build_symbolic(i),
                RelOp::Eq,
            ));
        }
        let script = script! {
            for i in 0..depth{
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(i))}
            }
            {copy_to_altstack_top_item_first_in_gadget(depth)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_m31_vec_from_bottom_gadget() {
        pre_process("../data/stark/m31_vec_from_bottom_gadget.bs");
        let mut builder = ConstraintBuilder::new();
        let len = 32;
        for i in 0..len {
            builder.build_assertion(builder.build_stack_rel(
                i,
                builder.build_symbolic(i + 10),
                RelOp::Eq,
            ));
        }
        for i in 0..10 {
            builder.build_assertion(builder.build_stack_rel(
                i + len,
                builder.build_symbolic(i),
                RelOp::Eq,
            ));
        }
        let script = script! {
            for i in (0..len+10).rev(){
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(i))}
            }
            {m31_vec_from_bottom_gadget(len)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_dup_m31_vec_gadget() {
        pre_process("../data/stark/dup_m31_vec_gadget.bs");
        let mut builder = ConstraintBuilder::new();
        let len = 32;
        for i in 0..len {
            builder.build_assertion(builder.build_stack_rel(
                i,
                builder.build_symbolic(i),
                RelOp::Eq,
            ));
        }
        for i in 0..len {
            builder.build_assertion(builder.build_stack_rel(
                i + len,
                builder.build_symbolic(i),
                RelOp::Eq,
            ));
        }
        let script = script! {
            for i in (0..len).rev(){
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(i))}
            }
            {dup_m31_vec_gadget(len)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_limb_to_le_bits() {
        pre_process("../data/stark/limb_to_le_bits.bs");
        let mut builder = ConstraintBuilder::new();
        let limb_size = 29;
        for i in 0..limb_size {
            builder.build_assertion(builder.build_stack_rel(
                i,
                builder.build_bit_of_symbolic(0, i as u128),
                RelOp::Eq,
            ));
        }

        let mut index = 0;

        let script = script! {
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
            {
                builder.dump_assumption(
                    builder.build_and_rel(
                        builder.build_rel(
                            builder.build_symbolic(0),
                            builder.build_constant(1 << limb_size),
                            RelOp::Lt,
                        ),
                        builder.build_rel(
                            builder.build_symbolic(0),
                            builder.build_constant(0),
                            RelOp::Ge,
                        ),
                    ),
                    &mut index,
                )
            }
            {limb_to_le_bits_stark(limb_size as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_limb_to_be_bits_toaltstack_common() {
        pre_process("../data/stark/limb_to_be_bits_toaltstack_common.bs");
        let mut builder = ConstraintBuilder::new();
        let limb_size = 29;
        for i in 2..limb_size {
            builder.build_assertion(builder.build_alt_stack_rel(
                i - 2,
                builder.build_bit_of_symbolic(0, i as u128),
                RelOp::Eq,
            ));
        }
        for i in 0..2 {
            builder.build_assertion(builder.build_stack_rel(
                i,
                builder.build_bit_of_symbolic(0, 1 - i as u128),
                RelOp::Eq,
            ));
        }

        let mut index = 0;

        let script = script! {
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
            {
                builder.dump_assumption(
                    builder.build_and_rel(
                        builder.build_rel(
                            builder.build_symbolic(0),
                            builder.build_constant(1 << limb_size),
                            RelOp::Lt,
                        ),
                        builder.build_rel(
                            builder.build_symbolic(0),
                            builder.build_constant(0),
                            RelOp::Ge,
                        ),
                    ),
                    &mut index,
                )
            }
            {limb_to_be_bits_toaltstack_common(limb_size as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_limb_to_be_bits_toaltstack_except_lowest_1bit() {
        pre_process("../data/stark/limb_to_be_bits_toaltstack_except_lowest_1bit.bs");
        let mut builder = ConstraintBuilder::new();
        let limb_size = 29;
        for i in 1..limb_size {
            builder.build_assertion(builder.build_alt_stack_rel(
                i - 1,
                builder.build_bit_of_symbolic(0, i as u128),
                RelOp::Eq,
            ));
        }

        let mut index = 0;

        let script = script! {
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
            {
                builder.dump_assumption(
                    builder.build_and_rel(
                        builder.build_rel(
                            builder.build_symbolic(0),
                            builder.build_constant(1 << limb_size),
                            RelOp::Lt,
                        ),
                        builder.build_rel(
                            builder.build_symbolic(0),
                            builder.build_constant(0),
                            RelOp::Ge,
                        ),
                    ),
                    &mut index,
                )
            }
            {limb_to_be_bits_toaltstack_except_lowest_1bit(limb_size as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_limb_to_be_bits_toaltstack_except_lowest_2bits() {
        pre_process("../data/stark/limb_to_be_bits_toaltstack_except_lowest_2bits.bs");
        let mut builder = ConstraintBuilder::new();
        let limb_size = 29;
        for i in 2..limb_size {
            builder.build_assertion(builder.build_alt_stack_rel(
                i - 2,
                builder.build_bit_of_symbolic(0, i as u128),
                RelOp::Eq,
            ));
        }

        let mut index = 0;

        let script = script! {
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(0))}
            {
                builder.dump_assumption(
                    builder.build_and_rel(
                        builder.build_rel(
                            builder.build_symbolic(0),
                            builder.build_constant(1 << limb_size),
                            RelOp::Lt,
                        ),
                        builder.build_rel(
                            builder.build_symbolic(0),
                            builder.build_constant(0),
                            RelOp::Ge,
                        ),
                    ),
                    &mut index,
                )
            }
            {limb_to_be_bits_toaltstack_except_lowest_2bits(limb_size as u32)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_verify() {
        pre_process("../data/stark/verify.bs");
        let mut builder = ConstraintBuilder::new();
        let mut index = 0;
        let logn = 12 - 1;
        let mut expr: ValueExpr = builder.build_symbolic(2 * logn + 1);
        for i in 0..logn {
            expr = builder.build_if_expr(
                builder.build_rel(
                    builder.build_symbolic(logn - 1 - i),
                    builder.build_constant(1),
                    RelOp::Eq,
                ),
                builder.build_sha256(
                    builder.build_app_expr(builder.build_symbolic(2 * logn - i), expr.clone()),
                ),
                builder.build_sha256(
                    builder.build_app_expr(expr, builder.build_symbolic(2 * logn - i)),
                ),
            )
        }
        builder.build_assertion(builder.build_rel(expr, builder.build_symbolic(logn), RelOp::Eq));
        let script = script! {
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(logn))} // root_hash
            OP_TOALTSTACK
            for i in 0..logn{
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(i))}
                {
                    builder.dump_assumption(
                        builder.build_or_rel(
                            builder.build_rel(
                                builder.build_symbolic(i),
                                builder.build_constant(1),
                                RelOp::Eq,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(i),
                                builder.build_constant(0),
                                RelOp::Eq,
                            ),
                        ),
                        &mut index,
                    )
                }
                OP_TOALTSTACK
            }
            for i in logn+1..2*logn+1{
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(i))}
            }
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(2*logn+1))} // left & right hash
            {verify(logn)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }

    #[test]
    fn check_query_and_verify_internal() {
        pre_process("../data/stark/query_and_verify_internal.bs");
        let mut builder = ConstraintBuilder::new();
        let mut index = 0;
        let len = 4;
        let logn = 12 - 1;
        let mut expr: ValueExpr = builder.build_symbolic(2 * logn + 1);
        for i in 0..logn {
            expr = builder.build_if_expr(
                builder.build_rel(
                    builder.build_symbolic(logn - 1 - i),
                    builder.build_constant(1),
                    RelOp::Eq,
                ),
                builder.build_sha256(
                    builder.build_app_expr(builder.build_symbolic(2 * logn - i), expr.clone()),
                ),
                builder.build_sha256(
                    builder.build_app_expr(expr, builder.build_symbolic(2 * logn - i)),
                ),
            )
        }
        builder.build_assertion(builder.build_rel(expr, builder.build_symbolic(logn), RelOp::Eq));
        let script = script! {
            {U254::push_verification_meta(MetaType::SingleSymbolicVar(logn))} // root_hash
            OP_TOALTSTACK
            for i in 0..logn{
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(i))}
                {
                    builder.dump_assumption(
                        builder.build_or_rel(
                            builder.build_rel(
                                builder.build_symbolic(i),
                                builder.build_constant(1),
                                RelOp::Eq,
                            ),
                            builder.build_rel(
                                builder.build_symbolic(i),
                                builder.build_constant(0),
                                RelOp::Eq,
                            ),
                        ),
                        &mut index,
                    )
                }
                OP_TOALTSTACK
            }
            for i in 2*logn+1 ..2*logn+len{
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(i))}
            }
            for i in 2*logn+len..2*logn+2*len{
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(i))}
            }
            for i in logn+1..2*logn+1{
                {U254::push_verification_meta(MetaType::SingleSymbolicVar(i))}
            }
            {query_and_verify_internal(len,logn)}
            {add_assertions(&builder)}
        };
        dump_script(&script);
    }
}
