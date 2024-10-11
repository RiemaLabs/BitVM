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
    Assertion(String),
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::bigint::{U254, U64};
    use crate::pseudo::push_to_stack;
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
        }
    }
    fn pre_process() {
        // empty the file for process
        unsafe {
            let bs_path = BS_FILE_PATH.as_ref().expect("BS_FILE_PATH is not set");
            let verified_path = VERIFED_FILE_PATH
                .as_ref()
                .expect("VERIFED_FILE_PATH is not set");
            File::create(bs_path).ok();
            File::create(verified_path).ok();
        }
    }
    fn dump_script(script: &Script, path: &str) {
        set_filepath(path);
        pre_process();
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

    #[test]
    fn check_is_zero() {
        let script = script! {
            { U254::push_verification_meta(MetaType::SymbolicVar(0)) }
            { U254::is_zero(0) }
        };
        dump_script(&script, "../data/is_zero.bs");
    }

    #[test]
    fn check_push_one() {
        let script = script! {
            { push_to_stack(0,(U254::N_LIMBS - 1) as usize) }
            1
            // TODO : Add Assertion for the top limbs of stack  is 1.
        };
        dump_script(&script, "../data/push_one.bs");
    }

    #[test]
    fn check_push_zero() {
        let script = push_to_stack(0, U254::N_LIMBS as usize);
        // TODO : Add Assertion for the top limbs of stack is 0.
        dump_script(&script, "../data/push_zero.bs");
    }

    #[test]
    fn check_drop() {
        let script = script! {
            {U254::push_verification_meta(MetaType::SymbolicVar(0))}
            for _ in 0..U254::N_LIMBS / 2 {
                OP_2DROP
            }
            if U254::N_LIMBS & 1 == 1 {
                OP_DROP
            }
            // TODO : Add Assertion for the symbolic variable is truly dropped.
        };
        dump_script(&script, "../data/drop.bs");
    }

    #[test]
    fn check_is_negative() {
        let depth = 0;
        let script = script! {
            { U254::push_verification_meta(MetaType::SymbolicVar(0)) }
            { (1 + depth) * U254::N_LIMBS - 1 } OP_PICK
            { U254::HEAD_OFFSET >> 1 }
            OP_GREATERTHANOREQUAL
            // TODO : Add Assertion for checking symbolic whether < 0.
        };
        dump_script(&script, "../data/is_negative.bs");
    }

    #[test]
    fn print_is_positive() {
        let depth = 0;
        let script = script! {
            { U254::push_verification_meta(MetaType::SymbolicVar(0)) }
            { U254::is_zero_keep_element(depth) } OP_NOT
            { (1 + depth) * U254::N_LIMBS } OP_PICK
            { U254::HEAD_OFFSET >> 1 }
            OP_LESSTHAN OP_BOOLAND
            // TODO : Add Assertion for checking symbolic whether < 0.
        };
        dump_script(&script, "../data/is_positive.bs");
    }

    #[test]
    fn check_zip() {
        let a = 1;
        let b = 0;
        let script = U254::zip(a, b);
        dump_script(&script, "../data/zip.bs");
    }

    #[test]
    fn test_less_than() {
        let num_a: u64 = 0x00000000000000FF;
        let num_b: u64 = 0xFF00000000000000;
        let script = script! {
            {U64::push_u64_le(&[num_a])}
            {U64::push_u64_le(&[num_b])}
            {U64::lessthan(1, 0)}
        };
        dump_script(&script, "../data/test_less_than.bs");
    }
}
