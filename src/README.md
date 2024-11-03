# Writing Specifications for BitVM Using Constraint Builders and Expression Trees

This tutorial provides a step-by-step guide on how to write specifications for BitVM using a custom scripting `dump.rs` in Rust. We will focus on the core functionalities of the provided codebase, including the `ConstraintBuilder`, `ValueExpr`, and `BoolExpr` classes, to build and manipulate expression trees that define constraints and assertions within the BitVM environment.

## Table of Contents

- [Writing Specifications for BitVM Using Constraint Builders and Expression Trees](#writing-specifications-for-bitvm-using-constraint-builders-and-expression-trees)
    - [Table of Contents](#table-of-contents)
    - [Introduction](#introduction)
    - [Overview of Key Components](#overview-of-key-components)
        - [ConstraintBuilder](#constraintbuilder)
    - [Writing a Specification: An Example](#writing-a-specification-an-example)
        - [Step 1: Pre-processing](#step-1-pre-processing)
        - [Step 2: Building Assumptions (Optional)](#step-2-building-assumptions-optional)
        - [Step 3: Building Assertions](#step-3-building-assertions)
        - [Step 4: Constructing the Script](#step-4-constructing-the-script)
        - [Step 5: Dumping the Script](#step-5-dumping-the-script)
    - [Notation](#notation)

## Introduction

BitVM is a virtual machine that enables complex computations on Bitcoin's blockchain through the use of off-chain computation and on-chain verification. Writing specifications for BitVM involves defining constraints or loop invariants within the bitcoin script.

This tutorial aims to demonstrate how to use a custom Rust scripting approach to write these specifications effectively. By leveraging the `ConstraintBuilder`, we can construct complex logical statements that represent the desired behavior of our BitVM programs.

## Overview of Key Components

### ConstraintBuilder

The `ConstraintBuilder` is a core class used to construct complicate constraints and assertions. It supports various types of expressions and relations, which is then parsed by `Pomelo`.

## Writing a Specification: An Example

We will walk through an example that demonstrates how to use the provided classes and methods to write a specification for BitVM. The example focuses on checking the conversion of bytes to big integers (`from_bytes` function).

```rust
#[test]
fn check_from_bytes() {
    pre_process("../data/bigint/bits/from_bytes.bs");
    let mut builder = ConstraintBuilder::new();

    // Step 1: Building Assumptions
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

    // Step 2: Building Assertions
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

    // Step 3: Constructing the Script
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
```

### Step 1: Pre-processing

Before building constraints, we call the `pre_process` function to set up the environment and specify the output file path for the generated script.

```rust
pre_process("../data/bigint/bits/from_bytes.bs");
```

### Step 2: Building Assumptions (Optional)

We loop through indices to create assumptions about symbolic variables, ensuring they are within the range `[0, 255]`.

```rust
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
```

Here, `builder.build_symbolic(i)` creates a symbolic variable, and we assert that each variable `v_i` satisfies `0 ≤ v_i ≤ 255`.

### Step 3: Building Assertions

We construct assertions to ensure that the stack values correspond to the computed expressions from the symbolic variables.

```rust
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
```

In this code:

- We initialize `expr` as zero.
- For each limb `i`, we build an expression that accumulates the weighted sum of symbolic variables.
- We assert that the value on the stack at position `i` equals this accumulated expression.

### Step 4: Constructing the Script

We create a script that combines the assumptions, the BitVM function call, and the assertions.

```rust
let script = script! {
    for i in (0..4*U254::N_LIMBS).rev(){
        {U254::push_verification_meta(MetaType::SingleSymbolicVar(i as usize))}
    }
    {add_assumptions(&builder)}
    {U254::from_bytes()}
    {add_assertions(&builder)}
};
```

- We push the symbolic variables onto the stack in reverse order.
- We add all the assumptions and assertions to the script.
- We call the `from_bytes` function of `U254`, which performs the byte-to-integer conversion.

### Step 5: Dumping the Script

Finally, we output the script to the specified file for further processing.

```rust
dump_script(&script);
```

## Notation

1. **SingleSymbolicVar**: Pushing a `SingleSymbolicVar` to the stack occupies only one stack element.

2. **SymbolicVar**: When using a general `SymbolicVar`, pushing the symbolic variable to the stack corresponds to `N_LIMBS` stack elements. This represents pushing a large integer onto the stack in little-endian order, where the limb containing the least significant bits (LSB) is at the top of the stack.

3. **SymbolicVar and SingleSymbolicVar Counters**: Both `SymbolicVar` and `SingleSymbolicVar` share the same counter. When referencing a `SymbolicVar`, corresponding to the syntactic sugar in Pomelo, each limb that constitutes the large integer is multiplied by its respective positional weight (e.g., in binary, the \( n \)-th bit is multiplied by \( 2^n \)). The sum of these products yields the value of the symbolic variable.

4. **Reference Expressions**:
    - **RefSymbolLimb**: Generates a reference to a specific limb of a large integer symbolic variable. Here, `limb[0]` contains the LSB, and `limb[N_LIMBS-1]` contains the most significant bits (MSB).
    - **RefSymbolLimbBit**: Represents a specific bit within a limb of a symbolic variable.
    - **RefStack**: Corresponds to elements within the main stack.
    - **RefAltStack**: Corresponds to elements within the auxiliary stack.