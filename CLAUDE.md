# CLAUDE.md

 <!-- LTeX: enabled=false -->

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Verus tutorial project demonstrating formal verification of Rust code. Verus is a verification system that allows writing specifications and proofs alongside Rust implementation code to mathematically prove correctness properties.

## Build and Development Commands

- **Build**: `cargo build`
- **Run**: `cargo run` (executes main function from src/main.rs)
- **Check verification**: `verus` (if Verus toolchain is installed)
- **Clean**: `cargo clean`

## Architecture

The codebase is organized into several modules demonstrating different Verus verification patterns:

### Core Modules

- **src/main.rs**: Main entry point containing examples of factorial implementations, increment functions, and octuple operations with Verus specifications
- **src/triangle.rs**: Comprehensive triangle number implementations showing various approaches (recursive, tail-recursive, mutable, loop-based) with formal proofs
- **src/ae.rs**: Abstract syntax tree evaluator for arithmetic expressions (Add, Sub, Num) with verified evaluation functions
- **src/octuple.rs**: Simple octuple function examples with preconditions and postconditions
- **src/octuple/**: Modular examples showing specification reuse across modules
  - **m1.rs**: Defines `min` function specification and lemmas
  - **m2.rs**: Imports and uses `min` properties without implementation details

### Verus Patterns

The codebase demonstrates key Verus verification patterns:

1. **Specification Functions**: `spec fn` declarations that define mathematical properties (e.g., `triangle`, `fact`, `eval_spec`)
2. **Executable Functions**: `fn` with `requires`/`ensures` clauses that implement verified behavior
3. **Proof Functions**: `proof fn` that establish mathematical properties and lemmas
4. **Loop Invariants**: While loops with `invariant` and `decreases` clauses for termination proofs
5. **External Bodies**: `#[verifier::external_body]` for functions that interface with unverified code
6. **Assert By**: `assert(...) by { ... }` blocks for guided proof assistance

### Verification Approaches

- **Multiple implementations**: Same functionality implemented recursively, with loops, and tail-recursively
- **Overflow handling**: Careful bounds checking with preconditions like `triangle(n as nat) < 0x1_0000_0000`
- **Monotonicity proofs**: Helper lemmas like `triangle_is_monotonic` to assist overflow verification
- **Type conversion**: Bridging between machine integers (`i32`, `u32`) and mathematical integers (`int`, `nat`)

## Key Dependencies

- **vstd::prelude::***: Verus standard library providing verification primitives
- **builtin**: Core Verus verification constructs
- Standard Rust Cargo project structure without external crates
