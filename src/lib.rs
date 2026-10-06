//! Kin — a Datalog-style language in which a type *is* a relation.
//!
//! The crate follows the pipeline of the core spec (`docs/core-spec.md`),
//! one module per stage, in the spec's suggested implementation order:
//!
//! 1. [`syntax`]      — §2: abstract syntax and parser.
//! 2. [`term`]        — §3: structural equality, unification, desugaring.
//! 3. [`classify`]    — §5: dependency graph and STATIC/DYNAMIC classification.
//! 4. [`termination`] — §6: structural decrease and Datalog-safety checks.
//! 5. [`typing`]      — §4: arity matching, spec conformance, membership.
//! 6. [`infer`]       — §7: positional type inference.

pub mod classify;
pub mod infer;
pub mod syntax;
pub mod term;
pub mod termination;
pub mod typing;
