# Kin

Kin is a Datalog-style logic language in which **a type is a relation**:
checking a term against `T` means deciding membership of that term in the
extension of the relation `T`.

```prolog
#person(symbol).
person(alice).
person(bob).

#parent(person, person).
parent(alice, bob).
```

The language core is specified in [`docs/core-spec.md`](docs/core-spec.md).
This repository is its Rust implementation.

## Layout

| Path            | Spec | Purpose                                             |
| --------------- | ---- | --------------------------------------------------- |
| `src/syntax.rs` | §2   | AST and parser                                      |
| `src/term.rs`   | §3   | Equality, unification, desugaring                   |
| `src/classify.rs` | §5 | Dependency graph, STATIC/DYNAMIC classification     |
| `src/termination.rs` | §6 | Structural decrease, tabling, Datalog-safety   |
| `src/typing.rs` | §4   | Arity matching, spec conformance, generics          |
| `src/infer.rs`  | §7   | Positional type inference                           |
| `src/bin/kin.rs`| —    | Command-line checker                                |
| `examples/`     | —    | Sample Kin programs                                 |

## Development

```sh
cargo build
cargo test
cargo fmt --all --check
cargo clippy --all-targets -- -D warnings
cargo run -- examples/family.kin
```
