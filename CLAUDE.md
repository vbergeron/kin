# Kin

Kin is a Datalog-style language where a type is a relation. The language is
specified in `docs/core-spec.md`; this repository is its Rust implementation.

## Language design guidelines

When changing or extending the language (spec or implementation):

- **Minimize language structure and complexity.** Fewer constructs, fewer
  special cases, fewer grammar rules.
- **Prefer the more generic and expressive structure** over a dedicated one:
  reuse an existing construct (relations, terms, membership `t : T`) before
  introducing a new one.
- **Avoid keywords.** Prefer punctuation and position over reserved words.
  The only reserved name is the primitive type `symbol`; it must stay the
  only one.

## Development

```sh
cargo fmt --all --check
cargo clippy --all-targets -- -D warnings
cargo test
```
