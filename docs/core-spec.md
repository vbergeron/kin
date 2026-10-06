# Kin — Core Language (Implementation Note)

Sep 18, 2026 · @Valentin

## 1. Status of this note

This document specifies the **minimal core** of Kin: terms, clauses (specs, facts, rules), and the typing discipline built on top of them. Anything a relation might do beyond this — reach outside the language, carry a proof obligation, be asked as a query — is out of scope for this note. It is written for implementers; familiarity with Datalog evaluation and structural recursion (Rocq/Coq `Fixpoint`) is assumed.

**Scope note.** The grammar (§2) describes Kin's term and clause syntax in general — it is not type-specific. A type annotation's right-hand side (`TypeExpr`, §2.1) is an ordinary term drawn from the same grammar as a fact's arguments; typing (§4–§7) is a discipline layered on top of that one term language, not a separate syntactic category. Reading §2 as "the type grammar" would be a misreading: it is Kin's whole clause-level syntax.

**Design invariant.** In Kin, a type *is* a relation. There is no separate kind of "type", no record/struct sort, no lattice of constraints. Type-checking a term against `T` reduces to deciding membership of that term in the extension of the relation `T`. §4–§7 specify exactly when that membership question is well-formed and decidable, and how it is decided.

Requirements are stated with RFC 2119 keywords (MUST, MUST NOT, SHOULD, MAY).

## 2. Terms — abstract syntax and grammar

### 2.1 Abstract syntax

```
Ident    ::= lowercase-initial identifier   (atom / functor)
VarName  ::= uppercase-initial identifier   (logic variable)

Term ::= TermCore (':' TypeExpr)?    -- annotation, an escape hatch, on any term

TermCore ::= Var
           | Atom
           | Tuple(Term, ..., Term)      -- arity ≥ 2, anonymous constructor
           | Compound(Ident, Term*)      -- named constructor, e.g. cons(H, T)
           | ListNil                     -- []
           | ListCons(Term, Term)        -- [H|T], sugar for cons(H, T)

TypeExpr ::= Ident Args?            -- a relation name, optionally applied
           | Ident                  -- unapplied generic parameter

Args ::= '(' Term (',' Term)* ')'

Spec ::= '#' Ident GenericParams? '(' TypeExpr (',' TypeExpr)* ')'
```

A `Var` unifies structurally; an `Atom` is a 0-arity `Ident` used as a value, distinguished from a relation name only by position (relation names occur as the functor of a `Compound` in body position; atoms occur as arguments).

### 2.2 Concrete grammar (PEG)

Operator precedence, whitespace and comments are elided for brevity; `~` denotes an ordered choice, `<-` a rule.

```peg
Program     <- Spacing Clause* EndOfFile

Clause      <- Spec
             / Head '.'
             / Head ':-' Body '.'

Spec        <- '#' Functor GenericParams? '(' TypeTerm (',' TypeTerm)* ')' '.'

Head        <- Functor GenericParams? '(' TermList? ')'
GenericParams <- '(' Ident (',' Ident)* ')'

Body        <- Compound (',' Compound)*

TermList    <- Term (',' Term)*

Term        <- TermCore (':' TypeTerm)?        -- annotation, an escape hatch (§7.2), on any term
TermCore    <- Compound
             / Tuple
             / ListTerm
             / Var
             / Atom

TypeTerm    <- Ident ('(' TermList? ')')?       -- bare, or applied to arguments

Compound    <- Functor '(' TermList? ')'
Tuple       <- '(' Term ',' Term (',' Term)* ')'

ListTerm    <- '[' ']'
             / '[' Term (',' Term)* ('|' Term)? ']'

Functor     <- Ident
Var         <- [A-Z_][A-Za-z0-9_]* Spacing
Ident       <- [a-z][A-Za-z0-9_]* Spacing
Atom        <- Ident

Spacing     <- (Space / Comment)*
Comment     <- '%' (!EndOfLine .)* EndOfLine
Space       <- ' ' / '\t' / EndOfLine
EndOfLine   <- '\r\n' / '\n' / '\r'
EndOfFile   <- !.
```

Notes on the grammar:

- `Tuple` requires **arity ≥ 2** (`(X, Z)`), so that a single parenthesised term (`(X)`) is not ambiguous with a grouping parenthesis. Kin's core grammar has no grouping parenthesis for terms outside `Tuple`/`Compound`, so this ambiguity does not otherwise arise.
- `ListTerm` is pure sugar: `[]` desugars to the atom `nil`; `[H|T]` desugars to `cons(H, T)`; `[A, B, C]` desugars to `cons(A, cons(B, cons(C, nil)))`. Desugaring MUST happen before type-checking (§4) and before the structural-decrease check (§6); neither rule has special-case knowledge of list syntax.
- `GenericParams` is the second, separate argument list of a generic definition (`list(A)(head: A, tail: list(A))`). It is syntactically distinct from the head's `TermList` precisely so that a generic parameter is never confused with an ordinary field.
- **Case is a convention, not a grammatical distinction, for relation names.** `Ident` matching — between a `Spec`'s functor, its facts' and rules' head functors (§4.5), and any occurrence of a relation name in `TypeTerm` position — is **case-insensitive**. By convention, authors capitalize a relation's spelling when it is referenced as a type (a `Spec`'s own functor, and any `TypeTerm` occurrence, e.g. `x: Person`, `list(A)`) and use lowercase when it is referenced as a callable predicate (fact and rule heads, body literals, e.g. `person(alice).`). `Person` and `person` denote the identical relation; this convention carries no grammatical consequence and is never required. `Var` is unaffected — it is distinguished from a case-insensitively-read `Ident` by grammatical position, not by case, since `Var` never occurs where a `TypeTerm` or a `Head`/`Compound` functor is expected.

## 3. Term semantics

§2 fixes the syntax of terms; this section fixes their meaning, independent of typing. Every later section (§4 typing, §5 stratification, §6 termination, §7 inference) is stated over these definitions.

### 3.1 Structural equality and unification

Two ground terms (no free variables) are equal iff they have the same shape recursively:

```
eq(Atom a, Atom b)               = (a = b as identifiers)
eq(Compound(f, [t1..tn]), Compound(g, [u1..un])) = (f = g) ∧ (n = m) ∧ ∀i. eq(ti, ui)
eq(_, _)                          = false   -- different shapes, incl. different arity
```

A `Tuple` and `ListCons` are Compounds under this definition once desugared (§3.2) — equality never needs a separate case for them.

Unification of two (possibly open) terms `t`, `u` under a substitution `σ` follows the same structural recursion, with a `Var` case added: a variable unifies with anything by extending `σ`, subject to the occurs check (a variable MUST NOT unify with a term that structurally contains it, which would produce an infinite term). Kin's core does not admit infinite terms; the occurs check MUST be enforced, not optionally skipped for performance as some Prolog systems do.

### 3.2 Desugaring

Desugaring is a total, syntax-directed function `desugar : Term → Term`, applied once after parsing and before any semantic rule (typing, stratification, termination, inference) sees a term:

```
desugar(ListNil)            = Atom(nil)
desugar(ListCons(h, t))     = Compound(cons, [desugar(h), desugar(t)])
desugar(Tuple(t1, ..., tn)) = Compound(tuple/n, [desugar(t1), ..., desugar(tn)])
desugar(Compound(f, ts))    = Compound(f, map(desugar, ts))
desugar(t)                  = t                         -- Var, Atom: unchanged
```

`tuple/n` names the anonymous constructor of arity `n` (§2.2's `Tuple` production); it is not a user-writable identifier (excluded from `Ident` by convention, since `Ident` is lowercase-initial and `tuple/n` is reserved per arity). Every later section operates on `desugar(t)`, never on the surface form — in particular, the subterm order `⊏` (§6.1) and the arity-matching judgment (§4.1) are defined over desugared terms, which is why neither needs a case for list or tuple syntax specifically.

### 3.3 Ground vs. open terms

A term is **ground** if it contains no `Var`; otherwise it is **open**. `Ext(R)`, the extension of a relation `R` (§5.2 onward), is a set of ground terms by construction — a fact or a derived tuple is always fully instantiated. A rule body may contain open terms (its variables), resolved to ground instances during evaluation or during a membership query (§6.4); typing (§4) and inference (§7) both operate over open terms, since they run before any particular substitution is chosen.

## 4. Types as relations — the typing judgment

### 4.1 Arity-matching rule

The sole typing rule of Kin's core is:

```
Γ ⊢ t : R
────────────────────────────────────────────
left(t) has arity n  ⇔  arity(R) = n
R is statically computable (§5) and terminating (§6)
member(desugar(t), Ext(R))  holds
```

where `left(t)` is the shape of the annotated term:

| Term shape `t` | `left(t)` arity |
| --- | :-: |
| bare atom / variable `x` | 1 |
| tuple `(a, ..., z)` (k elems) | k |
| compound `f(a, ..., z)` (k args) | — (see §4.2) |

A bare term (atom or variable, arity 1) MUST only be checked against a unary relation. A tuple of arity *k* MUST only be checked against a *k*-ary relation. There is no implicit coercion between the two.

```prolog
X: Person                    % arity 1 — Person must be unary
(X, Z): Grandparent          % arity 2 — Grandparent must be binary
(X, Y, Z): SomeTernary       % arity 3
```

An arity mismatch (e.g. `X: Grandparent` with `Grandparent/2`) MUST be rejected at compile time.

### 4.2 Annotation inside constructed terms

An annotation `field: T` MAY occur recursively inside a compound term, not only at the head argument position. In that position it types a single **field of the constructor**, not the constructor's own overall arity — the constructor itself is not being checked against `T`, one of its arguments is:

```prolog
list(A)(nil).
list(A)(cons(H: A, T: list(A))).
```

Here `H: A` types the first field of `cons/2` against the (possibly generic) unary relation `A`; `T: list(A)` types the second field against the instantiated relation `list(A)`. Both are ordinary arity-1 judgments per §4.1 — `A` and `list(A)` are each unary — nested inside the compound rather than applied to it.

### 4.3 Generic instantiation

A generic parameter `A` (introduced via `GenericParams`, §2.2) ranges only over relations, not over terms. At the point of instantiation (e.g. `list(Person)`), `A` MUST be substituted textually by the supplied relation before any annotation inside the body is checked — instantiation is **monomorphisation**, never a runtime call to a higher-order relation value. After substitution, every annotation reduces to an ordinary arity-1 or arity-*k* judgment per §4.1–4.2, checked against the concrete relation.

### 4.4 Spec conformance

Let `R` be a relation with spec `#R(T_1, ..., T_n).` For every clause of `R` — fact or rule — with head `R(v_1, ..., v_n)`:

```
∀i ∈ 1..n:  v_i : T_i
```

MUST hold, checked by §4.1's arity-matching judgment applied to each `v_i` against `T_i` positionally — no field names are involved (§4.5), only position. This is not an additional mechanism — it is §4.1 applied once per head argument rather than once at an isolated annotation site. A clause that fails this check MUST be rejected at compile time, citing the argument position and the spec it violates.

This is the rule that gives a spec its force: `#parent(person, person).` would otherwise be a declaration with no consequence, since §4.1 alone only says how to check a term *explicitly* written with a `:` annotation — it says nothing about facts or rule heads, which carry no `:` at all. §4.4 is what makes `parent(alice, bob).` (§8) actually checked, position by position, against `#parent(person, person).`, rather than merely resembling it.

A spec is now **mandatory** for every relation (§4.5) — there is no unconstrained case to handle. §7's inference algorithm may therefore assume `R.spec` exists for every `R` it looks up, without a fallback branch.

### 4.5 Relations and specs

A **relation** is a maximal contiguous run of clauses in the program sharing one functor: exactly one `Spec` (§2.2), immediately followed by zero or more `Head '.'` facts and `Head ':-' Body '.'` rules for that same functor, with no clause of any other relation interleaved.

```prolog
#parent(person, person).
parent(alice, bob).
parent(bob, carol).
```

Three requirements this imposes, none of them optional:

1. **A spec is mandatory.** Every relation MUST open with a `Spec`; a `Head '.'` or `Head ':-' Body '.'` clause whose functor has no preceding `Spec` MUST be rejected at compile time. This closes the gap left open in §4.4: `R.spec` is never absent, so §7's inference algorithm needs no fallback for an unconstrained relation.
2. **The spec MUST precede its clauses**, and MUST be unique per functor. A second `Spec` for a functor already opened elsewhere in the program — whether identical or contradictory — MUST be rejected, citing both locations.
3. **The spec fixes the relation's arity.** `arity(R)`, used throughout §4.1's arity-matching judgment and §6's structural-decrease check, is defined as the number of `TypeTerm` entries in `R`'s spec. Every fact and rule head for `R` MUST have exactly that many arguments — an arity mismatch between a clause and its relation's own spec is a compile error distinct from (though checked alongside) the arity-matching judgment of §4.1, which governs an argument's *type*, not the head's *arity*.

A relation whose spec is followed by zero clauses is well-formed — its extension is simply empty — and is classified per §5.1 like any other.

### 4.6 Primitive type: `Symbol`

The core provides exactly one primitive type, `Symbol`, denoting an uninterpreted atom — the base case every relation-type eventually rests on. Unlike every other relation, `Symbol` requires no `Spec` (§4.5's mandatory-spec rule has a single, deliberate exception for it) and has no clauses: its extension is not enumerated by classify(G) — it is simply the set of all `Atom` terms (§2.1). It contributes no node to §5.1's dependency graph `G`; any edge naming it is immediately satisfied, since it depends on nothing and is STATIC by fiat, not by derivation.

`Symbol` closes the circularity §8 surfaced: a base enumeration no longer needs to self-reference to have a spec.

```prolog
#person(Symbol).
person(alice).
person(bob).
person(carol).
```

### 4.7 Literal (singleton) types

A particular symbol is its own type: an atom `a` used in `TypeTerm` position, once resolved as neither `Symbol` nor a relation nor a generic parameter (resolution order below), denotes the **literal type** `{a}` — the singleton set containing exactly that atom. Like `Symbol`, a literal type requires no `Spec`, contributes no node to §5.1's graph `G`, and is trivially STATIC: `member(t, {a})` holds iff `desugar(t) = a` exactly (§3.1's structural equality). This is scoped to bare atoms only — a compound term is never itself a type.

```prolog
#status(x: pending).
```

A fact for `status` MUST carry the atom `pending` itself in its argument position, not merely any `Symbol`.

**Resolution order**, for a bare `Ident` (no arguments) occurring in `TypeTerm` position — the ambiguity `TypeTerm <- Ident (...)?` (§2.2) leaves open otherwise, since `Symbol`, a generic parameter, a declared relation and a literal atom are all syntactically just an `Ident`:

1. `Symbol` (§4.6), matched case-insensitively.
2. A generic parameter bound by the enclosing `GenericParams` (§4.3), if the `TypeTerm` occurs inside that generic's own definition.
3. A declared relation, matched case-insensitively against some `Spec` in the program (§2.2's case convention).
4. Otherwise, the literal type naming that exact atom.

Each step is tried only if the previous one fails to match; the first match wins. An `Ident` applied to arguments (`list(A)`, `Grandparent(...)`) skips straight to step 3 — a literal type is never itself parameterised.

## 5. Static computability (stratification)

A relation MAY appear in type position (right of `:`) if and only if it is statically computable: its full extension is determined without recourse to any input unknown at compile time.

### 5.1 Classification algorithm

Build the relation dependency graph `G`: one node per declared relation, and an edge `R → S` whenever either (a) a clause of `R` contains a literal `S(...)` in its body, or (b) `R`'s spec (§4.5) names `S` in a `TypeTerm` position — a relation depends on every relation its own spec is typed against, not only on what its rule bodies call. `Symbol` (§4.6) is not a node of `G`; an edge naming it is trivially satisfied. Classify every node by a single bottom-up pass over `G`'s condensation (its DAG of strongly connected components, SCCs):

```
function classify(G):
    for each SCC C in G, in reverse topological order:
        if any relation in C has no defining clauses:
            mark every relation in C as DYNAMIC
        else if every out-edge from C leads to a relation already marked STATIC:
            mark every relation in C as STATIC
        else:
            mark every relation in C as DYNAMIC
```

A relation with no defining clauses (declared only) MUST be classified DYNAMIC — absence of a body is indistinguishable from an unbounded, unconstrained source, and the core has no way to tell the two apart.

### 5.2 Rule

```
R statically computable  ⇔  classify(R) = STATIC
```

Only a STATIC relation MAY occur in type position. A DYNAMIC relation used in type position MUST be rejected at compile time, citing the dependency edge that introduced dynamism `— the undeclared or clauseless relation reached transitively`.

This is the same SCC/stratification analysis a Datalog engine already performs to order semi-naïve evaluation (§7 of the companion evaluation note); §5 reuses it for a second purpose rather than introducing a separate pass.

## 6. Termination: structural decrease criterion

A STATIC relation that is recursive (its own SCC in §5.1 is non-trivial, or it calls itself directly) MUST additionally pass a structural-decrease check (§6.2, extended by tabling in §6.4) or qualify as Datalog-safe (§6.5) before it is accepted in type position. The structural-decrease check is the standard guard-by-constructor check used by `Fixpoint` in Rocq/Coq, restricted to syntactic pattern matching (no general well-founded measure, no `Function`/`measure` escape hatch — deliberately out of scope for the minimal core).

### 6.1 Subterm order

Define `t ⊏ u` (`t` is a **strict structural subterm** of `u`) as the smallest relation such that, for every compound `f(a_1, ..., a_n)` with `n ≥ 1`, each `a_i ⊏ f(a_1, ..., a_n)`, extended transitively. Tuples and list sugar are included via their desugared form (§2.2): in `cons(H, T)`, `T ⊏ cons(H, T)`. Atoms and variables have no subterms and can only occur as the smaller side of `⊏`.

**A bare tuple `(a, b)` used as a generic recursive argument does not, by itself, decrease** — it has no distinguished constructor to descend into unless it appears as a field of a named compound (`cons`, `nil`, or a user-defined functor). This is the open point already flagged in the main specification (list/tuple unification); §6 applies only where a named constructor is present.

### 6.2 Check

For relation `R` with clauses `R(h_1, ..., h_n) :- L_1, ..., L_m.`:

```
for each clause C of R:
    for each literal L_i in body(C) such that L_i's relation is R
                                      (a recursive call):
        require: ∃ position p such that
                  head_arg[p](C) is a compound, and
                  L_i.arg[p] ⊏ head_arg[p](C)
    if no such p exists for some recursive L_i:
        reject R at compile time
```

In words: at least one argument position must be fixed across the whole relation, such that the head's term at that position is always a compound, and every recursive call's term at that same position is a strict structural subterm of it.

### 6.3 Worked check

```prolog
list(A)(nil).
list(A)(cons(H: A, T: list(A))).
```

Position 1 (the sole argument): head is `cons(H, T)` in the recursive clause; the recursive occurrence is `list(A)(T)`, i.e. the call's argument at position 1 is `T`. Since `T ⊏ cons(H, T)`, the check passes.

A relation with no structurally decreasing position (e.g. one whose only recursive argument is a bare tuple, per §6.1, or an unguarded arithmetic decrement without a Peano encoding) and that is not Datalog-safe (§6.5) MUST be rejected — with a compile error naming the recursive literal that could not be matched to a decreasing position, not a silent non-termination risk deferred to runtime.

### 6.4 Non-enumerative membership

A STATIC, structurally-decreasing relation is not necessarily *finite* (`even/1` is an example). §5 licenses a **memoised membership query**, not full enumeration: `member(t, R)` is decided by unfolding `R`'s clauses only along the structural order fixed by §6.2, which is guaranteed to terminate by construction, with a memo table keyed on `(R, t)` to avoid recomputation (tabling, as in XSB Prolog). The compiler MUST use this algorithm rather than attempting to materialise `Ext(R)` in full whenever `R` is not finite.

### 6.5 Finite-domain (Datalog-safe) termination

A second, independent route exists into type position for a STATIC relation that never satisfies §6.2. A relation is **Datalog-safe** if no clause in its dependency SCC (§5.1) applies a functor to construct a new compound term around a variable bound by a body literal — every argument in every head and body literal is a bare variable or an atom, copied unchanged between positions, never wrapped in a fresh `Compound`, `Tuple`, or `ListCons`.

**Rule.** If `R` is Datalog-safe, and every relation in `R`'s dependency SCC is Datalog-safe, then `Ext(R)` is finite and computable by ordinary bottom-up fixpoint evaluation, independent of §6.2. `R` is usable in type position on this basis alone.

**Justification.** This is the standard finiteness argument for function-symbol-free Datalog: a program that never constructs compound terms has a Herbrand base bounded by the constants already present in its finite extensional facts, so semi-naive evaluation reaches a fixpoint after finitely many iterations, regardless of cycles in the dependency graph. §6.2's structural-decrease check is needed only when a relation's recursion is carried by a growing compound term (§6.3's `list(A)`, §6.4's `even/1`) — there the Herbrand base is genuinely unbounded and finiteness cannot be assumed without it.

**Worked check.**

```prolog
ancestor(X, Z) :- parent(X, Z).
ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z).
```

Every argument in both clauses is a bare variable copied between literals; neither clause constructs a compound term, so `ancestor` is Datalog-safe. Its dependency SCC, `person` and `parent` (§8), are extensional facts and trivially Datalog-safe. `ancestor` therefore qualifies for type position under this rule, without needing to satisfy §6.2 (see §8's worked example).

A STATIC relation need only satisfy one of §6.2 (extended by §6.4) or §6.5; the two routes are disjoint and neither subsumes the other.

## 7. Type inference algorithm

Unannotated variables in a rule body are typed by **position**: the same occurrence-propagation used for ordinary Datalog mode inference, applied here to types instead of bindings.

```
function infer(clause):
    env := {}                                   // Var → TypeExpr
    for each explicit annotation (x: T) in clause.head or clause.body:
        env[x] := unify_type(env[x], T)          // §7.1
    for each literal L(t_1, ..., t_k) in clause.body:
        R := relation(L)
        for i in 1..k:
            if t_i is a Var and env[t_i] undefined:
                env[t_i] := R.spec.param_type[i]
            else if t_i is a Var:
                env[t_i] := unify_type(env[t_i], R.spec.param_type[i])
    return env
```

### 7.1 `unify_type`

Since the core has no constraint lattice (§ deliberately out of scope, see main specification's Notes), `unify_type(T1, T2)` is equality, not a meet:

```
unify_type(T1, T2) =
    T1                  if T1 = T2
    reject               otherwise, citing both occurrences
```

A variable that is typed differently by two occurrences in the same clause body (e.g. two relations whose corresponding positions declare distinct relation names for the same variable) MUST be rejected at compile time. There is no implicit widening, no common supertype search `— the core has no type hierarchy at all`.

### 7.2 Explicit annotation as escape hatch

An explicit annotation always MAY be supplied (`parent(X, Y: Person)`) and is checked, not merely accepted — it participates in `unify_type` exactly like an inferred type, so a wrong explicit annotation is rejected the same way a wrong inference would be. Its only effect is to seed `env` before propagation runs, letting the author document or disambiguate.

## 8. Worked example

```prolog
#person(Symbol).
person(alice).
person(bob).
person(carol).

#parent(person, person).
parent(alice, bob).
parent(bob, carol).

#ancestor(person, person).
ancestor(X, Z) :- parent(X, Z).
ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z).
```

**§5 classification.** `#person(Symbol).` depends only on `Symbol`, which contributes no node to `G` (§4.6) — `person` has no unsatisfied out-edges, so it is STATIC. `parent`'s spec (`#parent(person, person).`) names `person` in `TypeTerm` position — an edge `parent → person` per §5.1(b) — and `person` is already STATIC, so `parent` is STATIC. `ancestor`'s spec names `person` (STATIC) and its rule bodies name `parent` (STATIC) and itself → STATIC, pending §6.

§6.2 check on ancestor. Two clauses, no compound head arguments (`X`, `Z` are bare variables, not compounds) — so §6.2's requirement ("the head's term at position *p* is always a compound") is **not met by either argument position**. Under §6.2 alone, `ancestor` therefore does not pass the structural-decrease check on its own arguments — see §6.5 for why it is still admitted.

This is expected: `ancestor`'s termination is not evident from its own argument shapes under §6.2, which only recognizes recursion carried by compound-term structure. `ancestor` qualifies instead under §6.5 (Datalog-safe termination): neither clause constructs a compound term, and its dependency SCC (`person`, `parent`) is extensional, so `Ext(ancestor)` is finite by ordinary bottom-up evaluation regardless of `parent`'s cycle structure. `ancestor` is therefore usable in type position on the basis of §6.5, not §6.2. A relation satisfying neither §6.2 nor §6.5 — one whose recursion both builds new compound structure and depends on the extension of another possibly-unbounded relation — MUST NOT be accepted in type position under the core rules of §4–6.

§7 inference. In the second clause of `ancestor`, `Y` is unannotated. Position 2 of the first body literal `parent(X, Y)` gives `env[Y] := Person`; the second literal `ancestor(Y, Z)` re-derives `Y : Person` from `ancestor`'s own spec, `#ancestor(person, person).` (§8's codeblock), applied positionally, and `unify_type(Person, Person) = Person` — consistent, no rejection.

§4 query. `(Alice, Carol) : Grandparent` (with `Grandparent` defined, elsewhere, as a STATIC, structurally-checkable relation over compound-carrying arguments) is a well-formed arity-2 judgment; `Grandparent(Alice, Carol) : Person` would be rejected outright — arity 2 against a unary relation, §4.1.

## 9. Implementation notes and complexity

§5 (classification). Tarjan's SCC algorithm on the dependency graph, `O(V + E)` in the number of relations and clause-body literal references. Run once per compilation unit; re-run incrementally is possible but out of scope here.

§6 (structural check and Datalog-safety check). §6.2: for each recursive clause, `O(k)` per literal where `k` is the clause's arity, to test `⊏` at each candidate position; `O(clauses × arity)` overall per relation. §6.5: comparable cost, `O(clauses × arity)`, to check that no clause constructs a compound term. Both checks are purely syntactic (no unification with runtime data), so both are cheap. Per §6.3/§8's worked examples, a relation may pass either, both, or neither: `list(A)` passes §6.2 only, `ancestor` passes §6.5 only, and a relation satisfying neither remains excluded — correctly so, since the general case (an arbitrary semantic termination proof) is undecidable and out of scope for the minimal core.

**§6.4 (memoised membership).** Standard tabling: a hash map keyed on `(relation, term)` with three states (unknown / in-progress / resolved), to also detect and reject a membership query that recurses into itself without progress (which §6's static check should already have excluded, but which tabling MUST still guard against defensively, e.g. against a bug in the checker itself).

§7 (inference). Single pass per clause, `O(literals × arity)`, no backtracking — a direct consequence of `unify_type` being equality rather than a lattice meet (§7.1): there is never more than one candidate type per variable to consider.

**Suggested implementation order.** §2 (parser) → §3 (term semantics: equality, desugaring — needed by every later section) → §5 (classification, needed before anything else can be checked) → §6 (structural check and Datalog-safety check, gates type-position use) → §4 (arity-matching judgment, the leaf-level check) → §7 (inference, which calls §4 at each literal). §8's worked example is a reasonable first integration test — it exercises both termination routes (`list(A)` via §6.2, `ancestor` via §6.5).

## 10. Negation

The core as specified in §2–§9 has no negation of any kind — no literal in a clause body may be negated, and none of §4's typing judgment, §5's classification, §6's termination check, or §7's inference depends on one existing.

**This is not an oversight; negation is not needed for the soundness of §4–§7.** Soundness there rests on two properties that a purely positive (negation-free) program gets for free: **monotonicity** (adding a fact to any relation's extension never removes a fact from another's — so the bottom-up computation is a well-defined least fixpoint, unique and order-independent) and **stratification-by-construction of the classification graph** in §5.1 (the dependency graph's edges are all positive, so "depends on" has no ambiguity to resolve). Introducing negation — even the stratified variant, which restricts a negative literal `not p(X)` to refer only to a relation in a strictly earlier layer — would not repair a soundness gap in §4–§7; there is none to repair. It would only add expressiveness (the ability to state "absence of a derivation" directly) at the cost of extending §5's dependency graph with negative edges and rejecting any negative edge that falls inside a non-trivial SCC (negation through a recursive cycle, which stratification cannot assign a layer to).

Negation is therefore left out of this core by the same principle as everything in the excised extensions: it is a well-understood, independently addable capability, not a prerequisite for §2–§9 to be sound. Should it be added, it belongs as its own extension, specified against a term+type core that does not need it to stand on its own.
