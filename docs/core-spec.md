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
Ident    ::= lowercase-initial identifier   (atom / functor / relation name / type name)
VarName  ::= uppercase- or '_'-initial identifier   (logic variable / type parameter)

Term ::= TermCore (':' TypeExpr)?    -- t : T, membership (§4.3.5), on any term

TermCore ::= Var
           | Atom
           | Tuple(Term, ..., Term)      -- arity ≥ 2, anonymous constructor
           | Compound(Ident, Term+)      -- named constructor, e.g. cons(H, T)
           | ListNil                     -- []
           | ListCons(Term, Term)        -- [H|T], sugar for cons(H, T)

TypeExpr ::= Ident                  -- a relation, symbol, or a literal type (§4.7)
           | Tuple(TypeExpr, ..., TypeExpr)   -- arity ≥ 2, an anonymous relation (§4.1)
           | Ident(TypeExpr+)       -- instantiation of a generic relation (§4.3)
           | VarName                -- a type parameter (§4.3)

Spec     ::= '#' Ident ('(' TypeExpr+ ')')? ('~' '(' VarName+ ')')?

Literal  ::= Member(TermCore, TypeExpr)   -- t : T, the only literal after desugaring (§4.3.5)
           | Compound(Ident, Term+)       -- r(t1, ..., tn), sugar for (t1, ..., tn) : r
```

A `Var` unifies structurally; an `Atom` is a 0-arity `Ident` used as a value, distinguished from a relation name only by position (relation names occur as the functor of a `Compound` in body position; atoms occur as arguments).

### 2.2 Concrete grammar (PEG)

Operator precedence, whitespace and comments are elided for brevity; `/` denotes an ordered choice, `<-` a rule.

```peg
Program     <- Spacing Clause* EndOfFile

Clause      <- Spec
             / Head '.'
             / Head ':-' Body '.'

Spec        <- '#' Functor SpecPositions TypeParams? '.'
             / '#' Functor TypeParams '.'
SpecPositions <- '(' TypeTerm (',' TypeTerm)* ')'
TypeParams  <- '~' '(' Var (',' Var)* ')'

Head        <- Functor '(' TermList ')'

Body        <- Term (',' Term)*                -- each a membership literal (§4.3.5)

TermList    <- Term (',' Term)*

Term        <- TermCore (':' TypeTerm)?        -- t : T, the membership judgment (§4.3.5)
TermCore    <- Compound
             / Tuple
             / ListTerm
             / Var
             / Atom

TypeTerm    <- Ident ('(' TypeTerm (',' TypeTerm)* ')')?   -- relation / literal, or an instantiation
             / '(' TypeTerm ',' TypeTerm (',' TypeTerm)* ')'  -- anonymous relation (§4.1)
             / Var                                         -- type parameter

Compound    <- Functor '(' TermList ')'
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

- **No empty argument lists.** `Compound` and `Head` require at least one argument: `f()` is not a term (it would be a second spelling of the atom `f`), and every relation has arity ≥ 1.
- `Tuple` requires **arity ≥ 2** (`(X, Z)`), so that a single parenthesised term (`(X)`) is not ambiguous with a grouping parenthesis. Kin's core grammar has no grouping parenthesis for terms outside `Tuple`/`Compound`, so this ambiguity does not otherwise arise.
- `ListTerm` is pure sugar: `[]` desugars to the atom `nil`; `[H|T]` desugars to `cons(H, T)`; `[A, B, C]` desugars to `cons(A, cons(B, cons(C, nil)))`. Desugaring MUST happen before type-checking (§4) and before the structural-decrease check (§6); neither rule has special-case knowledge of list syntax.
- **Case is grammatical (the Prolog convention).** An uppercase- or `_`-initial name is a `Var`; a lowercase-initial name is an `Ident` — an atom, a functor, or a relation name. A relation is referred to by the same lowercase spelling everywhere: as a predicate (`person(alice).`, body literals) and as a type (`#parent(person, person).`, `X: person`). Relation-name matching is exact.
- **Term position vs. type position.** A `Var` in term position (a `Term`) is a logic variable; a `Var` in type position (a `TypeTerm`) is a type parameter (§4.3). The same name MUST NOT occur in both positions within one relation.
- **Type parameters are postfix.** A generic relation's parameters are written after its spec, introduced by `~` (`#assoc ~ (K, V).`), and are usually omitted altogether because they are inferred (§4.3.2). Clause heads never carry type parameters.
- **No keywords.** The only reserved name is `symbol`, in type position (§4.6).
- **One judgment, `t : T`.** A body is a list of `Term`s. A body `Term` written `t : T` is a membership literal (`L: list(person)`, `(X, Y): parent`); a body `Term` without `:` MUST be a `Compound`, read as a call (`parent(X, Y)`, sugar for `(X, Y): parent`). Inside any term, `t : T` is the same judgment written in place — an annotation — and is lifted into the body by desugaring (§3.2).

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

Desugaring then normalises every clause so that `t : T` occurs in exactly one place — the body — and is the only kind of body literal:

```
call:        r(t_1, ..., t_n)       ⟶  (t_1, ..., t_n) : r          -- r(t) ⟶ t : r
annotation:  C[t : T]               ⟶  C[t]  with  t : T  added to the body
spec:        clause of R, #R(T_1, ..., T_n)
                                     ⟶  (v_1, ..., v_n) : (T_1, ..., T_n)  added to its body   (§4.4)
```

An annotation in a head is lifted into the body, which may turn a fact into a rule: `list(cons(H: A, T: list(A))).` becomes `list(cons(H, T)) :- H: A, T: list(A).`, and `foo(X) :- parent(X, Y: person).` becomes `foo(X) :- (X, Y): parent, Y: person.` After desugaring, a clause is a head and a conjunction of membership literals; every later section is stated over that form.

`tuple/n` names the anonymous constructor of arity `n` (§2.2's `Tuple` production); it is not a user-writable identifier (excluded from `Ident` by convention, since `Ident` is lowercase-initial and `tuple/n` is reserved per arity). Every later section operates on `desugar(t)`, never on the surface form — in particular, the subterm order `⊏` (§6.1) and the arity-matching judgment (§4.1) are defined over desugared terms, which is why neither needs a case for list or tuple syntax specifically.

### 3.3 Ground vs. open terms

A term is **ground** if it contains no `Var`; otherwise it is **open**. `Ext(R)`, the extension of a relation `R` (§5.2 onward), is a set of ground terms by construction — a fact or a derived tuple is always fully instantiated. A rule body may contain open terms (its variables), resolved to ground instances during evaluation or during a membership query (§6.4); typing (§4) and inference (§7) both operate over open terms, since they run before any particular substitution is chosen.

## 4. Types as relations — the typing judgment

### 4.1 Membership: the typing rule

**Relations hold tuples.** The extension `Ext(R)` of a relation `R` of arity `n` is a set of ground terms: for `n = 1`, plain terms; for `n ≥ 2`, `n`-tuples, i.e. `tuple/n` compounds (§3.2). A fact `parent(alice, bob).` puts the tuple `(alice, bob)` in `Ext(parent)`.

**Tuples are anonymous relations.** In type position, a tuple of types `(T_1, ..., T_n)` denotes the relation with no name whose extension is every `n`-tuple of members:

```
Ext((T_1, ..., T_n)) = { (t_1, ..., t_n) | t_i ∈ Ext(T_i) for each i }
```

A named relation is a named subset of an anonymous one: a spec `#parent(person, person)` states `Ext(parent) ⊆ Ext((person, person))` (§4.4), and `#person(symbol)` is the one-element case, `Ext(person) ⊆ Ext(symbol)` (a 1-tuple is the term itself, so `(T)` is just `T`).

The sole typing rule of Kin's core is membership:

```
Γ ⊢ t : T
────────────────────────────────────────────
T is statically computable (§5) and terminating (§6)
member(desugar(t), Ext(T))  holds
```

`T` is any type: a named relation, an instantiation (§4.3), an anonymous relation, `symbol` (§4.6) or a literal type (§4.7). Every typing judgment in this note — annotations, spec conformance (§4.4), membership literals (§4.3.5), and calls, which are membership literals in disguise — is this one rule.

```prolog
X: person                    % X holds a member of person
(X, Z): grandparent          % (X, Z) is a pair in grandparent
P: grandparent               % P holds a pair: P = (X, Z) for some X, Z
(X, Y): (person, nat)        % anonymous relation: X: person, Y: nat
```

**Arity mismatch.** A tuple term of `k` elements can only be a member of a relation of arity `k`, and an atom or a non-tuple compound only of a unary relation. When the shape of `t` is written out — a tuple, an atom, or a compound — and contradicts `T`'s arity, the judgment can never hold and MUST be rejected at compile time (`(alice, carol): person`, `alice: grandparent`). A variable has no written shape: its arity is that of its type, fixed by inference (§7).

### 4.2 Annotation inside constructed terms

An annotation `field: T` MAY occur recursively inside a compound term, not only at the head argument position. In that position it types a single **field of the constructor**, not the constructor's own overall arity — the constructor itself is not being checked against `T`, one of its arguments is:

```prolog
list(nil).
list(cons(H: A, T: list(A))).
```

Here `H: A` types the first field of `cons/2` against the type parameter `A` (§4.3); `T: list(A)` types the second field against the instantiated relation `list(A)`. Both are ordinary §4.1 judgments, written in place and lifted into the clause body by desugaring (§3.2): the clause means `list(cons(H, T)) :- H: A, T: list(A).` Annotating the whole compound is the same rule applied to the whole term: `cons(alice, nil): list(person)` holds iff that list is a member of `list(person)`.

### 4.3 Generics

A **generic relation** is a relation whose clauses or spec mention one or more **type parameters**: `Var`s in type position (§2.2). A type parameter ranges over relations, never over terms.

```prolog
list(nil).
list(cons(H: A, T: list(A))).        % one parameter, A

option(none).
option(some(X: A)).                  % one parameter, A

#assoc ~ (K, V).
assoc(L) :- L: list((K, V)).         % two parameters, explicit order

#append(list(A), list(A), list(A)).  % A comes from the spec
append(nil, L, L).
append(cons(H, T), L, cons(H, R)) :- append(T, L, R).
```

#### 4.3.1 Parameter arity

Every type parameter ranges over relations of one fixed arity `n`, its **arity**. It is never written: it is fixed by the arity of every judgment the parameter occurs in (§4.1) — `H: A` makes `A` unary, `(X, Y): E` makes `E` binary. `symbol` (§4.6) and literal types (§4.7) are unary. Two occurrences of one parameter requiring different arities MUST be rejected at compile time, citing both.

#### 4.3.2 Inferred and explicit parameters

A generic relation's parameter list is **inferred**: it is the set of type parameters occurring in its spec and clauses, each with the arity fixed by §4.3.1. The list MAY be written explicitly after the spec with `~`:

```prolog
#assoc ~ (K, V).
#append(list(A), list(A), list(A)) ~ (A).
```

1. **Order.** Instantiation (§4.3.3) is positional, so the parameter order matters. A relation with **exactly one** parameter MAY omit `~`. A relation with **two or more** parameters MUST declare them with `~`; inferring an order from textual appearance would let reordering clauses silently change what `assoc(person, nat)` means.
2. **Agreement.** When `~` is present, it MUST list exactly the inferred parameters; a missing or extra parameter MUST be rejected at compile time.
3. A `~` header without positions (`#assoc ~ (...)`) declares parameters only; the relation's positions are then typed as if it had no spec (§4.5).

#### 4.3.3 Instantiation

In type position, a generic relation MUST be applied to exactly as many type arguments as it has parameters, positionally: `list(person)`, `assoc(person, nat)`, `list((person, nat))`. Each argument MUST be a type of the parameter's arity — a relation of that arity, a type parameter of that arity in scope, or (for a unary parameter) `symbol` or a literal type. A generic relation MUST NOT be used unapplied in type position, nor called as a predicate in a body (`list(L)` leaves `A` undetermined; write `L: list(person)`, §4.3.5). A non-generic relation is never applied in type position, so an applied `TypeTerm` is always an instantiation.

Instantiation is **monomorphisation**: `list(person)` denotes the relation obtained by copying `list`'s spec and clauses with `A` substituted textually by `person`, and every reference to `list(A)` inside them by `list(person)`. It is never a runtime call to a higher-order relation value. Instantiation happens after desugaring (§3.2) and before every later pass: classification (§5), termination (§6) and inference (§7) see only the instances that the program actually uses, each an ordinary, non-generic relation. A generic relation is therefore checked once **per instance**; diagnostics in an instance MUST cite the location in the generic definition and the instantiation that produced it.

**No polymorphic recursion.** Inside a generic relation, every instantiation of the relation itself MUST pass its own parameters unchanged (`list(A)` inside `list`). A self-reference with different arguments (`list((A, A))` inside `list`) would make the set of instances infinite, and MUST be rejected at compile time.

#### 4.3.4 Displayed spec

For a generic relation without a written spec, the compiler displays (in diagnostics and documentation) an **inferred spec** that joins the head shapes of its clauses with `|`, annotations replaced by their types:

```
list   :  #list(nil | cons(A, list(A))) ~ (A)
option :  #option(none | some(A)) ~ (A)
```

This form is **display-only**: `|` is not part of the grammar, and a program MUST NOT write it. A type is defined by clauses, never by a separate type expression — the design invariant of §1.

#### 4.3.5 Membership literals

`t : T` is the one judgment of the language: `t` is a member of `T` (§4.1). It has one meaning wherever it is written — in a body, or in place inside a term as an annotation — and after desugaring (§3.2) it occurs only as a body literal: calls, annotations and specs all become membership literals. A clause body is thus a conjunction of memberships, and conjunction is intersection: a variable subject to `X: S_1, ..., X: S_k` ranges over `Ext(S_1) ∩ ... ∩ Ext(S_k)` (§7).

The written form `t : T` is also the only way to call an instantiated generic relation or an anonymous one, since a call's functor has nowhere to carry type arguments.

### 4.4 Spec conformance

A spec `#R(T_1, ..., T_n).` adds to the body of every clause of `R` with head `R(v_1, ..., v_n)` the membership literal

```
(v_1, ..., v_n) : (T_1, ..., T_n)
```

(§3.2). A spec therefore does not need a check of its own: it is a condition on every clause, and `Ext(R) ⊆ Ext((T_1, ..., T_n))` holds by construction. Its force at compile time comes from the general rule of §7.1 — every clause body MUST be statically satisfiable — which, applied to the added literal, rejects any clause that can never conform:

- a fact `parent(alice, dave).` becomes `parent(alice, dave) :- (alice, dave): (person, person).`, a ground literal decided at compile time; if `dave` is not a person the clause is unsatisfiable and MUST be rejected, citing the argument position and the spec;
- a rule whose head variable `X` is already constrained by its body to a type disjoint from `T_i` is likewise rejected.

The added literal also types and binds head variables that the body does not mention: `append(nil, L, L).` under `#append(list(A), list(A), list(A))` becomes `append(nil, L, L) :- (nil, L, L): (list(A), list(A), list(A)).`, which is range-restricted (§4.5) and types `L` as `list(A)`.

When `R` has no written spec, nothing is added.

### 4.5 Relations and specs

A **relation** is a maximal contiguous run of clauses in the program sharing one functor: at most one `Spec` (§2.2), which, when present, comes first, followed by zero or more `Head '.'` facts and `Head ':-' Body '.'` rules for that same functor, with no clause of any other relation interleaved.

```prolog
#parent(person, person).
parent(alice, bob).
parent(bob, carol).

nat(z).
nat(s(N)) :- nat(N).
```

1. **A spec is optional.** A relation's clauses already define its extension: `nat` is `z | s(N) where N is a nat`, and a spec `#nat(nat)` would only restate that. A spec is written when a position must be restricted to *another* relation, as in `#parent(person, person)`; §4.4 then checks every clause against it.
2. **Implicit spec.** A relation `R` of arity `n` without a written spec (or with a `~` header only) has the implicit spec `#R(π_1(R), ..., π_n(R))`, where `π_i(R)` is the projection of `Ext(R)` onto position `i`. For a unary relation, `π_1(R) = R`: an argument of `nat` has type `nat`. §7's inference uses `R.spec`, written or implicit, without a fallback branch. A projection `π_i(R)` is an ordinary type: joined with other types on a variable, it intersects with them (§7.1).
3. **The spec, if any, MUST precede its clauses**, and MUST be unique per functor. A second `Spec` for a functor already opened elsewhere in the program — whether identical or contradictory — MUST be rejected, citing both locations. A clause whose functor's relation was already closed by another relation's clauses MUST likewise be rejected.
4. **Arity.** `arity(R)`, used throughout §4.1's arity-matching judgment and §6's structural-decrease check, is the number of `TypeTerm` positions in `R`'s written spec, or else the head arity of its clauses. Every fact and rule head for `R` MUST have exactly that many arguments — an arity mismatch between a clause and its relation is a compile error distinct from (though checked alongside) the arity-matching judgment of §4.1, which governs an argument's *type*, not the head's *arity*.

5. **Facts are ground.** A clause whose body is empty after desugaring (§3.2) MUST NOT contain a variable. Under the case convention, `person(X).` would otherwise mean "everything is a person"; it MUST be rejected at compile time.
6. **Rules are range-restricted.** After desugaring, every variable occurring in a clause's head MUST also occur in the term of one of its body's membership literals (§4.3.5) — including those added by annotations and by the spec. An occurrence inside a literal's type does not count. `p(X) :- q(Y).` MUST be rejected at compile time, citing `X`.

A relation with a written spec and zero clauses is well-formed — its extension is simply empty — and is classified per §5.1 like any other.

### 4.6 Primitive type: `symbol`

The core provides exactly one primitive type, `symbol`, denoting an uninterpreted atom — the base case every relation-type eventually rests on. Unlike every other relation, `symbol` has no clauses: its extension is not enumerated by classify(G) — it is simply the set of all `Atom` terms (§2.1). It contributes no node to §5.1's dependency graph `G`; any edge naming it is immediately satisfied, since it depends on nothing and is STATIC by fiat, not by derivation.

`symbol` gives a base enumeration a non-circular spec: `#person(symbol)` restricts `person`'s facts to atoms.

```prolog
#person(symbol).
person(alice).
person(bob).
person(carol).
```

### 4.7 Literal (singleton) types

A particular symbol is its own type: an atom `a` used in `TypeTerm` position, once resolved as neither `symbol` nor a relation nor a generic parameter (resolution order below), denotes the **literal type** `{a}` — the singleton set containing exactly that atom. Like `symbol`, a literal type requires no `Spec`, contributes no node to §5.1's graph `G`, and is trivially STATIC: `member(t, {a})` holds iff `desugar(t) = a` exactly (§3.1's structural equality). This is scoped to bare atoms only — a compound term is never itself a type.

```prolog
#status(pending).
```

A fact for `status` MUST carry the atom `pending` itself in its argument position, not merely any `symbol`.

**Resolution order**, for a bare `Ident` (no arguments) occurring in `TypeTerm` position — the ambiguity `TypeTerm <- Ident (...)?` (§2.2) leaves open otherwise, since `symbol`, a generic parameter, a declared relation and a literal atom are all syntactically just an `Ident`:

1. `symbol` (§4.6).
2. (A type parameter is a `Var`, not an `Ident`, and never reaches this resolution — §4.3.)
3. A declared relation, matched against some `Spec` in the program.
4. Otherwise, the literal type naming that exact atom.

Each step is tried only if the previous one fails to match; the first match wins. Because step 4 also catches a misspelled relation name, the compiler SHOULD warn when a literal type names an atom that occurs nowhere else in the program as a value. An `Ident` applied to arguments (`list(A)`, `grandparent(...)`) skips straight to step 3 — a literal type is never itself parameterised.

## 5. Static computability (stratification)

A relation MAY appear in type position (right of `:`) if and only if it is statically computable: its full extension is determined without recourse to any input unknown at compile time.

### 5.1 Classification algorithm

Build the relation dependency graph `G`: one node per declared relation, and an edge `R → S` whenever a clause of `R`, after desugaring (§3.2), has a membership literal whose type names `S`. Since calls, annotations and specs all desugar to membership literals, this covers what `R`'s rules call, what its terms are annotated with, and what its spec is typed against. Nodes are the monomorphised instances of §4.3.3, so `list(person)` is a node with an edge to `person`; uninstantiated generic definitions are not nodes. `symbol` (§4.6) is not a node of `G`; an edge naming it is trivially satisfied. Classify every node by a single bottom-up pass over `G`'s condensation (its DAG of strongly connected components, SCCs):

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

This is the same SCC/stratification analysis a Datalog engine already performs to order semi-naïve evaluation; §5 reuses it for a second purpose rather than introducing a separate pass.

## 6. Termination: structural decrease criterion

A STATIC relation that is recursive (its own SCC in §5.1 is non-trivial, or it calls itself directly) MUST additionally pass a structural-decrease check (§6.2, extended by tabling in §6.4) or qualify as Datalog-safe (§6.5) before it is accepted in type position. The structural-decrease check is the standard guard-by-constructor check used by `Fixpoint` in Rocq/Coq, restricted to syntactic pattern matching (no general well-founded measure, no `Function`/`measure` escape hatch — deliberately out of scope for the minimal core).

### 6.1 Subterm order

Define `t ⊏ u` (`t` is a **strict structural subterm** of `u`) as the smallest relation such that, for every compound `f(a_1, ..., a_n)` with `n ≥ 1`, each `a_i ⊏ f(a_1, ..., a_n)`, extended transitively. Tuples and list sugar are included via their desugared form (§2.2): in `cons(H, T)`, `T ⊏ cons(H, T)`. Atoms and variables have no subterms and can only occur as the smaller side of `⊏`.

**A bare tuple `(a, b)` used as a generic recursive argument does not, by itself, decrease** — it has no distinguished constructor to descend into unless it appears as a field of a named compound (`cons`, `nil`, or a user-defined functor). This is the open point already flagged in the main specification (list/tuple unification); §6 applies only where a named constructor is present.

### 6.2 Check

For relation `R` with clauses `R(h_1, ..., h_n) :- L_1, ..., L_m.`:

```
for each clause C of R:
    for each literal L_i = (t : R) in body(C)
                                      (a recursive reference; L_i.arg[p] is
                                       the p-th component of t):
        require: ∃ position p such that
                  head_arg[p](C) is a compound, and
                  L_i.arg[p] ⊏ head_arg[p](C)
    if no such p exists for some recursive L_i:
        reject R at compile time
```

In words: at least one argument position must be fixed across the whole relation, such that the head's term at that position is always a compound, and every recursive call's term at that same position is a strict structural subterm of it.

### 6.3 Worked check

```prolog
list(nil).
list(cons(H: A, T: list(A))).
```

Checked per instance (§4.3.3); take `list(person)`. Position 1 (the sole argument): head is `cons(H, T)` in the recursive clause; the recursive reference is the annotation `T: list(person)` (§4.3.5), i.e. a recursive literal whose argument at position 1 is `T`. Since `T ⊏ cons(H, T)`, the check passes.

A relation with no structurally decreasing position (e.g. one whose only recursive argument is a bare tuple, per §6.1, or an unguarded arithmetic decrement without a Peano encoding) and that is not Datalog-safe (§6.5) MUST be rejected — with a compile error naming the recursive literal that could not be matched to a decreasing position, not a silent non-termination risk deferred to runtime.

### 6.4 Non-enumerative membership

A STATIC, structurally-decreasing relation is not necessarily *finite*. For example, the even Peano numerals:

```prolog
even(z).
even(s(s(N))) :- even(N).
```

`even` passes §6.2 (position 1: `N ⊏ s(s(N))`), yet `Ext(even)` is infinite. §5 licenses a **memoised membership query**, not full enumeration: `member(t, R)` is decided by unfolding `R`'s clauses only along the structural order fixed by §6.2, which is guaranteed to terminate by construction, with a memo table keyed on `(R, t)` to avoid recomputation (tabling, as in XSB Prolog). The compiler MUST use this algorithm rather than attempting to materialise `Ext(R)` in full whenever `R` is not finite.

### 6.5 Finite-domain (Datalog-safe) termination

A second, independent route exists into type position for a STATIC relation that never satisfies §6.2. A relation is **Datalog-safe** if no clause in its dependency SCC (§5.1) applies a functor to construct a new compound term around a variable bound by a body literal — every argument in every head and body literal is a bare variable or an atom, copied unchanged between positions, never wrapped in a fresh `Compound`, `Tuple`, or `ListCons`.

**Rule.** If every relation in `R`'s dependency SCC is Datalog-safe, and every relation `R` depends on outside its SCC (every node reachable from it in `G`, §5.1) has a finite extension, then `Ext(R)` is finite and computable by ordinary bottom-up fixpoint evaluation, independent of §6.2. `R` is usable in type position on this basis alone.

A relation has a **finite extension** when it is itself admitted by this rule, or is non-recursive with only facts. A literal type (§4.7) is finite; `symbol` (§4.6) is not, and neither is a relation admitted only by §6.2 (`nat`, `list(A)`). Without this condition, `foo(X) :- nat(X).` — Datalog-safe on its own clauses — would be wrongly declared finite; range restriction (§4.5) alone does not bound an extension, it only ties it to the body's.

**Justification.** This is the standard finiteness argument for function-symbol-free Datalog: a program that never constructs compound terms has a Herbrand base bounded by the constants already present in its finite extensional facts, so semi-naive evaluation reaches a fixpoint after finitely many iterations, regardless of cycles in the dependency graph. §6.2's structural-decrease check is needed only when a relation's recursion is carried by a growing compound term (§6.3's `list(A)`, §6.4's `even/1`) — there the Herbrand base is genuinely unbounded and finiteness cannot be assumed without it.

**Worked check.**

```prolog
ancestor(X, Z) :- parent(X, Z).
ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z).
```

Every argument in both clauses is a bare variable copied between literals; neither clause constructs a compound term, so `ancestor` is Datalog-safe. Its dependency SCC, `person` and `parent` (§8), are extensional facts and trivially Datalog-safe. `ancestor` therefore qualifies for type position under this rule, without needing to satisfy §6.2 (see §8's worked example).

A STATIC relation need only satisfy one of §6.2 (extended by §6.4) or §6.5; the two routes are disjoint and neither subsumes the other.

## 7. Type inference algorithm

After desugaring (§3.2), a clause body is a conjunction of membership literals, so the type of a variable is simply every membership it is subject to — the **intersection** of those types. Inference collects them:

```
function infer(clause):
    env := {}                                   // Var → set of types
    for each literal (t: T) in clause.body:     // calls, annotations, spec included
        bind(env, t, T)                         // T after monomorphisation, §4.3.3
    for each variable X in env:
        check_nonempty(env[X])                  // §7.1
    return env

function bind(env, t, T):
    if t is a Var:
        env[t] := env[t] ∪ {T}
    else if t is a tuple (t_1, ..., t_k):
        (T_1, ..., T_k) := components(T)        // §4.1
        for i in 1..k: bind(env, t_i, T_i)
    else if t is ground:
        require member(t, Ext(T))               // decided now, §7.1
    // an open non-tuple compound contributes its literal as a whole

components((T_1, ..., T_k)) = (T_1, ..., T_k)                  // anonymous relation
components(R)               = (R.spec.param_type[1..k])        // written or implicit spec, §4.5
```

### 7.1 Static satisfiability

Every type in a membership literal is STATIC (§5) and terminating (§6): its extension is fixed before evaluation. Whether a clause can ever hold is therefore decided **at compile time**, not discovered at evaluation. A clause MUST be rejected at compile time, citing the literals involved, when:

1. a ground literal `t : T` does not hold (`member(t, Ext(T))` is false, decided by §6.4's terminating membership);
2. a tuple literal's arity contradicts its type's (§4.1);
3. a variable's types have an empty intersection: `Ext(S_1) ∩ ... ∩ Ext(S_k) = ∅`.

The emptiness test of 3 is decided as follows:

- if some `S_i` has a finite extension (§6.5), enumerate it and test each member against the other types by §6.4's membership;
- otherwise every `S_i` is admitted by §6.2 (structural recursion), and emptiness is decided by unfolding their clauses **simultaneously** on one shared term, tabled on the set of (type, subterm position) pairs reached — the product construction for tree automata. The table is finite, since after monomorphisation there are finitely many types, so the search terminates.

The product construction applies when each clause of the `S_i` constrains each of its head's subterms independently (every body literal mentions one head variable). A clause that relates several head subterms in one literal (as `append` does) falls outside it; if the emptiness of an intersection involving such a relation cannot be decided by the first rule, the compiler MUST reject the clause as **not statically decidable** rather than defer the question to evaluation.

There is no type hierarchy and no widening: a variable's type is exactly the intersection of the memberships written (or desugared) in its clause. Joins on a variable across differently-typed relations are ordinary intersections:

```prolog
#employee(person).
staff(X) :- person(X), employee(X).            % X: person ∩ employee

closure(X, Y) :- (X, Y): E.
closure(X, Z) :- (X, Y): E, (Y, Z): closure(E).

#ancestor(person, person).
ancestor(X, Y) :- (X, Y): closure(parent).     % X: π_1(closure(parent)) ∩ person
```

### 7.2 Annotations

An annotation `parent(X, Y: person)` is a membership literal written in place (§4.3.5): it narrows `Y`'s type to an intersection including `person`, and is checked by §7.1 like any other literal — a contradictory annotation (`Y: nat` where `Y` is already a `person`) leaves an empty intersection and is rejected.

## 8. Worked example

```prolog
#person(symbol).
person(alice).
person(bob).
person(carol).

#parent(person, person).
parent(alice, bob).
parent(bob, carol).

#ancestor(person, person).
ancestor(X, Z) :- parent(X, Z).
ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z).

#grandparent(person, person).
grandparent(X, Z) :- parent(X, Y), parent(Y, Z).
```

**§5 classification.** `#person(symbol).` depends only on `symbol`, which contributes no node to `G` (§4.6) — `person` has no unsatisfied out-edges, so it is STATIC. `parent`'s spec (`#parent(person, person).`) names `person` in `TypeTerm` position — an edge `parent → person` per §5.1(b) — and `person` is already STATIC, so `parent` is STATIC. `ancestor`'s spec names `person` (STATIC) and its rule bodies name `parent` (STATIC) and itself → STATIC, pending §6.

§6.2 check on ancestor. Two clauses, no compound head arguments (`X`, `Z` are bare variables, not compounds) — so §6.2's requirement ("the head's term at position *p* is always a compound") is **not met by either argument position**. Under §6.2 alone, `ancestor` therefore does not pass the structural-decrease check on its own arguments — see §6.5 for why it is still admitted.

This is expected: `ancestor`'s termination is not evident from its own argument shapes under §6.2, which only recognizes recursion carried by compound-term structure. `ancestor` qualifies instead under §6.5 (Datalog-safe termination): neither clause constructs a compound term, and its dependency SCC (`person`, `parent`) is extensional, so `Ext(ancestor)` is finite by ordinary bottom-up evaluation regardless of `parent`'s cycle structure. `ancestor` is therefore usable in type position on the basis of §6.5, not §6.2. A relation satisfying neither §6.2 nor §6.5 — one whose recursion both builds new compound structure and depends on the extension of another possibly-unbounded relation — MUST NOT be accepted in type position under the core rules of §4–6.

§7 inference. In the second clause of `ancestor`, `Y` is unannotated. Position 2 of the first body literal `parent(X, Y)` gives `person` for `Y`; the second literal `ancestor(Y, Z)` gives `person` again, from `ancestor`'s spec applied positionally. `Y`'s type is `person ∩ person = person`, which is non-empty — no rejection.

§4 query. `grandparent` is non-recursive and depends only on `parent` and `person`, which have finite extensions, so it is STATIC and finite (§6.5). `(alice, carol) : grandparent` is a well-formed arity-2 judgment, and holds; `(alice, carol) : person` would be rejected outright — arity 2 against a unary relation, §4.1.

## 9. Implementation notes and complexity

§5 (classification). Tarjan's SCC algorithm on the dependency graph, `O(V + E)` in the number of relations and clause-body literal references. Run once per compilation unit; re-run incrementally is possible but out of scope here.

§6 (structural check and Datalog-safety check). §6.2: for each recursive clause, `O(k)` per literal where `k` is the clause's arity, to test `⊏` at each candidate position; `O(clauses × arity)` overall per relation. §6.5: comparable cost, `O(clauses × arity)`, to check that no clause constructs a compound term. Both checks are purely syntactic (no unification with runtime data), so both are cheap. Per §6.3/§8's worked examples, a relation may pass either, both, or neither: `list(A)` passes §6.2 only, `ancestor` passes §6.5 only, and a relation satisfying neither remains excluded — correctly so, since the general case (an arbitrary semantic termination proof) is undecidable and out of scope for the minimal core.

**§6.4 (memoised membership).** Standard tabling: a hash map keyed on `(relation, term)` with three states (unknown / in-progress / resolved), to also detect and reject a membership query that recurses into itself without progress (which §6's static check should already have excluded, but which tabling MUST still guard against defensively, e.g. against a bug in the checker itself).

§7 (inference). Collecting types is a single pass per clause, `O(literals × arity)`, no backtracking. The satisfiability check (§7.1) dominates: enumeration of a finite type is linear in its extension; the product construction is polynomial in the number of types intersected for a fixed set of clauses, exponential in the worst case.

**Suggested implementation order.** §2 (parser) → §3 (term semantics: equality, desugaring — needed by every later section) → §5 (classification, needed before anything else can be checked) → §6 (structural check and Datalog-safety check, gates type-position use) → §4 (arity-matching judgment, the leaf-level check) → §7 (inference, which calls §4 at each literal). §8's worked example is a reasonable first integration test — it exercises both termination routes (`list(A)` via §6.2, `ancestor` via §6.5).

## 10. Negation

The core as specified in §2–§9 has no negation of any kind — no literal in a clause body may be negated, and none of §4's typing judgment, §5's classification, §6's termination check, or §7's inference depends on one existing.

**This is not an oversight; negation is not needed for the soundness of §4–§7.** Soundness there rests on two properties that a purely positive (negation-free) program gets for free: **monotonicity** (adding a fact to any relation's extension never removes a fact from another's — so the bottom-up computation is a well-defined least fixpoint, unique and order-independent) and **stratification-by-construction of the classification graph** in §5.1 (the dependency graph's edges are all positive, so "depends on" has no ambiguity to resolve). Introducing negation — even the stratified variant, which restricts a negative literal `not p(X)` to refer only to a relation in a strictly earlier layer — would not repair a soundness gap in §4–§7; there is none to repair. It would only add expressiveness (the ability to state "absence of a derivation" directly) at the cost of extending §5's dependency graph with negative edges and rejecting any negative edge that falls inside a non-trivial SCC (negation through a recursive cycle, which stratification cannot assign a layer to).

Negation is therefore left out of this core by the same principle as everything in the excised extensions: it is a well-understood, independently addable capability, not a prerequisite for §2–§9 to be sound. Should it be added, it belongs as its own extension, specified against a term+type core that does not need it to stand on its own.
