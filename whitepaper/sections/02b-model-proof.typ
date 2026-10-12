#import "../lib.typ": *

// Notation local to this file, matching the first half of the section.
#let Sort = $sans("Sort")$
#let imax = $op("imax")$
#let red = sym.arrow.r.squiggly
#let elet = $sans("let")$
#let pt = $sans("pt")$
#let tv = $op("tv")$
#let graph = $op("graph")$
#let PiV = $Pi^sans("v")$
#let LamV = $Lambda$
#let TyU = $cal(T)$
// The denotation brackets ⟦ ⟧, used in math as `lden e rden_rho`.
#let lden = sym.bracket.l.stroked
#let rden = sym.bracket.r.stroked

== The set theory we assume <sec:lib>

The other side of the argument is a set theory. We do not construct
one: the reader is given an axiomatised theory — a type of sets with
the operations and laws listed below — and is promised that nothing
beyond these laws is used. The theory is stated in Lean's own logic,
so it is higher-order: separation takes any predicate of that logic,
and graphs and function spaces are formed from any function of it.
And it is deliberately not minimal: graphs, dependent function spaces
and the universe chain, which a minimal axiom system would construct,
are assumed outright with their laws, because how they are built does
not matter to the argument. The promise is literal: in the Lean
fragment the structure is a class,
#src("whitepaper/Fragment/Lib.lean", 56, 126)[#lean[SetLib]], and every theorem of the
fragment is proved against that class.

#real[
  The real proof is parametric in
  #src("ConLeche/SetTheory/Core.lean", 95, 100)[a smaller interface] —
  ZF without infinity plus a chain of Grothendieck universes, sets
  closed under all the set-forming operations — from which it derives
  the operators below.
]

Here are the laws, in four groups.

*Sets, membership, extensionality, separation.* A type $V$ of sets
with a membership relation $x in y$;
#src("whitepaper/Fragment/Lib.lean", 64, 65)[extensionality]: two sets with the same members are equal; and
#src("whitepaper/Fragment/Lib.lean", 66, 69)[separation]: for every set $A$ and every property $P$ of sets, a set
${x in A | P(x)}$ whose members are the members of $A$ that satisfy
$P$. A property here is any predicate on sets expressible in the logic
the theory is stated in — Lean's type theory — not only a first-order
formula.

*The point and the truth values.* A distinguished set $pt$, _the
point_, and
#src("whitepaper/Fragment/Lib.lean", 73, 76)[its singleton ${pt}$]. The point will be the one proof of every true
proposition. For a proposition $P$ — a proposition of the ambient
logic, in which this theory is stated — we write $tv(P)$ for the
separation ${x in {pt} | P}$ and call it
#src("whitepaper/Fragment/Lib.lean", 142, 144)[the _truth value_ of $P$]: a set whose only possible member is the
point, which it has exactly when $P$ holds, so $tv(P) = {pt}$ when
$P$ is true and $tv(P) = emptyset$ when it is false. This is an
abbreviation, not an axiom. The point itself obeys
#src("whitepaper/Fragment/Lib.lean", 120, 126)[three laws]: it is not a
truth value (it has a member other than itself), it has at most one
member, and no graph (below) is a member of it.

#real[
  The point is
  #src("ConLeche/SetTheory/Derive/Pt.lean", 68, 69)[the singleton]
  of #src("ConLeche/SetTheory/Derive/Pt.lean", 44, 46)[the set $\{emptyset, \{\{emptyset\}\}\}$],
  chosen so that no encoding of a value of a data type produces it;
  the three laws are theorems there.
]

*The universes.* A #src("whitepaper/Fragment/Lib.lean", 77, 85)[chain of sets] $cal(U)_0, cal(U)_1, cal(U)_2, dots$,
with $cal(U)_0$ the set of truth values — the subsets of ${pt}$. Each $cal(U)_n$ is a member of
$cal(U)_(n+1)$; the chain is cumulative: a member of $cal(U)_m$ is
a member of every later $cal(U)_n$; and every universe is
#src("whitepaper/Fragment/Lib.lean", 118, 119)[closed under separation].

*Graphs, function spaces, application.* For a function $F$ from sets to
sets — a function of the meta-theory, not a set — and a set $A$, a set
$graph(F, A)$; for a set $A$ and a family $B$ of sets indexed by sets,
again a function of the meta-theory, a set $Pi(A, B)$, the _dependent function
space_; and for two sets $f$ and $a$ a set $f dot.op a$, #src("whitepaper/Fragment/Lib.lean", 86, 93)[the
_application_]. Their laws:

- $pt dot.op a = pt$: #src("whitepaper/Fragment/Lib.lean", 94, 95)[a proof applied to anything is the proof].
- #src("whitepaper/Fragment/Lib.lean", 96, 97)[β]: if $a in A$ then $graph(F, A) dot.op a = F(a)$.
- $graph(F, A) != pt$: #src("whitepaper/Fragment/Lib.lean", 98, 99)[a graph is never the point].
- #src("whitepaper/Fragment/Lib.lean", 100, 103)[Congruence]: $graph(F, A)$ depends only on the values of $F$ on $A$,
  and $Pi(A, B)$ only on the values of $B$ on $A$.
- #src("whitepaper/Fragment/Lib.lean", 104, 106)[Introduction]: if $F(x) in B(x)$ for every $x in A$, then
  $graph(F, A) in Pi(A, B)$.
- #src("whitepaper/Fragment/Lib.lean", 107, 108)[Elimination]: if $f in Pi(A, B)$ and $a in A$, then $f dot.op a in B(a)$.
- #src("whitepaper/Fragment/Lib.lean", 109, 110)[η]: if $f in Pi(A, B)$, then $graph(x |-> f dot.op x, A) = f$.
- #src("whitepaper/Fragment/Lib.lean", 111, 113)[Domain uniqueness]: if $f in Pi(A, B)$ and $f in Pi(A', B')$, then
  $A = A'$.
- #src("whitepaper/Fragment/Lib.lean", 114, 117)[Closure]: for $n != 0$, if $A in cal(U)_n$ and $B(x) in cal(U)_n$ for
  every $x in A$, then $Pi(A, B) in cal(U)_n$.

This is all this section needs. When inductive types arrive, §4
extends the theory.

Two of these laws are design choices, and each earns a sentence. The
first is that _application of the point is the point_. In the model a
proof of a proposition is the point, and a proof of $forall x : A. thin P$
is again the point, not a function; the law makes application a single
operation that does the right thing on both kinds of value, so the
interpretation of $f thick a$ will not need to know which kind it is
applying. The second is that _a graph is never the point_: a function
and a proof are never the same set. A value that is known to be in a
function space, or merely known not to be the point, is therefore a
graph, and by domain uniqueness a graph carries its own domain. This is
what will let β fire with no certificate at all.

One law is deliberately restricted: closure of a universe under function
spaces is stated for $cal(U)_1, cal(U)_2, dots$ and not for $cal(U)_0$. A
proposition $forall x : A. thin P$ has no function space in the model. It
has a truth value, and a truth value is in $cal(U)_0$ whatever $A$ is —
#src("whitepaper/Fragment/Lib.lean", 275, 278)[the model's impredicativity].

== The interpretation <sec:interp>

Every term denotes a set. The interpretation is _total_ — it is defined
on every term, well-typed or not — and _term-directed_: it is a
structural recursion on the term, consulting no derivation and no
type. It takes two parameters:

- a valuation $phi$ of the level parameters (@sec:levels);
- a _variable environment_ $rho$, assigning a set to every variable in
  scope.

We write $lden e rden_rho$ for the set the term $e$ denotes under $rho$
($phi$ stays implicit), and $rho, x |-> v$ for $rho$ extended
with the value $v$ for the variable $x$. #src("whitepaper/Fragment/Interp.lean", 138, 146)[The clauses]:

$
  lden x rden_rho & = rho(x) \
  lden Sort u rden_rho & = TyU_(phi(u)) \
  lden f thick a rden_rho & = lden f rden_rho dot.op lden a rden_rho \
  lden lambda x : A. thin b rden_rho & = LamV(lden A rden_rho, med v |-> lden b rden_(rho, x |-> v)) \
  lden forall x : A. thin B rden_rho & = PiV(lden A rden_rho, med v |-> lden B rden_(rho, x |-> v)) \
  lden elet x : T := v; thin b rden_rho & = lden b rden_(rho, x |-> lden v rden_rho)
$

with $phi(u)$ the value of the level $u$ at the valuation, and $TyU_n$
the sets a sort denotes, below. The two binder clauses
#src("whitepaper/Fragment/Lib.lean", 469, 481)[read the regime off the values]:

$
  PiV(A, B) & = cases(
    Pi_0(A, B) & "if" B(v) "is a truth value for every" v in A\,,
    Pi(A, B) & "otherwise;") \
  LamV(A, F) & = cases(
    pt & "if" F(v) = pt "for every" v in A\,,
    graph(F, A) & "otherwise.")
$

Here $Pi_0(A, B)$ is
#src("whitepaper/Fragment/Lib.lean", 185, 191)[the _propositional product_],
$tv(forall v in A. thin B(v) = {pt})$: when the fibres $B(v)$ are
truth values it is their intersection $inter.big_(v in A) B(v)$ (the
empty intersection being ${pt}$), which is ${pt}$ exactly when every
fibre is and $emptyset$ otherwise — the product of subsets of a
singleton.
A `let` reads its body at the value's value, and its type is not read,
as no type is read anywhere.

A binder has two regimes. When the body is not a proposition, a
$lambda$ is a graph and a $forall$ is a set of such graphs, a
function space. When it is, a $lambda$ is a proof, hence the point,
and a $forall$ is a proposition — true when every _fibre_, the set
$lden B rden_(rho, x |-> v)$ at each $v in lden A rden_rho$, is
${pt}$. Which regime applies is decided by the values the body takes
over the domain, and by nothing else: the interpretation does not know
the sort of $B$, and does not compute it.

*The empty domain.* Over a non-empty domain the values decide as the
sort of the body would. Over an _empty_ domain there are no values,
and both clauses take their first case: a product over an empty domain
#src("whitepaper/Fragment/Lib.lean", 625, 631)[is ${pt}$], and an abstraction over one
#src("whitepaper/Fragment/Lib.lean", 633, 635)[is the point] — whatever the sort of
the body. So `False → Nat`, a type of sort `Type`, denotes ${pt}$,
and its inhabitant `fun h => h.elim` denotes the point. A product
over an inhabited domain can do the same: `Nat → False → Nat` has
${pt}$ as every fibre and is
#src("whitepaper/Fragment/Probe.lean", 52, 54)[itself ${pt}$], and `fun n h => h.elim`
is the point. No other reading over the empty domain does better:
whether the codomain is a proposition there is a fact about the
syntax, not about any value, and reading an empty product as a
function space instead would make the proposition `False → False`
denote a one-element set of graphs, which no truth value is.

*What a sort denotes.* A set is a
#src("whitepaper/Fragment/Lib.lean", 298, 302)[_type_] when it is a truth value or
_strict_: neither the point nor a set holding the point. The members
of a type are #src("whitepaper/Fragment/Lib.lean", 359, 364)[all the point or none of it] — the one fact about
types the soundness proof reads. A sort denotes
#src("whitepaper/Fragment/Lib.lean", 304, 306)[the types of its universe]:
$TyU_0 = cal(U)_0$, the truth values, and $TyU_n$ for $n >= 1$ the members of
$cal(U)_n$ that are types. These are cumulative, and $TyU_(n+1)$
holds the truth values too: it must, since `False → Nat`, of sort
`Type`, denotes ${pt}$,
#src("whitepaper/Fragment/Unannot.lean", 58, 63)[which is no strict set].
The point is no type, so no sort holds it.

// PORT: con-leche's `tyU` is on the port branch, not yet on master;
// link it (`ConLeche/SetTheory/Derive/TypeU.lean`) once it lands.
#real[
  Con-leche's sorts denote the same sets, the universe's types
  (`tyU`), read off the same notion of a strict set.
]

This is the whole of the interpretation. Nothing had to be well-typed;
no typing judgement was consulted; there is no partiality to discharge.
What replaces typing is the subject of the next subsection. Three
lemmas about the interpretation are needed later, each proved by
induction on the term:
#src("whitepaper/Fragment/Interp.lean", 242, 246)[substituting a term for a variable] is extending
the environment with the term's value,
$lden b[x := a] rden_rho = lden b rden_(rho, x |-> lden a rden_rho)$\;
hence #src("whitepaper/Fragment/Interp.lean", 248, 253)[a `let` denotes what its $zeta$-reduct denotes],
at every environment\; and #src("whitepaper/Fragment/Hygiene.lean", 464, 467)[a term does not
see a variable it does not mention].

== The semantic invariant <sec:inv>

There is no typing judgement in the proof. In its place is a predicate
on terms, the _semantic invariant_: a term is #src("whitepaper/Fragment/WellDenoted.lean", 55, 78)[_well-denoted_] when its
set is put together honestly. It is stated under a valuation $phi$ and an environment
$rho$, like the interpretation, by recursion on the term: it holds of
a term when it holds of the subterms and one condition on the term's
own shape is met. We write $rho models e$ for "$e$ is well-denoted
under $rho$" ($phi$ is fixed throughout); variables and sorts are
always well-denoted, and

#rules(
  rule(name: "app",
    $rho models f$, $rho models a$,
    $lden f rden_rho in P$,
    $lden a rden_rho in A'$,
    $rho models f thick a$),
  rule(name: "let",
    $rho models v$, $rho, x |-> lden v rden_rho models b$,
    $rho models elet x : T := v; thin b$),
)
#rules(
  rule(name: "lam",
    $rho models A$, $lden A rden_rho "a type"$,
    $forall v in lden A rden_rho. thin rho, x |-> v models b \
     forall v in lden A rden_rho. thin lden b rden_(rho, x |-> v) in B(v) "a type"$,
    $rho models lambda x : A. thin b$),
  rule(name: "pi",
    $rho models A$, $lden A rden_rho "a type"$,
    $forall v in lden A rden_rho. thin rho, x |-> v models B \
     forall v in lden A rden_rho. thin lden B rden_(rho, x |-> v) "a type"$,
    $rho models forall x : A. thin B$),
)

In app, $P$ is some product with domain $A'$: a function space
$Pi(A', B')$ whose domain $A'$ is a type, or a propositional product
$Pi_0(A', B')$ whose fibres are truth values. In lam, $B$ is some
family of types bounding the body's values, its _codomain_. In words:
an application applies a function, or a proof of a propositional
$forall$, to a member of its domain; a binder's domain is a type; a
$lambda$'s values lie in a bounded family of types, and a $forall$'s
fibres are types. The invariant records which sets are types, and that
is what makes the value reading coherent: an abstraction is
#src("whitepaper/Fragment/Lib.lean", 552, 558)[a member of the product] of a family of types bounding its values
— if every fibre is a truth value, every value is the point and so is
the abstraction; if one fibre is not, it is strict, the body's value
there is not the point, and the abstraction is the graph.

The semantic invariant is #src("whitepaper/Fragment/WellDenoted.lean", 196, 199)[transported by substitution]: $b[x := a]$ is
well-denoted under $rho$ exactly when $b$ is well-denoted under
$rho, x |-> lden a rden_rho$, provided $a$ itself is. The proof is by
induction on the term, using the interpretation's substitution
lemma; no typing derivation is involved.

A context $Gamma$ — the list of the types of the variables in scope —
is #src("whitepaper/Fragment/WellDenoted.lean", 252, 259)[_satisfied_] by $rho$ when every entry is well-denoted under the
environment beyond it, denotes a type there, and has the variable's
value as a member.
This is the semantic reading of "$Gamma$ is a well-formed context", and
it is the only thing the claims below assume about the context.

Now the first interesting point of the whole development: what a β step
needs. Take a redex $(lambda x : A. thin b) thick a$ that is
well-denoted. From the application rule we know the $lambda$'s value
lies in some product whose domain $A'$ contains $lden a rden_rho$; from the
$lambda$ rule we know the body is bounded over $lden A rden_rho$. To make
the β law fire we need $lden a rden_rho in lden A rden_rho$ — the argument
in _the λ's own_ domain — and the semantic invariant has given us $A'$, not $A$.

#lemma(name: [β off the point])[
  If $(lambda x : A. thin b) thick a$ is well-denoted under $rho$ and
  does not denote the point, then
  $lden (lambda x : A. thin b) thick a rden_rho = lden b[x := a] rden_rho$
  and $b[x := a]$ #src("whitepaper/Fragment/Sound.lean", 107, 132)[is well-denoted under $rho$].
] <lem:beta>

#proof[
  The application is not the point, so neither is the $lambda$, since
  $pt dot.op a = pt$. An abstraction that is not the point is
  a graph, $graph(v |-> lden b rden_(rho, x |-> v), lden A rden_rho)$.
  A graph is never the point, so the application's product $P$ is a
  function space $Pi(A', B')$, not a propositional product. The
  $lambda$'s own rule puts the same graph into
  $Pi(lden A rden_rho, B)$ by introduction, and domain
  uniqueness gives $A' = lden A rden_rho$; so $lden a rden_rho in lden A rden_rho$,
  and the β law computes the application to
  $lden b rden_(rho, x |-> lden a rden_rho)$, which is $lden b[x := a] rden_rho$ by
  the substitution lemma. The semantic invariant of the reduct is the
  substitution transport.
]

A redex that does denote the point is the other case, and there is no
lemma for it: its $lambda$ may be the point, which carries no domain,
and its argument may lie anywhere. Such a redex is well-denoted, and
its reduct need not be:
#src("whitepaper/Fragment/EtaIota.lean", 707, 724)[$(lambda x : A. thin g thick (k thick x)) thick a$]
with a $lambda$ that is the point and an argument $a$ outside the
domain $A$ of the graph $k$ reduces to $g thick (k thick a)$, which
is not well-denoted. So the reduction claim below says nothing about
a term that denotes the point, and β needs no premise. Why the other
rules can live with a claim that is silent about the point is the
subject of @sec:claims.

*Why no sort holds the point.* The claims below lean on one fact: an
inferred type is a type, so it is never the point. It also keeps β
sound on stored values. A stored constant $c : Sort 1$ whose value is
the ill-typed redex
$(lambda h : (forall P : sans("Prop"). thin P). thin h) thick sans("Prop")$
reduces by δ and β to $sans("Prop")$; the redex denotes the point (its
$lambda$ is an abstraction over an empty domain) and $sans("Prop")$
does not. Such an environment
#src("whitepaper/Fragment/UniformBeta.lean", 76, 80)[has no model]: the
constant's set would have to be the point and a member of
$TyU_1$, which holds no point.

== The three claims and their proof <sec:claims>

#theorem(name: "Soundness of the three relations")[
  Fix a valuation $phi$ and let $rho$ satisfy $Gamma$. Then:
  + reduction preserves the denotation and the semantic invariant off
    the point: if $Gamma tack e red e'$, $e$ is well-denoted and
    $lden e rden_rho != pt$, then $e'$ is well-denoted and
    $lden e rden_rho = lden e' rden_rho$;
  + equality means equal sets off the point: if $Gamma tack a equiv b$,
    both $a$ and $b$ are well-denoted and neither denotes the point,
    then $lden a rden_rho = lden b rden_rho$;
  + inference establishes the semantic invariant and a membership: if
    $Gamma tack e => T$, then $e$ and $T$ are well-denoted, $lden T
    rden_rho$ is a type, and $lden e rden_rho in lden T rden_rho$.
  (The theorem is #src("whitepaper/Fragment/Sound.lean", 2322, 2326)[`soundness`], with
  #src("whitepaper/Fragment/Motive.lean", 51, 84)[the three claims stated].)
] <thm:sound>

Look at where the semantic invariant sits in the three statements. Reduction and
equality _consume_ it: they are stated for well-denoted subjects, and
say nothing about others. Inference _establishes_ it: the third claim
has no premise about $e$ at all. That is the division of labour. The
checker's inference rules are the ones that check a term's shape, so
their soundness is what proves the term put together honestly; the
other two relations are handed well-denoted terms and pass the semantic
invariant along.

And look at the point. The first two claims say nothing about a term
that denotes it: a reduction of a proof may produce anything, and two
proofs are equal by proof irrelevance whatever the checker says about
them. The third claim is not conditional, and it does not need to be:
an inferred type is a type, never the point.

#corollary[
  If the checker infers $tack e => T$ in the empty context, then $lden e rden_rho in lden T rden_rho$ #src("whitepaper/Fragment/Sound.lean", 2330, 2333)[at every valuation]
  and every $rho$.
] <cor:closed>

This is the statement the environment section builds on: a
declaration is accepted when its value's inferred type is
definitionally equal to its declared type, and the corollary, with the
second claim, puts the value's set into the declared type's set.

*Why the claims may say nothing about the point.* A claim that is
silent about the point is only useful if every rule that consumes a
premise's claim has that premise off the point, or does not need it
there. Every rule falls into one of four cases.

+ _The subject is a type, never the point._ The reductions of an
  inferred type to a sort or a $forall$ (in the binder rules, in app,
  in $eta$, in proof irrelevance), the comparisons of two types (an
  argument's type with a domain in app, a domain with a domain in
  the congruences, the checker's type comparisons in $iota$), the
  fibres compared in $forall$-congruence. The third claim made each
  subject a type, so the conditional claim applies outright.
+ _The subject is off the point by hypothesis._ trans passes the
  first claim's denotation on to the second; head reduces the head of
  an application that is not the point, which is therefore not the
  point either; red-l reduces a side of an equality that is off the
  point; app compares the heads of two applications off the point.
+ _The two sides share a type, so they are both the point or
  neither._ app's arguments: the heads are one graph, whose domain is
  a type and holds both arguments. ι's comparisons and its major
  premise (@sec:ind) are of the same kind. The bodies of
  λ-congruence and $eta$ are the one place where nothing else
  supplies a common type, and that is why those rules compare the
  bodies' types (@sec:tax).
+ _The step is an identity everywhere._ β on a redex off the point
  (@lem:beta), $zeta$ and δ (@sec:defs) claim nothing beyond what
  holds at every environment.

*Proofs that are not proofs.* The proof never asks whether a term is a
_proof_ in Lean's sense, a member of a type of sort `Prop`, except in
the proof-irrelevance rule, whose claim turns out to be empty. It asks
whether the _value_ is the point, and it learns that only through a
type the term lies in. So the inhabitants of `False → Nat` and of
`Nat → False → Nat`, which denote the point although their types have
sort `Type`, are treated exactly like proofs: the claims say nothing
about their reductions, and a comparison of two of them is never
consulted. They are members of types that denote ${pt}$ at the
valuation, and to the model a member of ${pt}$ is a proof. The same
goes for a term whose value is the point only at some valuations, or
only at some values of a variable: `fun (P : Prop) (h : P) => c` is a
graph whose application to `False` is the point and to `True` is not
(#src("whitepaper/Fragment/Probe.lean", 65, 72)[a body whose point-ness varies]).

The three claims are proved together, by #src("whitepaper/Fragment/Sound.lean", 2202, 2311)[one structural induction] over
the three mutually inductive relations (#src("ConLeche/Model/Rules/Sound.lean", 43, 44)[as in con-leche]).
Every rule is one case, and every case is a lemma about that rule
alone, with the induction hypothesis for each premise as an assumption.
Most cases are routine and are listed at the end; the ones below are
where the argument lives.

#proof[
  *#src("whitepaper/Fragment/Sound.lean", 111, 132)[Rule beta]* — $(lambda x : A. thin b) thick a red b[x :=
  a]$: \
  This is @lem:beta, verbatim: the rule has no premise, and the lemma
  needs none, because the claim is asked only off the point.

  *#src("whitepaper/Fragment/Sound.lean", 134, 142)[Rule zeta]* — $elet x : T := v; thin b red b[x := v]$: \
  The two sides denote the same set at every environment, the point
  included, and the reduct's semantic invariant is the `let`'s,
  through the substitution transport.

  *#src("whitepaper/Fragment/Sound.lean", 165, 171)[Rule red-l]* — $Gamma tack a equiv b$ from $Gamma tack a red a'$ and
  $Gamma tack a' equiv b$: \
  $a$ is off the point, so by the first claim $a'$ is well-denoted
  and $lden a rden_rho = lden a' rden_rho$; now both $a'$ and $b$ are
  well-denoted and off the point, so the second claim applies to the
  continuation, and the two equalities chain. This is the one sound
  way to chain in the equality relation, because a reduction step
  _produces_ the semantic invariant of its result; see the discussion
  of transitivity below.

  *#src("whitepaper/Fragment/Sound.lean", 173, 175)[Rule sort]* — $Sort u equiv Sort v$ when $u eq.dot v$: \
    The oracle is assumed correct: it
  answers yes only if the levels agree at every valuation
  (@sec:levels), so the two sorts denote the same set.

  *#src("whitepaper/Fragment/Sound.lean", 181, 198)[Rule pi]* — $forall x : A_1. thin B_1 equiv forall x : A_2. thin B_2$ from
  $Gamma tack A_1 equiv A_2$ and $Gamma, x : A_2 tack B_1 equiv B_2$: \
  Both $forall$s are well-denoted, so their domains are types, never
  the point, and the second claim on the domains gives
  $lden A_1 rden_rho = lden A_2 rden_rho$. At every $v$ in that domain
  the fibres are types too, so the claim on the bodies makes them
  equal. A $forall$'s set is a function of its domain's set and its
  fibres — the regime included, since it is read off the fibres — so
  the two $forall$s are equal. Nothing else is needed: no comparison of
  the two sides' sorts.

  *#src("whitepaper/Fragment/Sound.lean", 200, 220)[Rule lam]* — $lambda x : A_1. thin b_1 equiv lambda x : A_2. thin b_2$ from
  the domains, the bodies, and the bodies' types $t_1 equiv t_2$: \
  The domains are equal as for $forall$. Fix $v$ in the domain. The
  third claim puts $lden b_1 rden$ in $lden t_1 rden$ and $lden b_2
  rden$ in $lden t_2 rden$ (at $rho, x |-> v$), both types, and the
  second claim on the types, which are off the point, makes them one
  type. Its members are all the point or none; so either both bodies
  are the point, or neither is and the claim on the bodies makes them
  equal. Either way they are equal at every $v$, and so are the two
  abstractions. Neither $lambda$ had to be a graph, and neither had to
  be off the point. Without the type premises the argument breaks at
  "both or neither": a body may be the point at some $v$ and not at
  others, and the claim on the bodies says nothing at such a $v$
  (@sec:tax).

  *#src("whitepaper/Fragment/Sound.lean", 233, 254)[Rule app]* — $f_1 thick a_1 equiv f_2 thick a_2$: \
  Both applications are off the point, so both heads are, and the
  claim on the heads makes them one graph. Each application's rule
  puts its argument in a product holding its head; a graph is in no
  propositional product, so both products are function spaces, and
  domain uniqueness gives both arguments in one domain — a type. They
  are both the point, or neither is and the claim on the arguments
  makes them equal.

  *#src("whitepaper/Fragment/Sound.lean", 391, 436)[Rule fun-eta]* — $lambda x : A_1. thin b_1 equiv b$ when
  $Gamma tack b => T red forall x : A_2. thin B$,
  $Gamma tack A_2 equiv A_1$, $Gamma, x : A_1 tack b_1 equiv b thick x$,
  and the body's type agrees with $B$: \
  $b$ is off the point, so the third claim, then the first, put $lden
  b rden_rho$ in the denotation of the $forall$, which is
  well-denoted; the domains are equal as before. Fix $v$ in the
  domain. The $lambda$'s body lies in its inferred type, which the
  type premise makes the fibre $lden B rden_(rho, x |-> v)$; the term
  $b thick x$ lies there by elimination. One type: both the point or
  neither, and in the second case the claim on the bodies makes them
  equal. So the $lambda$ denotes the abstraction of $v |-> lden b
  rden_rho dot.op v$, and a #src("whitepaper/Fragment/Lib.lean", 574, 577)[member of a product of types is the
  abstraction of its applications].

  *#src("whitepaper/Fragment/Sound.lean", 579, 589)[Rule proof-irrel]* — $a equiv b$ when $Gamma tack a => T_a => S_a red Sort u$
  with $u eq.dot 0$, and likewise for $b$: \
  By the third claim twice and the first once, $lden a rden_rho in
  lden T_a rden_rho in TyU_0$: a truth value, whose only possible member is
  the point. So $a$ denotes the point, and the claim, which is about
  sides off the point, holds vacuously. The two types $T_a$ and $T_b$
  were never compared, and the semantic invariants of $a$ and $b$ were
  not even used.

  *#src("whitepaper/Fragment/Sound.lean", 292, 306)[Rule pi, inference]* — $Gamma tack forall x : A. thin B => Sort (imax(u,
  v))$ when $Gamma tack A => S red Sort u$ and $Gamma, x : A tack B => T
  red Sort v$: \
  The third claim for $A$ and the first for $S$ put $lden A rden_rho$ in
  $TyU_(phi(u))$, so it is a type, and for every $v' in lden A rden_rho$
  the environment $rho, x |-> v'$ satisfies $Gamma, x : A$; the same
  claims for $B$ put every fibre in $TyU_(phi(v))$. That is the
  $forall$ rule of the semantic invariant, and the product
  #src("whitepaper/Fragment/Lib.lean", 595, 601)[lies in $TyU_(phi(imax(u, v)))$]:
  if $phi(v) = 0$ every fibre is a truth value, the product is a
  truth value, and $phi(imax(u, v)) = 0$; otherwise the product is a
  truth value or a function space in $cal(U)_(max(phi(u), phi(v)))$
  by cumulativity and closure, a type either way. Note that the
  product need not be a function space when $phi(v) != 0$: over an
  empty domain it is ${pt}$, and $TyU$ admits it.

  *#src("whitepaper/Fragment/Sound.lean", 308, 329)[Rule lam, inference]* — $Gamma tack lambda x : A. thin b => forall x : A
  . thin B$ when $Gamma tack A => S red Sort u$ and
  $Gamma, x : A tack b => B$: \
  The same argument one level down: the domain is a type, and for
  every $v'$ in it the third claim for $b$ gives $b$ and $B$
  well-denoted, $lden B rden$ a type and $lden b rden in lden B rden$.
  So the family of the $lden B rden$ is a bounded codomain of types,
  which is the $lambda$ rule, and the $forall$ rule of the inferred
  type is met too; and the introduction law for values puts the
  abstraction into the product. Nothing about the sort of $B$ is
  needed, so the rule computes none.

  *#src("whitepaper/Fragment/Sound.lean", 331, 349)[Rule app, inference]* — $Gamma tack f thick a => B[x := a]$ when
  $Gamma tack f => T red forall x : A. thin B$,
  $Gamma tack a => T_a$ and $Gamma tack T_a equiv A$: \
  By the third claim, $f$ and $T$ are well-denoted and $lden f rden_rho in lden T rden_rho$;
  $T$ is a type, so by the first claim the $forall$ is well-denoted and
  $lden T rden_rho = lden forall x : A. thin B rden_rho$. By the
  third claim for $a$, $a$ and $T_a$ are well-denoted, $lden T_a rden$ is
  a type and $lden a rden_rho in lden T_a rden_rho$; $A$ is a type by
  the $forall$ rule, so the second claim gives $lden T_a rden_rho =
  lden A rden_rho$ and $lden a rden_rho in lden A rden_rho$. Now $f thick a$ is well-denoted by the
  application rule of @sec:inv, with the $forall$'s denotation as the
  product; $B[x := a]$ is well-denoted by the
  substitution transport; and the elimination law puts
  $lden f rden_rho dot.op lden a rden_rho$ into the fibre at $lden a rden_rho$, which
  is $lden B[x := a] rden_rho$ by the substitution lemma.

  A syntactic proof would here invert a derivation of $f : T$ to
  learn the domain and the codomain — the injectivity of $forall$
  that @sec:rules discussed. Nothing is inverted here: the checker
  itself reduced $T$ to a syntactic $forall$, the first claim says
  the reduction did not change the set, and that set _is_ a product
  by the interpretation's rule.

  *#src("whitepaper/Fragment/Sound.lean", 351, 367)[Rule let, inference]* — $Gamma tack elet x : T := v; thin b => B$
  when $Gamma tack b[x := v] => B$ and the checks on the value: \
  The claim for the substituted body is the claim for the `let`: the
  two denote the same set, and the `let`'s semantic invariant is the
  substituted body's, by the transport. The two checks on the value
  are not used. They would be if the body were inferred at a variable
  of type $T$ instead: then the value must
  #src("whitepaper/Fragment/Sound.lean", 369, 385)[lie in the type] to extend a
  satisfying environment, and the checks give that.

  *The rest*, by induction on the derivation.

  - #src("whitepaper/Fragment/Sound.lean", 87, 105)[Reduction]: the no-step reduction is $lden e rden_rho = lden e rden_rho$;
    trans chains two reductions, passing the semantic invariant along;
    head reduces the head of an application off the point, which is
    off the point, and keeps the application's rule, because the head's
    set did not change.
  - #src("whitepaper/Fragment/Sound.lean", 158, 163)[Equality]: refl is again $lden e rden_rho = lden e rden_rho$, and
    sym swaps the two sides.
  - #src("whitepaper/Fragment/Sound.lean", 262, 274)[Inference]: a variable's type is read off the satisfied context; a
    sort's type is the next sort, which contains it.

  In every one of these cases the semantic invariant of every term the induction
  hypothesis is applied to is either a subterm's, or was produced by
  another claim; and every term a conditional claim is applied to is
  off the point by one of the four cases above.
]

*Why there is no transitivity.* The proof above shows why the rule
"$a equiv b$ and $b equiv c$ give $a equiv c$" cannot be added. The
second claim assumes both sides well-denoted. In a transitivity case
the induction would have to apply the hypothesis to $a equiv b$, and
for that it needs $b$ well-denoted — but $b$ is neither a subterm of
$a$ or $c$ nor produced by a premise, so nothing supplies its semantic
invariant. #src("whitepaper/Fragment/Rules.lean", 529, 546)[Every other rule] keeps the discipline of @sec:rules, and the
corresponding claim delivers the semantic invariant of every produced term. The
one way to chain is therefore "reduce, then continue", and that is how
the checker's equality test is structured: it head-normalises a side
and compares again.

The absence is not a restriction on the checker: its equality test
never chains through an arbitrary middle term; every comparison it
makes is one of the rules. Transitivity is a property one would want of
a _type theory_; the relation here describes a _checker_, and the
model only has to agree with what the checker does.

== The certification tax <sec:tax>

The checker makes two kinds of check that other checkers for Lean —
the official kernel, Lean4Lean, nanoda — skip. Both come from one fact:
the semantic invariant admits terms that are well-denoted but not
well-typed. A typing judgement would exclude them, and with them the
need for the checks; the semantic proof has no typing judgement, so
the checker verifies the one property the proof would otherwise take
from typing. The two checks are:

+ *The bodies' types at λ-congruence and $eta$*, inferred at the full
  grade and compared, at the innermost level of two $lambda$-telescopes
  only. This subsection explains it.
+ *The constructor's fields in one case of ι-reduction*: when the
  family of the major premise may be a proposition at the instance
  and the motive may not, every parameter and field of the
  constructor application is type-checked against the constructor's
  type (@sec:iota-cases explains it).

// PORT: the λ/η check runs in the ported checker (S0-F), not on master.
#real[
  On real input neither check ever fails: they never change a verdict
  on a stream the official kernel accepts. Both run at `--verified`
  only; `--trusted` skips them.
]

*Why λ-congruence needs the bodies' types.* The claim on the bodies
says nothing where a body is the point, and whether a body is the
point can vary with the variable. Without a common type of the two
bodies the rule is unsound in the model:
#src("whitepaper/Fragment/Unannot.lean", 177, 184)[the two λs]
$
  lambda (x : sans("Prop")). thin (lambda (h : E thick x). thin h) thick n
  quad "and" quad
  lambda (x : sans("Prop")). thin n,
$
with $E$ sending `True` to `Prop` and `False` to `False`, and $n$ denoting
`True`, have equal domains, and their bodies are equal by β then refl —
both premises are checker derivations — yet at $x := sans("False")$ the
left body is an abstraction over an empty domain applied, the point,
while the right body is `True`. The two λs are well-denoted, neither
is the point, and they differ. The left body is ill-typed — $n$ is no
member of $E thick x$ — but it is well-denoted, because the
abstraction over $E thick sans("False")$ is the point and constrains
nothing.

Comparing less than the types is not enough. The ill-typed redex can
be moved into a stored definition
$d := lambda x. thin (lambda (h : E thick x). thin h) thick n$ of type
$forall x : sans("Prop"). thin F thick x$; then
#src("whitepaper/Fragment/Probe.lean", 378, 394)[$lambda x. thin d thick x$ and $lambda x. thin n$]
are typed in the empty context, their bodies' types $F thick x$ and
$sans("Prop")$ both have sort `Type`, and the comparison of the bodies'
sorts, or of their zero-ness, passes; only the comparison $F thick x
equiv sans("Prop")$ fails. (That environment has a model, but $d$'s value
is not typed, so it would not be accepted. No counterexample with an
accepted environment is known; it would need a typed term whose
reduct holds a redex with an argument outside its $lambda$'s domain.
The semantic proof does not need to know whether one exists: the
check replaces the argument.)

*Why other checkers do without it.* Their argument only ever compares
two terms of one type: the caller compared the types, or knows them,
and λ-inversion gives the two bodies a common type, by subject
reduction and uniqueness of types. The model has neither, and the
semantic invariant is satisfied by terms no typing judgement derives,
so the common type is recomputed.

*Innermost only.* The checker compares
#src("whitepaper/Fragment/Rules.lean", 670, 714)[two $lambda$-telescopes level by level], and
infers and compares the bodies' types only at the innermost level,
where the descent through two syntactic $lambda$s stops (the next
comparison is $eta$, or a reduction, or anything else). At the outer
levels the domains are compared and nothing else. This is sound
because the type comparison makes the claim at the innermost level
_unconditional_: two bodies in one type are equal at every value of
the variable, the point included; and an unconditional equality of
the bodies at every value is an equality of the abstractions, with no
type at all, so #src("whitepaper/Fragment/Sound.lean", 722, 739)[the claim propagates outwards] through
any number of levels. A δ step or a reduction between two levels ends
the telescope: the witness with $d$ above is caught there, at the
innermost level.

*The full grade.* The bodies' types are inferred by the full rules of
@sec:infer, not by the cheaper grade of @sec:io. With the cheaper
grade the rule is unsound whatever that grade claims: with a _typed_
definition $g := lambda (x : sans("Prop")) thin (h : E thick x). thin n$, the body
$g thick x thick n$ (whose argument $n$ is no member of $E thick x$)
gets the type `Prop` from that grade, as $n$ does, it reduces to $n$
by δ, β, β, and
#src("whitepaper/Fragment/IOWitness.lean", 444, 456)[every premise of λ-congruence holds]
while $lambda x. thin g thick x thick n$ and $lambda x. thin n$ differ.
The premises there are derivations, not claims, so the result is
about the rule, not about the proof.

The fragment also proves weaker forms sound — no type comparison over
a domain that is a proposition, or between two bodies that do not
use the variable, or between two arguments compared at the domain of
a known head type — which the checker does not use.

== The cheaper grade of inference <sec:io>

The official kernel infers the type of a term it has already checked
by a cheaper mode, `infer_only`: an application's type is the head's
codomain at the argument, and the argument's type is never compared
with the domain. The fragment has
#src("whitepaper/Fragment/IOGrade.lean", 60, 95)[that grade]: the
rules of @sec:infer without app's argument comparison, without the
$lambda$'s check of its domain, and without the check of a local
definition's value against its type. What can it claim?

Not membership. $(lambda h : sans("False"). thin (h.sans("elim") : sans("Nat"))) thick 0$
gets the type `Nat` from that grade, is well-denoted, and denotes the
point — the $lambda$ is an abstraction over an empty domain — which is
no member of the set `Nat` denotes. Not "a member unless it is the
point" either, because that claim does not survive a $lambda$: with
$h : (b : sans("Bool")) -> sans("Bool.rec") thick sans("False") thick sans("Nat") thick b -> sans("Nat")$,
the term $lambda x : sans("Bool"). thin h thick x thick 0$ is a graph
that is the point at `false` and a number at `true`, so it is not the
point and not a member of `Bool → Nat`. What holds is
#src("whitepaper/Fragment/IOGrade.lean", 148, 172)[a hereditary claim]: the value is the point, or a member of
the type, or — when the type is syntactically a $forall$ — a graph over
the $forall$'s domain, not everywhere the point, each of whose
applications satisfies the claim at the $forall$'s body. It is
#src("whitepaper/Fragment/IOGrade.lean", 368, 369)[proved for every rule] of the grade
with no certificate at any binder: at an application whose head is not
the point the head is a graph, and a graph determines its domain. The
claim reads the type's syntax, not its value:
#src("whitepaper/Fragment/IOWitness.lean", 506, 513)[a type of sort `Type` can denote a truth value]
inhabited by a term that is not the point, so a claim read off the
value alone could not give proof irrelevance.

Two consumers are served by it: proof irrelevance with both types
inferred by the cheap grade
(#src("whitepaper/Fragment/IOGrade.lean", 425, 428)[the rule's case]: a value
whose type has sort `Prop` is the point, the hereditary case
included, because the body of a $forall$ of sort `Prop` has sort
`Prop`), and $eta$ against a term whose head is a variable or a
constant, whose claim is
#src("whitepaper/Fragment/IOGrade.lean", 446, 449)[never the hereditary one]
(#src("whitepaper/Fragment/IOGrade.lean", 479, 482)[the rule's case]).
The bodies' types at λ-congruence and $eta$ are not served, as the
witness above shows: that is why the checker infers them at the full
grade, and keeps the two grades' results apart.

// PORT: master's io grade certifies the argument at binders whose
// datum says "maybe a proposition"; the ported checker's is infer_only.
#real[
  The checker's cheap grade is `infer_only` exactly. Like it, the
  grade does not check a local definition's value against its type
  (the full grade does, @sec:infer); the soundness proof needs no
  such check, since the value is substituted.
]
