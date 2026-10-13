#import "../lib.typ": *

// Notation local to this file.  Everything a rule mentions is spelled
// here once, so the rules below read the same in the PDF and the HTML.
#let Sort = $sans("Sort")$
#let imax = $op("imax")$
#let red = sym.arrow.r.squiggly
#let elet = $sans("let")$

== Terms <sec:terms>

The terms of the fragment are Lean's kernel terms, minus what @sec:left-out
leaves out:

$
  e & colon.double.eq x | Sort u | e thick e
      | lambda x : A. thin e | forall x : A. thin e
      | elet x : T := v; thin e
$

A #src("whitepaper/Fragment/Syntax.lean", 29, 48)[term] is a variable $x$; a sort $Sort u$ at a universe level $u$
(@sec:levels), with $sans("Prop") = Sort 0$; an application
$f thick a$; a function
$lambda x : A. thin b$; a dependent function type
$forall x : A. thin B$, written $A -> B$ when $x$ does not
occur in $B$; or a let-expression $elet x : T := v; thin b$.
Types are terms; there is no separate class.

The paper writes named variables, with the usual conventions: terms
are taken up to renaming of bound variables, and $B[x := a]$ is the
capture-avoiding #src("whitepaper/Fragment/Syntax.lean", 65, 75)[substitution] of $a$ for $x$.  The Lean fragment uses
de Bruijn indices instead (a variable is the number of binders
between its occurrence and its own), and a rule that mentions the types of the
variables in scope carries a _context_ $Gamma$, a list of those types.
No rule in this paper needs index arithmetic in its named form.

#real[
  Neither device is used: the checker opens a binder with a fresh
  free variable that carries its own type, so it keeps no context at
  all — a performance device that changes nothing below.
]

== Levels <sec:levels>

#src("whitepaper/Fragment/Level.lean", 29, 43)[Universe levels] are Lean's,
#src("ConLeche/Kernel/Expr.lean", 39, 44)[without metavariables]:

$
  u colon.double.eq 0 | u + 1 | max(u, v) | imax(u, v) | p
$

with $p$ a level parameter of the enclosing declaration.  A level
#src("whitepaper/Fragment/Level.lean", 50, 56)[means a natural number] once a _valuation_ $phi$ fixes the parameters:
$0$, successor, maximum, and $imax(u, v)$ is $0$ when $v$ is $0$ and
$max(u, v)$ otherwise
(#src("ConLeche/Verify/Level.lean", 26, 31)[as in con-leche]).
The impredicative maximum is what makes $forall x : A. thin B$ a
proposition whenever $B$ is one, whatever the level of $A$: its sort
is $Sort (imax(u, v))$ (rule pi in @sec:rules).

*The level oracle.*  The checker decides $u <= v$ and $u = v$ between
levels with an algorithm.  This paper does not present that algorithm
and does not verify it.  It #src("whitepaper/Fragment/Level.lean", 130, 145)[_assumes_ two Boolean functions] with a
specification: $u <= v$ is answered yes exactly when the value of $u$
is at most the value of $v$ at every valuation, and $u = v$ exactly
when the values agree at every valuation
(#src("ConLeche/Kernel/Level.lean", 143, 145)[the real $<=$],
#src("ConLeche/Kernel/Level.lean", 163, 166)[the real $=$] and their
#src("ConLeche/Verify/Level.lean", 173, 174)[soundness]
#src("ConLeche/Verify/Level.lean", 201, 202)[proofs]).  We write
$u eq.dot v$ for "the oracle says $u = v$".

== The three relations <sec:rules>

The checker is described by three relations over terms, defined
together by inference rules: _reduction_ $Gamma tack e red e'$,
_definitional equality_ $Gamma tack a equiv b$, and _inference_
$Gamma tack e => T$.  A context $Gamma$ lists the variables in scope
with their types.  The complete rule sets are
#src("whitepaper/Fragment/Rules.lean", 56, 798)[one mutual inductive definition],
#src("ConLeche/Rules/Rel.lean", 97, 101)[as in con-leche].

*How to read them.*  The three relations describe _what the checker
does_, not what is true.  $Gamma tack a equiv b$ means: on the terms
$a$ and $b$, the checker's equality test answers yes.  $Gamma tack e
=> T$ means: asked for the type of $e$, the checker returns $T$ —
we write $=>$ rather than the customary colon so that it is not read
as a typing judgement, which this paper does not have.  Every relation
is stated in the accepting direction only; nothing says what the
checker rejects.  A rule's premises are exactly what the checker did at that
site: the recursive calls it made, and the tests whose outcome fixes
the shape of the conclusion.  We call these the checker's
_certificates_.

A convention: a chain
such as $Gamma tack a => T red e$ abbreviates consecutive premises in
the same context, one per arrow, the right end of each arrow being the
subject of the next — here $Gamma tack a => T$ and $Gamma tack T red
e$.  Chains of any length are read the same way.

=== Reduction <sec:red>

Reduction chains the head steps the checker makes when it normalises
a term.  It is #src("whitepaper/Fragment/Rules.lean", 58, 69)[reflexive and transitive], and it
#src("ConLeche/Rules/Rel.lean", 101, 117)[reaches inside the head] of an application.

#rules(
  rule(name: "refl", $Gamma tack e red e$),
  rule(name: "trans", $Gamma tack e_1 red e_2$, $Gamma tack e_2 red e_3$,
    $Gamma tack e_1 red e_3$),
  rule(name: "head", $Gamma tack f red f'$, $Gamma tack f thick a red f' thick a$),
)

#src("whitepaper/Fragment/Rules.lean", 70, 80)[$beta$] fires at every redex, and
#src("whitepaper/Fragment/Rules.lean", 81, 87)[$zeta$] substitutes a
let-binding's value into its body; neither has a premise.

#rules(
  rule(name: "beta",
    $Gamma tack (lambda x : A. thin b) thick a red b[x := a]$),
  rule(name: "zeta",
    $Gamma tack (elet x : T := v; thin b) red b[x := v]$),
)

This is what the official kernel does, and it is worth a remark only
because a semantic proof might be expected to need more: the soundness
of a $beta$ step needs the argument to lie in the domain of the
$lambda$, and no premise says so.  @sec:inv explains why the model
supplies it for every redex whose value matters, and why the others
need nothing.  $zeta$ is simpler still: a let-expression denotes
what its body with the value substituted denotes, always.

=== Definitional equality

The checker's #src("whitepaper/Fragment/Rules.lean", 547, 566)[equality test] is reflexive and symmetric (the checker never
takes a symmetry step; the rule is there so that each one-sided rule
below — red-l, $eta$ — need be written once and its mirror image
follows), and it interleaves with
reduction in one way: reduce the left side, then continue.  Sorts
are #src("ConLeche/Rules/Rel.lean", 372, 374)[compared through the level oracle].

#rules(
  rule(name: "refl", $Gamma tack a equiv a$),
  rule(name: "sym", $Gamma tack a equiv b$, $Gamma tack b equiv a$),
  rule(name: "red-l", $Gamma tack a red a'$, $Gamma tack a' equiv b$,
    $Gamma tack a equiv b$),
  rule(name: "sort", $u eq.dot v$, $Gamma tack Sort u equiv Sort v$),
)

The congruences descend into the two binders and into applications.
Domains are compared first, then the bodies, under the right-hand
domain.  #src("whitepaper/Fragment/Rules.lean", 567, 575)[For $forall$] that is all; #src("whitepaper/Fragment/Rules.lean", 576, 590)[for $lambda$] the checker also
infers the types of the two bodies under the binder and compares
them — a check the official kernel does not make.  Such checks are
typeset in one colour, #tax[like this], throughout the paper; a reader
who ignores the coloured premises sees the official kernel's rule.
@sec:tax explains why they are there.

#rules(
  rule(name: "pi",
    $Gamma tack A_1 equiv A_2$, $Gamma\, x : A_2 tack B_1 equiv B_2$,
    $Gamma tack forall x : A_1. thin B_1 equiv forall x : A_2. thin B_2$),
  rule(name: "app",
    $Gamma tack f_1 equiv f_2$, $Gamma tack a_1 equiv a_2$,
    $Gamma tack f_1 thick a_1 equiv f_2 thick a_2$),
)
#rules(
  rule(name: "lam",
    $Gamma tack A_1 equiv A_2 \ Gamma\, x : A_2 tack b_1 equiv b_2$,
    tax($Gamma\, x : A_2 tack b_1 => t_1 quad Gamma\, x : A_2 tack b_2 => t_2 \ Gamma\, x : A_2 tack t_1 equiv t_2$),
    $Gamma tack lambda x : A_1. thin b_1 equiv lambda x : A_2. thin b_2$),
)

A $lambda$ against a non-$lambda$ term $b$ is #src("whitepaper/Fragment/Rules.lean", 640, 653)[tried by $eta$]: the
type of $b$ is inferred and reduced to a $forall$, its domain is
compared with the $lambda$'s, and the body is compared with $b$
applied to the bound variable — and, as at λ-congruence, the type of
the $lambda$'s body is inferred and compared with the $forall$'s
body.  Two terms are
#src("whitepaper/Fragment/Rules.lean", 654, 663)[equal by proof irrelevance] when both are proofs: each one's type has type
$Sort u$ with $u$ oracle-equal to $0$.

#rules(
  rule(name: "fun-eta",
    $Gamma tack b => T red forall x : A_2. thin B \ Gamma tack A_2 equiv A_1$,
    $Gamma\, x : A_1 tack b_1 equiv b thick x$,
    tax($Gamma\, x : A_1 tack b_1 => t_1 \ Gamma\, x : A_1 tack t_1 equiv B$),
    $Gamma tack lambda x : A_1. thin b_1 equiv b$),
)
#rules(
  rule(name: "proof-irrel",
    $Gamma tack a => T_a => S_a red Sort u$, $u eq.dot 0$,
    $Gamma tack b => T_b => S_b red Sort v$, $v eq.dot 0$,
    $Gamma tack a equiv b$),
)

*Proof irrelevance.*  The rule compares the two _sorts_ of the two
types and never the two types.  The official kernel demands more: it
also compares $T_a$ with $T_b$, so that $a$ and $b$ are proofs of the
same proposition.  This checker never compares them, and so accepts
strictly more than Lean at this one site.  The model
justifies it: every proof denotes the one canonical point, so two
proofs of two propositions denote the same set outright.

*No transitivity.*  #src("whitepaper/Fragment/Rules.lean", 529, 546)[The list has no rule] "$a equiv b$ and $b equiv c$
give $a equiv c$", and #src("ConLeche/Rules/Rel.lean", 334, 357)[none can be added].  Look at the shape of the
rules above: the two terms of every equality premise are each either a
subterm of the conclusion (the congruences, the $eta$ body) or a
term that another premise _produced_ — a reduct (red-l) or an
inferred type (lam, $eta$).  A transitivity rule would be the
one rule whose middle term comes from nowhere; @sec:claims says why
that matters, once the proof is on the table.  What the
checker does instead of chaining equalities is chain reductions:
reduce, then continue, which is red-l.

#real[
  In con-leche a transitivity rule would also meet two rules that are
  each sound alone. Free variables are
  #src("ConLeche/Rules/Rel.lean", 375, 381)[compared by index], not by
  the types they carry, and a
  #src("ConLeche/Rules/Rel.lean", 439, 444)[fast path] equates two
  terms whose heads' declared types say they are proofs. Chained, the
  two would equate any two variables: give each the type of a
  proposition, then compare the two proofs.
]

=== Inference <sec:infer>

A variable's type is #src("whitepaper/Fragment/Rules.lean", 740, 748)[read off the context], and a sort
#src("ConLeche/Rules/Rel.lean", 549, 565)[has the next sort].

#rules(
  rule(name: "var", $(x : A) in Gamma$, $Gamma tack x => A$),
  rule(name: "sort", $Gamma tack Sort u => Sort (u + 1)$),
)

The two #src("whitepaper/Fragment/Rules.lean", 754, 771)[binder rules] are Lean's own.  For a
$forall$, the domain's type must reduce to a sort $Sort u$ and the
body's type, under the domain, to a sort $Sort v$; the result is
$Sort (imax(u, v))$.  For a $lambda$, the domain's type must reduce to
a sort, and the result is the $forall$ of the body's inferred type;
the sort of that type is not computed.

#rules(
  rule(name: "pi",
    $Gamma tack A => S red Sort u$,
    $Gamma\, x : A tack B => T red Sort v$,
    $Gamma tack forall x : A. thin B => Sort (imax(u, v))$),
  rule(name: "lam",
    $Gamma tack A => S red Sort u$,
    $Gamma\, x : A tack b => B$,
    $Gamma tack lambda x : A. thin b => forall x : A. thin B$),
)

An #src("whitepaper/Fragment/Rules.lean", 772, 781)[application infers the head's type], reduces it to a $forall$,
infers the argument's type and #src("ConLeche/Rules/Rel.lean", 617, 621)[compares it with the domain].
A #src("whitepaper/Fragment/Rules.lean", 782, 796)[let-expression] checks that its type has a
sort and that its value's type agrees with it, as Lean does, and then
infers the type of the body with the value substituted.

#rules(
  rule(name: "app",
    $Gamma tack f => T red forall x : A. thin B$,
    $Gamma tack a => T_a$, $Gamma tack T_a equiv A$,
    $Gamma tack f thick a => B[x := a]$),
)
#rules(
  rule(name: "let",
    $Gamma tack T => S red Sort u$,
    $Gamma tack v => T_v$, $Gamma tack T_v equiv T$,
    $Gamma tack b[x := v] => B$,
    $Gamma tack (elet x : T := v; thin b) => B$),
)

*Reducing to a $forall$.*  Note what the application rule does not do.  It does not
know a type of $f$ that is a $forall$ "up to definitional equality"
and then argue that its domain is the right one; it reduces the
inferred type until a $forall$ is syntactically there.  This is the
site where a syntactic soundness proof needs injectivity of $forall$
— that $forall x : A. thin B equiv forall x : A'. thin B'$ forces $A equiv A'$
— a property our proof never needs, and one that the
model does not even validate: $forall x : A. thin sans("True")$ and
$forall x : A'. thin sans("True")$ denote the same truth value whatever
$A$ and $A'$ are.  Our proof argues instead: the head denotes a member
of what the $forall$ denotes, because reduction preserves denotations;
the argument denotes a member of the domain, by the certificate; and
applying a member of a function space to a member of its domain lands in the
fibre.  The second half of this section carries this out.

*The let-expression.*  The two checks on the value are what Lean
runs, and they decide verdicts: they reject a let-expression whose
value does not have the stated type even where the body ignores it.
The soundness proof does not use them (@sec:claims): the
interpretation reads no type, and the body is inferred with the value
itself in place of the variable.

#real[
  The checker substitutes the value in the same way, both when it
  #src("ConLeche/Kernel/Core.lean", 921, 923)[reduces] and when it
  #src("ConLeche/Kernel/Core.lean", 1102, 1107)[infers]; it keeps no
  variables bound to values.
  Lean's kernel opens the body at such a variable instead, which avoids
  copying the value when the body uses it many times; for con-leche
  that case is a known performance gap, not a soundness question.
]
