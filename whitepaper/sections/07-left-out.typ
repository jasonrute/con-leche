#import "../lib.typ": *

= What we left out <sec:left-out>

The fragment of §2–§4 is the real checker with everything removed that
does not change the shape of the argument. This section lists what was
removed, with one sentence on what the real proof does about it and a
link to where it lives; then it describes where the real proof's
architecture differs from the fragment's even on the features they
share.

== Dropped features

#left-out[Projections][Lean's primitive projection `e.i`, the `i`-th
field of a structure value. For every inductive type with one
constructor and no index the checker stores #src("ConLeche/Kernel/Inductives/BlockTail.lean", 106, 109)[a
projection table] — the fields' types, read off the constructor. The
real checker #src("ConLeche/Rules/Rel.lean", 169, 185)[reduces a projection of a
constructor application to that field] and #src("ConLeche/Rules/Rel.lean", 627, 637)[infers its type from
the table]\; in the model a structure value is the tagged tuple of
@sec:ext-eta and a projection reads a component, which
#src("ConLeche/Model/Inductives/BlockStageTables.lean", 10, 12)[the
install of the table] establishes
(#src("ConLeche/Model/Inductives/FixKit.lean", 723, 728)[its typing
and ι laws]).]

#left-out[Mutual inductive types][Several types declared together,
each constructor free to mention any of them. The real checker
checks such a block the same way as a single type, with
a tuple of operators, one per type of the block, and each type's
family is a component of their #src("ConLeche/SetTheory/Derive/LfpTuple.lean", 8, 12)[simultaneous
least fixed point]. Nothing in it is new — only the presentation gets
heavier — so this document skips it.]

#left-out[Nat and String literals, and the fast Nat path][Numerals and
strings are terms of their own; the checker expands a literal to its
constructor form when reduction needs it
(#src("ConLeche/Rules/Rel.lean", 144, 146)[natLit],
#src("ConLeche/Rules/Rel.lean", 151, 153)[strLit]) and folds #src("ConLeche/Rules/Rel.lean", 156, 159)[`Nat.succ`] and #src("ConLeche/Rules/Rel.lean", 163, 168)[the
binary `Nat` operations] on literals with machine arithmetic. The folding is sound only for
the operations as the toolchain defines them, so the checker compares
each stream's definition against #src("ConLeche/Kernel/NatOpPins.lean", 8, 21)[a pinned copy] and the model
#src("ConLeche/Model/NatEqs.lean", 1112, 1116)[establishes the operations' recurrences] from that comparison.]

#left-out[Quotients][`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind` and the
axiom `Quot.sound` are installed from #src("ConLeche/Kernel/Basis/Quot.lean", 8, 14)[a built-in pin] and modelled by #src("ConLeche/SetTheory/Derive/Quot.lean", 65, 67)[the
set-theoretic quotient of a set by a relation], for which the pinned
constants are #src("ConLeche/Model/BasisQuot.lean", 2435, 2439)[shown to be members of their types].]

#left-out[Pinned blocks][In the fragment `False` is whatever empty
proposition the stream declares. The real checker installs `Eq`,
`Nat`, `Empty`, `False` and the quotient `Quot` from hand-written
copies of the toolchain's declarations
(#src("ConLeche/Kernel/Basis/False.lean", 37, 39)[`False`, for instance],
#src("ConLeche/Kernel/Basis/Builder.lean", 9, 18)[the builder]): a
stream block that carries a pin's names and agrees with it up to
renaming of universe parameters
#src("ConLeche/Kernel/Basis.lean", 64, 67)[installs the pin], one that
disagrees is rejected. The pins are how the main theorem
can name `False` and `Eq` and say what they denote.]

#left-out[Axioms][The fragment has none. The real checker accepts
exactly Lean's three standard axioms: `propext` and `Classical.choice`,
each #src("ConLeche/Kernel/StdAxioms.lean", 8, 15)[pinned to the toolchain's statement] and each #src("ConLeche/Model/AxiomMem.lean", 635, 641)[true in the
model] — `propext` by the extensionality of truth values, `choice` by
choice in the meta-logic — and `Quot.sound` as
part of the pinned `Quot` block above. Any other axiom record declines
the stream, with two tolerated exceptions: a declared but unused
`sorryAx` installs nothing, and Lean's deprecated compiler-trust axioms are
accepted as pinned definitions of their own types.]

#left-out[Theorems and opaques][The fragment has definitions only. The
real checker never unfolds a theorem or an opaque — #src("ConLeche/Rules/Rel.lean", 138, 141)[only a definition
unfolds].]

#left-out[Structure η and unit-likeness][#src("ConLeche/Rules/Rel.lean", 466, 469)[A constructor applied to the
projections of `b` is definitionally equal to `b`], and #src("ConLeche/Rules/Rel.lean", 494, 499)[any two terms of a
structure type with one field-less constructor are equal]. Whether a
stored type has either rule is decided from its shape when it is installed
and #src("ConLeche/Kernel/Inductives/BlockInstall.lean", 67, 80)[recorded
with it], the two laws are established there, and @sec:ext-eta and @sec:ext-unit derive
them from extensionality.]

#left-out[The `And` rescue][A concession to the fact that this checker
never unfolds a theorem, unlike the official kernel, which still does: at a
stuck proof `h` of `A ∧ B` — which older elaborators emit for a case
split on a conjunction — the recursor #src("ConLeche/Rules/Rel.lean", 307, 332)[fires on `And.intro h.1 h.2`],
fabricated from `h`'s type.]

#left-out[Fuel, memo tables, the executable checker and its bridge
theorem][In the fragment the relations are the checker. The real
checker is a program with fuel, and a theorem of its own — #src("ConLeche/Verify/Rules/Bridge.lean", 26, 29)[the
_bridge_] — says that every accepting run of it, at any fuel, yields a
derivation in the relations\; the checker the
binary runs is a further clone with memo tables, proved to #src("ConLeche/Verify/Cached/SimC.lean", 10, 15)[simulate the
fuelled one]. The
subsection below says how these fit together.]

#left-out[The two-phase parallel fold][#src("ConLeche/Cached/Installed.lean", 443, 448)[The fold] installs every
declaration first and then checks the recorded declarations one by one,
each against the prefix of the environment it was installed at\; the binary runs the
second phase on #src("ConLeche/Cached/Installed.lean", 343, 354)[a pool of workers] whose results are reassembled in
record order, so its verdict is the fold's. #src("ConLeche/Verify/Cached/MainC.lean", 37, 40)[The proof reads an
accept of the fold] as an environment in which every declaration was
checked where it was installed, which is what the one-declaration-at-a-time
argument of §3 and §4 needs.]

== How the real proof differs from the fragment

*Free variables carry their types.* The paper uses named variables and a
context. The real checker keeps no context at all. When it opens a binder it
substitutes a free variable that carries its own type,
#src("ConLeche/Kernel/Expr.lean", 315, 317)[`fvar idx type`], identified by the depth at which it was opened\; so a variable is never
looked up, the relations are indexed by the opening depth in place of a
context, and two free variables are #src("ConLeche/Rules/Rel.lean", 380, 381)[compared by depth alone]. Stored types are closed
terms, and the statement's relation reads them with de Bruijn indices
under binders, with no opening at all.

*An intermediate term language.* The real proof does not interpret the
checker's terms directly. It first reads a term into a smaller language,
#src("ConLeche/Term/Syntax.lean", 187, 218)[`Term`]: de Bruijn
indices, sorts at concrete numbers (the level valuation already
applied), and built-in constants at concrete levels. That reading,
#src("ConLeche/Verify/Denote.lean", 138, 139)[`denote`], is partial only for
syntactic reasons — an unknown constant, a wrong number of levels, a
projection with no table. The interpretation
#src("ConLeche/Semantics/Interp.lean", 134, 145)[`interp`] then maps
the term to a set, reading each binder's regime off the values
as @sec:interp does. The paper folds the two steps into one
denotation on the terms themselves.

*Six relations, not three, and a second grade.* Beside reduction,
definitional equality and inference the real description has three
more: #src("ConLeche/Rules/Rel.lean", 639, 648)[the certification of an argument spine against
a binder telescope] (the certified case of $iota$),
#src("ConLeche/Rules/Rel.lean", 650, 655)[pairwise definitional equality], and
#src("ConLeche/Rules/Rel.lean", 507, 546)[the congruence of two λ-telescopes]
(@sec:tax). A rule with a premise about a list or a telescope needs a
relation of its own in a mutual block; the paper inlines them into the
rules that use them. Inference also carries a
grade index, for the cheaper grade of @sec:io, which the fragment
states as a relation of its own.

*The bridge and the recomposition.* Because the real checker is a
program, its proof has three parts where the paper has one. #src("ConLeche/Verify/Rules/Bridge.lean", 26, 29)[The bridge] turns an accepting
run at any fuel into a derivation — one induction on fuel, each checker
site landing on one rule. #src("ConLeche/Model/Rules/Sound.lean", 49, 50)[The soundness] is the paper's
induction: one structural induction over the six relations, each case a
lemma about one rule, never mentioning the implementation. #src("ConLeche/Model/Rules/Recompose.lean", 50, 55)[The
recomposition] puts them together, claim by claim: bridge the run,
apply the soundness, and hand the result to the declaration fold.

*The statement over `Denotes`.* The main theorem is not stated over the
intermediate language and `interp` but over #src("ConLeche/Denotes.lean", 121, 124)[`Denotes`], a relation on the checker's
own terms with no intermediate language, one rule per syntax form,
written to be read in one sitting; and over the structure #src("ConLeche/Denotes.lean", 266, 286)[`Model`] built on it. #src("ConLeche/Model/Denotes.lean", 192, 198)[A theorem]
connects the two: wherever the reading `denote` exists, its
interpretation is a `Denotes`-denotation of the term. The paper's theorem is
the model side directly.

*The cached checker and its simulation.* The core the binary runs is #src("ConLeche/Cached/CoreC.lean", 8, 11)[a
clone of the pure one] over a term representation that carries a
precomputed hash in every node, with memo tables for reduction,
equality and inference. #src("ConLeche/Verify/Cached/SimC.lean", 10, 15)[A simulation proof] shows
that every successful run of the cached core is a successful run of the
pure fuelled core at some fuel, with the memo tables' invariant
preserved\; the main
theorem #src("ConLeche/Verify/Cached/MainC.lean", 37, 40)[composes it with the fold's soundness].

*The frontend.* Between the export file and the declaration fold sit
a decoder and one transformation of the decoded list,
#src("ConLeche/Frontend/Prepare.lean", 171, 172)[`preparePrelude`]:
the declarations of a built-in copy of the toolchain's prelude — `Eq`,
`Nat`, `Bool` and their kin — are moved to the front, the stream's own
record where it has one and the copy's where it has none, and the
structural `Nat` operations a pinned operation's certificate mentions
are moved ahead of it.
#src("ConLeche/Verify/Frontend/Prepare.lean", 160, 161)[A theorem
says that this is all]: the fold's input is a permutation of the
decoded list plus records of the built-in prelude; nothing is rewritten
and nothing is generated. What no theorem says is that the decoded
list means the same as the export file: the decoder is written to be
meaning-preserving, and that is a review claim. The fragment has no
frontend: its stream is its environment.
