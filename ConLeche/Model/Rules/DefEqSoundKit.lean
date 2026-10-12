module

-- `RedSoundKit` is the SHARED kit: `DenoteMetaSpine`'s list algebra,
-- `hoist_spine`, `frame_spine`, `denoteMeta_mkAppN(_inv)`, the
-- `PiChain` guard and the tower entry's reading live there
public import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.PropRead
import ConLeche.Model.Annot.BitClosed
import ConLeche.Verify.InstLevels
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but
not `@[expose]`d, so the `cases`-then-`rfl` steps of the squash-regime
facts below cannot see the reduct.  `import all` restores that view
HERE only. -/
import all ConLeche.Kernel.PropWhen
import ConLeche.Semantics.Hoist
import ConLeche.Model.Annot.BitLevels
import ConLeche.Rules.Rigid

public section

/-!
# The definitional-equality soundness kit (task #305)

The plumbing the per-rule lemmas of `Model/Rules/DefEqSound.lean`
share: the frame/grading splitters at each node shape, the two `Nat`
constant readings, and `projAV`'s congruence — stated at the rules
tier's `Frame`/`Graded` vocabulary, so that no `Model/Rules` module is
stated over runs.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## The frame splitters -/

theorem Frame.app_fn {d : Nat} {f x : Expr} (h : Frame d (.app f x)) :
    Frame d f := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.app_arg {d : Nat} {f x : Expr} (h : Frame d (.app f x)) :
    Frame d x := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.2, hb.2, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.proj_arg {d : Nat} {s : Name} {i : Nat} {e : Expr}
    (h : Frame d (.proj s i e)) : Frame d e := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded] at hb
  exact ⟨hw, hb, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

/-- The opened body's frame, at an arbitrary (well-framed) domain. -/
theorem Frame.open_body {d : Nat} {ty' bd : Expr} (hty' : Frame d ty')
    (hwb : Expr.WScoped d bd) (hbb : bd.looseBVarsBounded 1 = true)
    (hLb : Expr.LeavesBounded bd) :
    Frame (d + 1) (bd.instantiate1 (.fvar d ty')) := by
  refine ⟨Expr.WScoped.instantiate1 hty'.1 0 hwb,
    ConLeche.looseBVarsBounded_instantiate1 bd 0 hbb, ?_⟩
  intro l hl
  rcases ConLeche.Expr.fvarLeaves_instantiate1 bd 0 hl with h2 | h2
  · exact hLb l h2
  · rw [ConLeche.Expr.fvarLeaves] at h2
    rcases List.mem_cons.mp h2 with rfl | h3
    · exact hty'.2.1
    · exact hty'.2.2 l h3

theorem Frame.forallE_ty {d : Nat} {ty bd : Expr} {mb : ConLeche.BinderMeta}
    (h : Frame d (.forallE ty bd mb)) : Frame d ty := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.forallE_open {d : Nat} {ty bd ty' : Expr}
    {mb : ConLeche.BinderMeta} (h : Frame d (.forallE ty bd mb))
    (hty' : Frame d ty') :
    Frame (d + 1) (bd.instantiate1 (.fvar d ty')) := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact Frame.open_body hty' hw.2 hb.2
    (fun l hl => hL l (by simp [Expr.fvarLeaves, hl]))

theorem Frame.lam_ty {d : Nat} {ty bd : Expr} {mb : ConLeche.BinderMeta}
    (h : Frame d (.lam ty bd mb)) : Frame d ty := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl])⟩

theorem Frame.lam_open {d : Nat} {ty bd ty' : Expr}
    {mb : ConLeche.BinderMeta} (h : Frame d (.lam ty bd mb))
    (hty' : Frame d ty') :
    Frame (d + 1) (bd.instantiate1 (.fvar d ty')) := by
  obtain ⟨hw, hb, hL⟩ := h
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact Frame.open_body hty' hw.2 hb.2
    (fun l hl => hL l (by simp [Expr.fvarLeaves, hl]))

theorem Frame.of_not_hasFvar {d : Nat} {e : Expr} (hf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true) : Frame d e :=
  ⟨Expr.WScoped.of_not_hasFvar hf, hb, Expr.LeavesBounded.of_not_hasFvar hf⟩

/-! ## The grading splitters, at `Graded` -/

theorem Graded.fst {Δa : List AnnotTerm} {e : AnnotTerm}
    (h : Graded V Δa (.fst e)) : Graded V Δa e := fun ρ hρ =>
  (cast (WellDenoted_fst V ρ e) (h ρ hρ)).1

theorem Graded.snd {Δa : List AnnotTerm} {e : AnnotTerm}
    (h : Graded V Δa (.snd e)) : Graded V Δa e := fun ρ hρ =>
  (cast (WellDenoted_snd V ρ e) (h ρ hρ)).1

/-- `WellDenoted.hoist_pi` at `Graded`. -/
theorem Graded.pi {Δa : List AnnotTerm} {A B : AnnotTerm}
    (h : Graded V Δa (.pi A B)) :
    GradedTy V Δa A ∧ Graded V (A :: Δa) B := by
  obtain ⟨h1, h2⟩ := WellDenoted.hoist_pi (V := V) (fun ρ hρ => h ρ hρ)
  exact ⟨fun ρ hρ => ⟨h1 ρ hρ, (cast (WellDenoted_pi V ρ A B) (h ρ hρ)).2.1⟩,
    fun ρ hρ => h2 ρ hρ⟩

/-- `WellDenoted.hoist_lam` at `Graded`. -/
theorem Graded.lam {Δa : List AnnotTerm} {A b : AnnotTerm}
    (h : Graded V Δa (.lam A b)) :
    GradedTy V Δa A ∧ Graded V (A :: Δa) b := by
  obtain ⟨h1, h2⟩ := WellDenoted.hoist_lam (V := V) (fun ρ hρ => h ρ hρ)
  exact ⟨fun ρ hρ => ⟨h1 ρ hρ, (cast (WellDenoted_lam V ρ A b) (h ρ hρ)).2.1⟩,
    fun ρ hρ => h2 ρ hρ⟩

/-- The head transport of a hoisted grading, at `Graded`. -/
theorem Graded.head_congr {Δa : List AnnotTerm} {A B e : AnnotTerm}
    (heq : ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ A = interp V ρ B)
    (h : Graded V (B :: Δa) e) : Graded V (A :: Δa) e :=
  fun ρ hρ => h ρ (Sat.head_congr heq hρ)

theorem denoteMeta_open_rename {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {bd ty ty' : Expr} {ba : AnnotTerm}
    (h : denoteMeta acval env φ (d + 1) (bd.instantiate1 (.fvar d ty))
      = some ba) :
    denoteMeta acval env φ (d + 1) (bd.instantiate1 (.fvar d ty'))
      = some ba := by
  rw [denoteMeta_erasedEq (Expr.ErasedEq.instantiate1 (Expr.ErasedEq.rfl bd)
    (show Expr.ErasedEq (.fvar d ty') (.fvar d ty) from rfl))]
  exact h

/-! ## The constant congruence -/

/-- The same constant at level-equivalent instantiations has one
validated reading. -/
theorem acval_const_congr' {m : EnvModel V env} (hap : AcvalParams m)
    {d : Nat} {n : Name} {us us' : List Level} {aa ba : AnnotTerm}
    (hlev : Level.isEquivList us us' = some true)
    (hda : denoteMeta m.acval env φ d (.const n us) = some aa)
    (hdb : denoteMeta m.acval env φ d (.const n us') = some ba) :
    aa = ba := by
  rw [denoteMeta] at hda hdb
  cases hf : env.find? n with
  | none => rw [hf] at hda; exact nomatch hda
  | some ci =>
    rw [hf] at hda hdb
    dsimp only at hda hdb
    split at hda
    · split at hdb
      · rw [← Option.some.inj hda, ← Option.some.inj hdb]
        refine hap n ci hf _ _ ?_
        intro p _
        exact Level.substFn_of_evalEqList _
          (Level.isEquivList_sound hlev φ) p
      · exact nomatch hdb
    · exact nomatch hda

/-- The subject of a graded projection spine is graded (`ProjAV.hoistV`
of `RedSoundKit`, at `Graded`). -/
theorem Graded.projAV {Δa : List AnnotTerm} {i : Nat} {e : AnnotTerm}
    (h : Graded V Δa (ConLeche.Semantics.projAV i e)) : Graded V Δa e :=
  fun ρ hρ => ProjAV.hoistV (h ρ hρ)

/-! ## The proof-irrelevance fast arm

The whole squash-regime licence: the `V`-level facts,
the type former's `.pi` chain, and `prf_of_isProofFast` itself, with
`ConstType` read as the rules tier's `ConstType`. -/

/-! ## 1. The squash-regime facts, V level -/

/-- Every application of `pt` is `pt` (`app_pt`, folded along a spine). -/
theorem foldl_app_pt' {ρ : Nat → V} : ∀ (as : List AnnotTerm),
    as.foldl (fun r a => app r (interp V ρ a)) (pt : V) = pt
  | [] => rfl
  | a :: as => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt' as

/-- A spine on a `pt`-valued head interprets to `pt`. -/
theorem interp_mkAppN_pt {ρ : Nat → V} {f : AnnotTerm}
    (hf : interp V ρ f = pt) (as : List AnnotTerm) :
    interp V ρ (AnnotTerm.mkAppN f as) = pt := by
  rw [interp_mkAppN, hf]
  exact foldl_app_pt' as

/-- The kernel's "definitely `Prop`" test on a datum: it holds at every
valuation. -/
theorem holds_of_isProp {pw : PropWhen}
    (h : pw.isProp = true) (φ : Name → Nat) : pw.holds φ = true := by
  rw [eq_of_beq h]
  rfl

/-- A level whose zero-ness datum is always-zero evaluates to `0`. -/
theorem eval_eq_zero_of_isProp {u : Level}
    (h : (Level.zeronessOf u).isProp = true) (φ : Name → Nat) :
    Level.eval φ u = 0 := by
  have := holds_of_isProp h φ
  rw [ConLeche.PropWhen.zeronessOf_sound] at this
  exact beq_iff_eq.mp this

/-- **THE FENCE.**  At a nonzero bit the product reading is a graph set
with two distinct members: a `prf` verdict read off a datum that is
not always-zero would equate them.  So the fast "yes" is exactly the
always-zero datum, model-class-wide. -/
theorem irrel_fast_fence :
    ∃ (A : V) (B : V → V) (f g : V),
      f ∈ˢ piR 1 A B ∧ g ∈ˢ piR 1 A B ∧ f ≠ g := by
  refine ⟨truthVal True, fun _ => univZero,
    lamR 1 (truthVal True) (fun _ => truthVal False),
    lamR 1 (truthVal True) (fun _ => truthVal True), ?_, ?_, ?_⟩
  · exact lamR_mem fun _ _ => truthVal_mem_univZero False
  · exact lamR_mem fun _ _ => truthVal_mem_univZero True
  · intro h
    have h1 : app (lamR 1 (truthVal True) (fun _ => (truthVal False : V))) (pt : V)
        = app (lamR 1 (truthVal True) (fun _ => (truthVal True : V))) (pt : V) :=
      congrArg (fun z => app z (pt : V)) h
    rw [app_lamR_pos (by decide) (pt_mem_truthVal trivial),
      app_lamR_pos (by decide) (pt_mem_truthVal trivial)] at h1
    have : (pt : V) ∈ˢ (truthVal False : V) := h1 ▸ pt_mem_truthVal trivial
    exact (mem_truthVal.mp this).1

/-! ## 2. The type former's telescope: a `.pi` chain -/

/-- The reading's first `n` heads are `.pi` nodes and the residual is
`.sort u` — the reading of a type former's stored type `∀ p⃗, Sort u`. -/
@[expose] def NeverChain : Nat → Nat → AnnotTerm → Prop
  | 0, u, e => e = .sort u
  | n + 1, u, e =>
    match e with
    | .pi _ B => NeverChain n u B
    | _ => False

theorem neverChain_succ_inv {n u : Nat} {e : AnnotTerm}
    (h : NeverChain (n + 1) u e) :
    ∃ A B, e = .pi A B ∧ NeverChain n u B := by
  match e with
  | .pi A B => exact ⟨A, B, rfl, h⟩
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ | .letE _ _
  | .eqE _ _ | .fst _ | .snd _ | .prf => exact nomatch h

/-- Substitution preserves the chain (`inst` maps `.pi` to `.pi` and
`.sort` to itself). -/
theorem NeverChain.inst : ∀ {n u : Nat} {e : AnnotTerm} (a : AnnotTerm) (k : Nat),
    NeverChain n u e → NeverChain n u (e.inst a k) := by
  intro n
  induction n with
  | zero => intro u e a k h; subst h; rfl
  | succ n ih =>
    intro u e a k h
    obtain ⟨A, B, rfl, hB⟩ := neverChain_succ_inv h
    exact ih a (k + 1) hB

/-- **A `.never`-peeled telescope reads to a chain**: the residual sort
evaluates. -/
theorem neverChain_of_peel {acval : Name → (Name → Nat) → AnnotTerm} :
    ∀ (n : Nat) {d : Nat} {T : Expr} {u : Level} {ta : AnnotTerm},
      T.peelNeverPis n = some (.sort u) →
      denoteMeta acval env φ d T = some ta →
      NeverChain n (Level.eval φ u) ta := by
  intro n
  induction n with
  | zero =>
    intro d T u ta hp hd
    obtain rfl := Expr.peelNeverPis_zero_inv hp
    rw [denoteMeta] at hd
    exact (Option.some.inj hd).symm
  | succ n ih =>
    intro d T u ta hp hd
    obtain ⟨ty, b, m, rfl, -, hb⟩ := Expr.peelNeverPis_succ_inv hp
    obtain ⟨tA, tB, -, htB, rfl⟩ := denoteMeta_forallE_inv hd
    exact ih (Expr.peelNeverPis_instantiate1 n _ 0 hb) htB

/-- **A type former's application lands in its result universe.**  The
walk along the chain: where the head is a graph, the argument's
membership in the domain is `slotTransfer` from the applied spine's own
hereditary app slot — no certificate anywhere. -/
theorem spine_mem_univ_of_neverChain {ρ : Nat → V} :
    ∀ (vs : List AnnotTerm) {Ta f : AnnotTerm} {u : Nat},
      NeverChain vs.length u Ta →
      WellDenotedV V ρ Ta → WellDenotedV V ρ (AnnotTerm.mkAppN f vs) →
      interp V ρ f ∈ˢ interp V ρ Ta →
      interp V ρ (AnnotTerm.mkAppN f vs) ∈ˢ (univ u : V) := by
  intro vs
  induction vs with
  | nil =>
    intro Ta f u hch _ _ hf
    obtain rfl : Ta = .sort u := hch
    exact hf
  | cons a vs ih =>
    intro Ta f u hch hokT hokS hf
    obtain ⟨A, B, rfl, hB⟩ := neverChain_succ_inv hch
    have hokApp : WellDenotedV V ρ (.app f a) := mkAppN_head vs hokS
    have hoka : WellDenotedV V ρ a :=
      (cast (WellDenoted_app V ρ f a) hokApp).2.1
    have hokB : ∀ y, y ∈ˢ interp V ρ A → WellDenotedV V (cons y ρ) B :=
      fun y hy =>
        (cast (WellDenoted_pi V ρ A B) hokT).2.2.1 y hy
    have hf' : interp V ρ f
        ∈ˢ piV (interp V ρ A) (fun x => interp V (cons x ρ) B) := hf
    -- L17: a value-read Π-tower over a sort is truth-valued where an inner
    -- domain is empty, so the head may be the point and the slot then pins
    -- no domain; the former readings' non-point head is owed
    by_cases hfp : interp V ρ f = pt
    · sorry
    have hgr : interp V ρ f
        ∈ˢ piR 1 (interp V ρ A) (fun x => interp V (cons x ρ) B) := by
      rw [piR_pos Nat.one_ne_zero]; exact mem_piSet_of_mem_piV hf' hfp
    have hmem : interp V ρ a ∈ˢ interp V ρ A := by
      obtain ⟨v', A', B', hslot, ha, -⟩ :=
        (cast (WellDenoted_app V ρ f a) hokApp).2.2
      exact slotTransfer Nat.one_ne_zero hgr hslot ha
    have hokB' : WellDenotedV V ρ (B.inst a) :=
      (WellDenotedV_inst0 hoka).mpr (hokB _ hmem)
    have hfa : interp V ρ (.app f a) ∈ˢ interp V ρ (B.inst a) := by
      rw [interp_app, interp_inst0]
      exact app_mem_piV hf' hmem
    exact ih (NeverChain.inst a 0 hB) hokB' hokS hfa

/-- The reading of a type-former application `T = hd b⃗` lands in
`univ 0` once the head's type reads to a chain of `b⃗`'s length ending
in `Sort 0`, the head inhabits it, and both readings are graded. -/
theorem mem_univ_zero_of_spine {m : EnvModel V env}
    {ρ : Nat → V} {d : Nat} {T hd : Expr} {Ta fa taH : AnnotTerm}
    (hfn : T.getAppFn = hd)
    (hTa : denoteMeta m.acval env φ d T = some Ta)
    (hfa : denoteMeta m.acval env φ d hd = some fa)
    (hchain : NeverChain T.getAppArgs.length 0 taH)
    (hokH : WellDenotedV V ρ taH) (hokT : WellDenotedV V ρ Ta)
    (hmem : interp V ρ fa ∈ˢ interp V ρ taH) :
    interp V ρ Ta ∈ˢ (univ 0 : V) := by
  rw [← ConLeche.Expr.mkAppN_getApp T, hfn] at hTa
  obtain ⟨fa', vs, hfa', hsp, rfl⟩ := denoteMeta_mkAppN_inv hTa
  rw [hfa] at hfa'
  obtain rfl := Option.some.inj hfa'
  rw [hsp.length] at hchain
  exact spine_mem_univ_of_neverChain vs hchain hokH hokT hmem

/-- **A constant-headed type former's application** (`I b⃗`, `I` stored
with type `∀ p⃗, Sort u`, every binder `.never`, `u` zero at the use's
levels) lands in `univ 0`: `ConstType` supplies `I`'s membership in
its instantiated stored type and that type's grading; the chain is
read off the stored syntax at the composed valuation. -/
theorem typeFormer_mem_univ_zero {m : EnvModel V env}
    (hct : ConstType m φ) {ρ : Nat → V} {d : Nat} {T : Expr}
    {I : Name} {us : List Level} {ci : ConstantInfo} {u : Level} {Ta : AnnotTerm}
    (hfn : T.getAppFn = .const I us) (hfI : env.find? I = some ci)
    (hnt : ci.isTowerEntry = false)
    (hlen : us.length = ci.toConstantVal.levelParams.length)
    (hpeel : ci.toConstantVal.type.peelNeverPis T.getAppArgs.length =
      some (.sort u))
    (hz : Level.eval (Level.substFn φ ci.toConstantVal.levelParams us) u = 0)
    (hTa : denoteMeta m.acval env φ d T = some Ta) (hokT : WellDenotedV V ρ Ta) :
    interp V ρ Ta ∈ˢ (univ 0 : V) := by
  obtain ⟨taI, htaI, hokI, hmemI, -, -⟩ := constTy_pkg hct hfI hnt hlen
  have htaI' := htaI d
  rw [denotePInstLevels] at htaI'
  have hchain := neverChain_of_peel (env := env) T.getAppArgs.length hpeel htaI'
  rw [hz] at hchain
  exact mem_univ_zero_of_spine hfn hTa (denoteMeta_const hfI hlen) hchain
    (hokI ρ) hokT (hmemI ρ)

/-! ## 3. The kernel-shaped licence -/

/-- A leaf of a spine's head is a leaf of the spine. -/
theorem mem_fvarLeaves_mkAppN : ∀ (as : List Expr) (f : Expr)
    (l : Nat × Expr), l ∈ f.fvarLeaves →
    l ∈ (Expr.mkAppN f as).fvarLeaves
  | [], _, _, h => h
  | a :: as, f, l, h =>
    mem_fvarLeaves_mkAppN as (.app f a) l (by simp [Expr.fvarLeaves, h])

/-- A leaf of a term's head is a leaf of the term. -/
theorem mem_fvarLeaves_of_getAppFn' {a hd : Expr} {l : Nat × Expr}
    (h : a.getAppFn = hd) (hl : l ∈ hd.fvarLeaves) : l ∈ a.fvarLeaves := by
  rw [← ConLeche.Expr.mkAppN_getApp a, h]
  exact mem_fvarLeaves_mkAppN _ _ _ hl

/-- The leaf of a term's head fvar is a leaf of the term. -/
theorem mem_fvarLeaves_of_getAppFn {a ty : Expr} {idx : Nat}
    (h : a.getAppFn = .fvar idx ty) : (idx, ty) ∈ a.fvarLeaves :=
  mem_fvarLeaves_of_getAppFn' h (by simp [Expr.fvarLeaves])

/-- The leaves of an fvar's type are leaves of the fvar. -/
theorem mem_fvarLeaves_of_ty {ty : Expr} {idx : Nat}
    {l : Nat × Expr} (h : l ∈ ty.fvarLeaves) :
    l ∈ (Expr.fvar idx ty).fvarLeaves := by
  simp [Expr.fvarLeaves, h]

/-- **A term whose validated data say "proof" is `pt`.**  The
head-symbol case split of `isProofFast`, each case closed by the
squash-regime licence (a ∀-typed head, a λ) or the one graph-regime
step (a type-former-typed head). -/
theorem prf_of_isProofFast {m : EnvModel V env} (hct : ConstType m φ)
    {d : Nat} {a : Expr} {Δa : List AnnotTerm} {aa : AnnotTerm}
    (h : isProofFast env.find? a = true)
    (hCa : CtxOkS m φ d Δa a)
    (hda : denoteMeta m.acval env φ d a = some aa)
    (ρ : Nat → V) (hρ : Sat V Δa ρ) (hL : LeavesGr m φ d a ρ) :
    interp V ρ aa = (pt : V) := by
  obtain ⟨pw, hpw, hprop⟩ := isProofFast_inv env.find? h
  rcases proofPW_some_inv env.find? hpw with
    ⟨ty, bd, mb, rfl, rfl⟩ | ⟨-, hhead⟩
  · -- a λ: L18 — the value reading reads no binder datum, so the λ's
    -- `isProp` datum does not make it the point (the fast test's `pw`
    -- read goes with L-ck's `PropRead` rewrite)
    sorry
  -- an application spine: the head decides
  have hspine := hda
  rw [← ConLeche.Expr.mkAppN_getApp a] at hspine
  obtain ⟨fa, vs, hfa, -, rfl⟩ := denoteMeta_mkAppN_inv hspine
  refine interp_mkAppN_pt ?_ vs
  rcases headProofPW_some_inv env.find? hhead with
    ⟨c, us, ci, hfn, hf, hnt, hlen, pw0, hty, rfl⟩ |
    ⟨idx, ty, hfn, hty⟩ | rfl
  · -- a constant head: the stored type decides
    rw [hfn, denoteMeta_const hf hlen] at hfa
    obtain rfl := Option.some.inj hfa
    obtain ⟨ta, hta, hokT, hmem, hnf, -⟩ := constTy_pkg hct hf hnt hlen
    rcases typeSortPW_some_inv env.find? hty with
      ⟨A, B, mb, hT, rfl⟩ | rfl |
      ⟨I, us', ciI, u, hfnT, hfI, hntI, hlenI, hpeel, rfl⟩ |
      ⟨idx, ty', u, hfnT, -, -⟩
    · -- ∀-typed: L18 — the ∀'s `isProp` datum is not read by the value
      -- reading (as the λ case)
      sorry
    · -- `Sort`-typed: never a proof
      exact absurd hprop (by simp)
    · -- a type-former application: the graph-regime step
      have hwf := m.wf _ (ConLeche.Semantics.Env.find?_mem hfI)
      have hdefU : (Level.zeronessOf u).paramsDefined
          ciI.toConstantVal.levelParams = true := by
        obtain ⟨bs, hbs⟩ := Expr.stripPis_of_peelNeverPis _ hpeel
        have := ConLeche.Expr.allLevelParamsDefined_stripPis_body _ hbs hwf.2.1
        exact ConLeche.Level.zeronessOf_paramsDefined
          (by simpa [ConLeche.Expr.allLevelParamsDefined] using this)
      have hcomp := ConLeche.Level.substPW_comp
        (ks := ci.toConstantVal.levelParams) (us := us) hlenI hdefU
      have hz : Level.eval (Level.substFn φ ciI.toConstantVal.levelParams
          (us'.map (Level.subst ci.toConstantVal.levelParams us))) u = 0 := by
        have hb := holds_of_isProp hprop φ
        rw [hcomp, ConLeche.Level.holds_substPW,
          ConLeche.PropWhen.zeronessOf_sound] at hb
        exact beq_iff_eq.mp hb
      have hT : (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us).getAppFn =
          .const I (us'.map (Level.subst ci.toConstantVal.levelParams us)) := by
        rw [ConLeche.Expr.getAppFn_instantiateLevelParams, hfnT]
        rfl
      have hpeel' : ciI.toConstantVal.type.peelNeverPis
          (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams us).getAppArgs.length =
          some (.sort u) := by
        rw [ConLeche.Expr.getAppArgs_instantiateLevelParams, List.length_map]
        exact hpeel
      have huniv := typeFormer_mem_univ_zero hct hT hfI hntI
        (by rw [List.length_map]; exact hlenI) hpeel' hz (hta d) (hokT ρ)
      exact mem_univ_zero huniv (hmem ρ)
    · -- an fvar-headed stored type: stored types are closed
      exact absurd (ConLeche.Expr.hasFvar_of_getAppFn_fvar hfnT)
        (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams] at hnf; simp [hnf])
  · -- an fvar head: the context supplies the membership
    rw [hfn, denoteMeta_fvar] at hfa
    obtain rfl := Option.some.inj hfa
    obtain ⟨-, -, tya, Aa, htya, hAa, heq⟩ :=
      hCa.2 _ (mem_fvarLeaves_of_getAppFn hfn)
    have hokT : WellDenotedTy V ρ tya :=
      hL _ (mem_fvarLeaves_of_getAppFn hfn) tya htya
    have hx : interp V ρ (.bvar (d - 1 - idx)) ∈ˢ interp V ρ tya := by
      rw [interp_bvar, heq ρ hρ]
      exact hρ _ _ hAa
    rcases typeSortPW_some_inv env.find? hty with
      ⟨A, B, mb, rfl, rfl⟩ | rfl |
      ⟨I, us', ciI, u, hfnT, hfI, hntI, hlenI, hpeel, rfl⟩ |
      ⟨idy, tyy, u, hfnT, hpeel, rfl⟩
    · -- ∀-typed: L18 (as above)
      sorry
    · exact absurd hprop (by simp)
    · -- a constant-headed type former: the graph-regime step
      have hz : Level.eval (Level.substFn φ ciI.toConstantVal.levelParams us') u
          = 0 := by
        have hb := holds_of_isProp hprop φ
        rw [ConLeche.Level.holds_substPW,
          ConLeche.PropWhen.zeronessOf_sound] at hb
        exact beq_iff_eq.mp hb
      have huniv := typeFormer_mem_univ_zero hct hfnT hfI hntI hlenI hpeel hz
        htya hokT.1
      exact mem_univ_zero huniv hx
    · -- an fvar-headed type former (`h : motive n`): the head's type
      -- is in the context too
      have hmemY := mem_fvarLeaves_of_getAppFn' hfn
          (mem_fvarLeaves_of_ty (idx := idx)
            (mem_fvarLeaves_of_getAppFn hfnT))
      obtain ⟨-, -, tyyA, Ay, htyy, hAy, heqy⟩ := hCa.2 _ hmemY
      have hokY : WellDenotedTy V ρ tyyA := hL _ hmemY tyyA htyy
      have hy : interp V ρ (.bvar (d - 1 - idy)) ∈ˢ interp V ρ tyyA := by
        rw [interp_bvar, heqy ρ hρ]
        exact hρ _ _ hAy
      have hchain := neverChain_of_peel (env := env) (acval := m.acval)
        ty.getAppArgs.length hpeel htyy
      rw [eval_eq_zero_of_isProp hprop φ] at hchain
      have huniv := mem_univ_zero_of_spine hfnT htya (denoteMeta_fvar _ _ _ _)
        hchain hokY.1 hokT.1 hy
      exact mem_univ_zero huniv hx
  · -- a sort, a ∀, a literal: never a proof
    exact absurd hprop (by simp)



/-! ## The η-projection spelling, unfolded locally

`rw [ConLeche.etaProjs]` would reference the function's EQUATION
LEMMA, generated in whichever module first forces it.  The checker's
definitions are `@[expose]`d, so the clause is available by `rfl`
here, in this tier's own module, and the proof term names nothing
outside it. -/

theorem etaProjs_eq (T : Name) (us : List Level) (targs : List Expr)
    (b : Expr) (nF : Nat) :
    ConLeche.etaProjs env T us targs b nF =
      if ConLeche.towerSlotsAll env T nF then
        (List.range nF).map fun j => Expr.proj T j b
      else
        (List.range nF).map fun j =>
          Expr.mkAppN (.const (projFnName T j) us) (targs ++ [b]) := by
  rfl

/-- The fabricated η spine's values, unfolded here for the same reason
(`etaFabArgsV`/`projSpines` are `EnvModelM`'s; `rfl` beats naming
their equation lemmas here too). -/
theorem etaFabArgsV_eq (val : Name → V) (T : Name) (ts : List V) (b : V)
    (nF : Nat) :
    etaFabArgsV val T ts b nF =
      ts ++ (List.range nF).map
        (fun j => (ts ++ [b]).foldl SetTheory.app (val (projFnName T j))) := by
  rfl

/-! ## Proof irrelevance at the io grade (task #342 L18)

The fragment's `eq_pt_of_IORel_prop`: a term whose io-inferred type's
io-inferred sort reduces to `Prop` is the point.  A member of the type:
the type is a truth value.  Hereditary: the type is a ∀ whose sort is
`Prop`, so its body's sort is `Prop` (inversion of `Infer.forallE` at
the syntax, `Sound.lean`; a sort reduces only to itself), and the
application at the hereditary clause's witness is the point by the
body's claim — against the witness.  The recursion over the ∀'s body is
`Sound.lean`'s `prop_pt_io` (it needs the body's inference claim); the
steps are here. -/

/-- The member half: a member of a type whose type reduces to a sort
evaluating to zero is the point ("not pt" source (1): the type and its
type are types). -/
theorem propPt_of_mem {m : EnvModel V env} {d : Nat} {T tt : Expr} {w : Level}
    (hsem : InferSemIO m φ d T tt) (hrs : RedSem m φ d tt (.sort w))
    (hr : Red env d tt (.sort w)) (hw0 : w.eval φ = 0)
    (hfT : Frame d T) {Δa : List AnnotTerm} {ta : AnnotTerm}
    (hCT : CtxOkS m φ d Δa T) (hT : denoteMeta m.acval env φ d T = some ta)
    (ρ : Nat → V) (v : V) (hρ : Sat V Δa ρ) (hLT : LeavesGr m φ d T ρ)
    (hm : IOMem m φ d T ρ v) : v = pt := by
  obtain ⟨hwT, hvm⟩ := hm.of_reading hT
  obtain ⟨hftt, hsub, tta, htta, hrow⟩ := hsem hfT hCT hT
  rcases hrow ρ hρ hLT hwT.1 with h | h | h
  · -- "not pt" source (1): the type is a type
    exact absurd h hwT.ne_pt
  · obtain ⟨hwtt, hTm⟩ := h.of_reading htta
    obtain ⟨-, -, sa, hsa, hs⟩ := hrs hftt (hCT.of_subset hsub) htta
    rw [denoteMeta_sort] at hsa
    obtain rfl : sa = AnnotTerm.sort (w.eval φ) := (Option.some.inj hsa).symm
    -- "not pt" source (1): the type's type is a type
    obtain ⟨-, heq⟩ := hs ρ hρ (hLT.of_subset hsub) hwtt.1 hwtt.ne_pt
    rw [heq, interp_sort, hw0] at hTm
    exact mem_univ_zero hTm hvm
  · obtain ⟨_, _, _, rfl⟩ := h.forallE
    exact nomatch Red.rigid hr trivial

/-- At a type that is not a ∀ the io claim is the point or a member. -/
theorem propPt_of_not_forallE {m : EnvModel V env} {d : Nat} {T tt : Expr} {w : Level}
    (hsem : InferSemIO m φ d T tt) (hrs : RedSem m φ d tt (.sort w))
    (hr : Red env d tt (.sort w)) (hw0 : w.eval φ = 0)
    (hnf : ∀ ty body mb, T ≠ .forallE ty body mb) : PropPt m φ d T := by
  intro hfT Δa ta hCT hT ρ v hρ hLT h
  rcases h.of_not_forallE hnf with h | h
  · exact h
  · exact propPt_of_mem hsem hrs hr hw0 hfT hCT hT ρ v hρ hLT h

/-- At a ∀: the member half as above; the hereditary half is the
point at its witness by the body's claim, a contradiction. -/
theorem propPt_forallE {m : EnvModel V env} {d : Nat} {ty body tt : Expr}
    {mb : ConLeche.BinderMeta} {w : Level}
    (hsem : InferSemIO m φ d (.forallE ty body mb) tt) (hrs : RedSem m φ d tt (.sort w))
    (hr : Red env d tt (.sort w)) (hw0 : w.eval φ = 0)
    (hbody : PropPt m φ (d + 1) (body.instantiate1 (.fvar d ty))) :
    PropPt m φ d (.forallE ty body mb) := by
  intro hfT Δa ta hCT hT ρ v hρ hLT h
  rcases h with h | h | h
  · exact h
  · exact propPt_of_mem hsem hrs hr hw0 hfT hCT hT ρ v hρ hLT h
  · rw [IOHered_forallE] at h
    obtain ⟨tya, htya, hwT, -, ⟨x₀, hx₀, hne⟩, hall⟩ := h
    exact absurd (hbody (hfT.forallE_open hfT.forallE_ty)
      (CtxOkS.openS hCT.forallE_ty hCT.forallE_body htya)
      (ta := (denoteMeta m.acval env φ (d + 1) (body.instantiate1 (.fvar d ty))).getD
        default) (by
          obtain ⟨_, ba, -, hba, -⟩ := denoteMeta_forallE_inv hT
          rw [hba]; rfl)
      (cons x₀ ρ) _ (Sat_cons V hρ hx₀)
      (LeavesGr.open hCT.forallE_ty hCT.forallE_body hLT.forallE_ty hLT.forallE_body
        htya hwT)
      (hall x₀ hx₀)) hne

/-- A ∀'s sort `imax u v` reducing to a sort that evaluates to zero:
`v` evaluates to zero (a sort reduces only to itself). -/
theorem eval_zero_of_red_imax {d : Nat} {u v w : Level}
    (hr : Red env d (.sort (.imax u v)) (.sort w)) (hw0 : w.eval φ = 0) :
    v.eval φ = 0 := by
  have h := Red.rigid hr trivial
  injection h with h
  subst h
  revert hw0
  simp only [Level.eval]
  split
  · next h => exact fun _ => h
  · next h => exact fun h' => absurd (Nat.max_eq_zero_iff.mp h').2 h

end ConLeche.Model.Rules
