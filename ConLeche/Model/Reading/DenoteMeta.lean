module

public import ConLeche.Semantics.Canon

public section

/-!
# `denoteMeta` — the stored-term reading (task #161, P3; task #342, L14a)

`denoteMeta` is `denote`'s recursion into the semantic syntax
`ITerm`: no checker run, no fuel, no mode.  The binders carry no
datum to read (the regime is read off the values by `interp`,
`piV`/`lamV`), so the level crossing is plain algebra
(`Reading/Levels.lean`, `denotePInstLevels`) and two readings of one
term at one valuation are equal.

The `Reading/` modules are `denoteMeta`'s metatheory: its lemma
battery (`Lemmas`), closedness (`Closed`), depth shift (`Shift`),
instantiation (`Inst`, `SubstFvars`), the level crossing (`Levels`),
blindness to erasure (`ErasedEq`), the environment crossings
(`EnvExtend`, `TowerExtend`, `ConsCross`, `Install`) and its level
footprint (`LpDefF`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (ITerm)
open ConLeche (CheckMode Env Expr Name Level PropWhen
  natLitSupported strLitSupported)

/-! ## The reading -/

/-- The stored-term reading: `denote`'s recursion into `ITerm`, no
checker runs, no fuel, no mode. -/
@[expose] def denoteMeta (acval : Name → (Name → Nat) → ITerm)
    (env : Env) (φ : Name → Nat) :
    (d : Nat) → Expr → Option ITerm
  | _, .sort u => some (.sort (u.eval φ))
  | d, .fvar idx _ => some (.bvar (d - 1 - idx))
  | _, .const n us =>
    match env.find? n with
    | some ci =>
      if us.length = ci.toConstantVal.levelParams.length then
        some (acval n (Level.substFn φ ci.toConstantVal.levelParams us))
      else none
    | none => none
  | d, .forallE ty body => do
    let ta ← denoteMeta acval env φ d ty
    let ba ← denoteMeta acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty))
    some (.pi ta ba)
  | d, .lam ty body => do
    let ta ← denoteMeta acval env φ d ty
    let ba ← denoteMeta acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty))
    some (.lam ta ba)
  | d, .app f a => do
    let fa ← denoteMeta acval env φ d f
    let aa ← denoteMeta acval env φ d a
    some (.app fa aa)
  | d, .letE ty v b => do
    -- the type must read (its constants resolve, as everywhere in a
    -- stored term), but the reading drops it: nothing reads a `let`'s
    -- type.  The body is opened at a fresh variable, as a binder's.
    let _ ← denoteMeta acval env φ d ty
    let va ← denoteMeta acval env φ d v
    let ba ← denoteMeta acval env φ (d + 1)
      (b.instantiate1 (.fvar d ty))
    some (.letE va ba)
  | d, .proj sn i e => do
    let ea ← denoteMeta acval env φ d e
    -- the entry-kind branch (task #175 wiring W3): a tower-backed
    -- entry reads field `i` by the uniform iterated spelling
    -- (`projAV`, whose `WellDenoted`/substitution batteries are the
    -- introduction machinery's); the pair/absent side is the pre-W3
    -- clause
    match env.findProj? sn i with
    | some entry => some (projAV (i + entry.off) ea)
    | none => ITerm.projPair? i ea
  | _, .lit (.natVal n) =>
    if natLitSupported env then
      some (natLitAV (acval natZeroName (Level.substFn φ [] []))
        (acval natSuccName (Level.substFn φ [] [])) n)
    else none
  | _, .lit (.strVal s) =>
    if strLitSupported env then
      some (.app (acval stringOfListName (Level.substFn φ [] []))
        (charListAV
          (.app (acval listNilName
              (Level.substFn φ (levelParamsAt env listNilName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (.app (acval listConsName
              (Level.substFn φ (levelParamsAt env listConsName) [.zero]))
            (acval charName (Level.substFn φ [] [])))
          (acval charOfNatName (Level.substFn φ [] []))
          (acval natZeroName (Level.substFn φ [] []))
          (acval natSuccName (Level.substFn φ [] []))
          s.toList))
    else none
  | _, _ => none
termination_by _ e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-! ## The erasure law

`denoteMeta` erases to `denote` exactly: the annotations are extra,
the denotation is the same. -/

/-- The validated-annotation reading is an annotation of the
denotation, exactly. -/
theorem denoteMeta_erase {acval : Name → (Name → Nat) → ITerm}
    {cval : TConstVal} {env : Env} {φ : Name → Nat}
    (hlink : ∀ n ψ, (acval n ψ).erase = cval n ψ) :
    ∀ (d : Nat) (e : Expr) {ea : ITerm},
      denoteMeta acval env φ d e = some ea →
      denote cval env φ d e = some ea.erase := by
  intro d e
  induction d, e using denoteMeta.induct (env := env) with
  | case1 d u =>
    intro ea h
    rw [denoteMeta] at h
    obtain rfl := Option.some.inj h
    rw [denote_sort]
    rfl
  | case2 d idx ty =>
    intro ea h
    rw [denoteMeta] at h
    obtain rfl := Option.some.inj h
    rw [denote_fvar]
    rfl
  | case3 d n us ci hf hlen =>
    intro ea h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [ite_eq_left hlen] at h
    obtain rfl := Option.some.inj h
    rw [denote_const, hf]
    dsimp only
    rw [ite_eq_left hlen, hlink]
  | case4 d n us ci hf hlen =>
    intro ea h
    rw [denoteMeta, hf] at h
    dsimp only at h
    rw [ite_eq_right hlen] at h
    exact nomatch h
  | case5 d n us hf =>
    intro ea h
    rw [denoteMeta, hf] at h
    exact nomatch h
  | case6 d ty body ihty ihbody =>
    intro ea h
    rw [denoteMeta] at h
    rcases hta : denoteMeta acval env φ d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denoteMeta acval env φ (d + 1)
        (body.instantiate1 (.fvar d ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    obtain rfl := Option.some.inj h
    rw [denote_forallE, ihty hta, ihbody hba]
    rfl
  | case7 d ty body ihty ihbody =>
    intro ea h
    rw [denoteMeta] at h
    rcases hta : denoteMeta acval env φ d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hba : denoteMeta acval env φ (d + 1)
        (body.instantiate1 (.fvar d ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    obtain rfl := Option.some.inj h
    rw [denote_lam, ihty hta, ihbody hba]
    rfl
  | case8 d fe a ihf iha =>
    intro ea h
    rw [denoteMeta] at h
    rcases hfa : denoteMeta acval env φ d fe with _ | fa
    · rw [hfa] at h; exact nomatch h
    rw [hfa] at h
    rcases haa : denoteMeta acval env φ d a with _ | aa
    · rw [haa] at h; exact nomatch h
    rw [haa] at h
    obtain rfl := Option.some.inj h
    rw [denote_app, ihf hfa, iha haa]
    rfl
  | case9 d ty val body ihty ihv ihbody =>
    intro ea h
    rw [denoteMeta] at h
    rcases hta : denoteMeta acval env φ d ty with _ | ta
    · rw [hta] at h; exact nomatch h
    rw [hta] at h
    rcases hva : denoteMeta acval env φ d val with _ | va
    · rw [hva] at h; exact nomatch h
    rw [hva] at h
    rcases hba : denoteMeta acval env φ (d + 1)
        (body.instantiate1 (.fvar d ty)) with _ | ba
    · rw [hba] at h; exact nomatch h
    rw [hba] at h
    obtain rfl := Option.some.inj h
    rw [denote_letE, ihv hva, ihbody hba]
    rfl
  | case10 d sn i e ihe =>
    intro ea h
    rw [denoteMeta] at h
    rcases hea : denoteMeta acval env φ d e with _ | ea'
    · rw [hea] at h; exact nomatch h
    rw [hea] at h
    replace h : (match env.findProj? sn i with
        | some entry => some (projAV (i + entry.off) ea')
        | none => ITerm.projPair? i ea')
          = some ea := h
    rw [denote_proj, ihe hea]
    dsimp only
    cases hfp : env.findProj? sn i with
    | some entry =>
      rw [hfp] at h
      dsimp only at h ⊢
      obtain rfl := Option.some.inj h
      rw [erase_projAV]
    | none =>
      rw [hfp] at h
      dsimp only at h ⊢
      match i with
      | 0 =>
        obtain rfl := Option.some.inj h
        rfl
      | 1 =>
        obtain rfl := Option.some.inj h
        rfl
      | _ + 2 => exact nomatch h
  | case11 d k hsup =>
    intro ea h
    rw [denoteMeta, ite_eq_left hsup] at h
    obtain rfl := Option.some.inj h
    rw [denote_natLit, ite_eq_left hsup,
      natLitAV_erase (hlink _ _) (hlink _ _)]
  | case12 d k hsup =>
    intro ea h
    rw [denoteMeta, ite_eq_right hsup] at h
    exact nomatch h
  | case13 d s hsup =>
    intro ea h
    rw [denoteMeta, ite_eq_left hsup] at h
    obtain rfl := Option.some.inj h
    rw [denote_strLit, ite_eq_left hsup]
    refine congrArg some ?_ |>.symm
    show Term.app _ _ = _
    rw [ConLeche.Verify.strLitT]
    congr 1
    · exact hlink _ _
    · refine charListAV_erase ?_ ?_ (hlink _ _) (hlink _ _)
        (hlink _ _) s.toList
      · show Term.app ((acval _ _).erase) ((acval _ _).erase) = _
        rw [hlink, hlink]
      · show Term.app ((acval _ _).erase) ((acval _ _).erase) = _
        rw [hlink, hlink]
  | case14 d s hsup =>
    intro ea h
    rw [denoteMeta, ite_eq_right hsup] at h
    exact nomatch h
  | case15 d x hxs hfv hc hpi hlam happ hlet hproj hnat hstr =>
    intro ea h
    cases x with
    | bvar i => rw [denoteMeta.eq_def] at h; exact nomatch h
    | sort u => exact absurd rfl (hxs u)
    | fvar i ty => exact absurd rfl (hfv i ty)
    | const n vs => exact absurd rfl (hc n vs)
    | forallE ty b => exact absurd rfl (hpi ty b)
    | lam ty b => exact absurd rfl (hlam ty b)
    | app fe a => exact absurd rfl (happ fe a)
    | letE ty v b => exact absurd rfl (hlet ty v b)
    | proj sn i e => exact absurd rfl (hproj sn i e)
    | lit l =>
      cases l with
      | natVal k => exact absurd rfl (hnat k)
      | strVal s => exact absurd rfl (hstr s)

end ConLeche.Model
