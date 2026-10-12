module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Model.Annot.BitInst

public section

/-!
# The soundness of the three list walks (task #305)

`Certs` (one step per constructor), `DefEqList` and `EtaProjCerts`
(pointwise), at one valuation (task #342, L9).  The certificate's slot
comparison is between two types (the argument's inferred type and the
binder's domain), so the conditional `DefEqSem` decides it outright.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}

theorem Certs.nil_sound {d : Nat} {lic : Bool} {T : Expr} :
    CertsSem m φ d lic T [] := by
  intro _ Δa Ta _ vs _ _ _ hsp
  cases hsp
  exact ⟨Ta, fun _ _ _ _ hgT _ _ => ⟨.nil, hgT⟩⟩

/-- **One slot of the certificate walk, given the slot membership.**
The two `Certs` rules differ only in how the membership at `ρ` is
obtained — the licence's transfer or the certificate's run — so
everything else (the residual's reading, its frame, its grading, the
licence handed to the tail, and `TeleFitPA.cons`) is shared. -/
theorem certs_step {d : Nat} {lic : Bool} {ty body arg : Expr}
    {mb : ConLeche.BinderMeta} {rest : List Expr}
    {Δa : List AnnotTerm} {doma bodya fa aa : AnnotTerm}
    {vs' : List AnnotTerm}
    (hrest : CertsSem m φ d lic (body.instantiate1 arg) rest)
    (hCT : CtxOkS m φ d Δa (.forallE ty body mb))
    (hargs : ∀ x ∈ arg :: rest, Frame d x ∧ CtxOkS m φ d Δa x)
    (hsp' : DenoteMetaSpine m.acval env φ d rest vs')
    (hbodyw : Expr.WScoped d body)
    (hbodyb : Expr.looseBVarsBounded 1 body = true)
    (hLbty : Expr.LeavesBounded (.forallE ty body mb))
    (hbodya : denoteMeta m.acval env φ (d + 1)
      (body.instantiate1 (.fvar d ty)) = some bodya)
    (haa : denoteMeta m.acval env φ d arg = some aa)
    (hfarg : Frame d arg) (hCarg : CtxOkS m φ d Δa arg) :
    ∃ resta : AnnotTerm,
      ∀ ρ : Nat → V, Sat V Δa ρ → LeavesGr m φ d (.forallE ty body mb) ρ →
        (∀ x ∈ arg :: rest, LeavesGr m φ d x ρ) →
        WellDenotedV V ρ (.pi 0 (pwBit φ mb.pw) doma bodya) →
        (∀ x ∈ aa :: vs', WellDenotedV V ρ x) →
        (lic = true →
          WellDenotedV V ρ (AnnotTerm.mkAppN fa (aa :: vs')) ∧
            interp V ρ fa ∈ˢ interp V ρ (.pi 0 (pwBit φ mb.pw) doma bodya)) →
        interp V ρ aa ∈ˢ interp V ρ doma →
        TeleFitPA V ρ (.pi 0 (pwBit φ mb.pw) doma bodya) (aa :: vs') resta ∧
          WellDenotedV V ρ resta := by
  obtain ⟨hwa, hba, hLa⟩ := hfarg
  have hbody' : denoteMeta m.acval env φ d (body.instantiate1 arg)
      = some (bodya.inst aa) := by
    rw [denoteMeta_beta m.acval_closed (acval_inst_self m)
      (ty := ty) hbodyw.fvarsBelow hwa hba haa 0, hbodya]
    rfl
  have hLbbody : Expr.LeavesBounded (body.instantiate1 arg) := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact hLbty l (by simp [Expr.fvarLeaves, hl'])
    · exact hLa l hl'
  have hsubBody : ∀ l ∈ (body.instantiate1 arg).fvarLeaves,
      l ∈ (Expr.forallE ty body mb).fvarLeaves ∨ l ∈ arg.fvarLeaves := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact Or.inl (by simp [Expr.fvarLeaves, hl'])
    · exact Or.inr hl'
  have hCbody : CtxOkS m φ d Δa (body.instantiate1 arg) := by
    refine ⟨hCT.1, fun l hl => ?_⟩
    rcases hsubBody l hl with hl' | hl'
    · exact hCT.2 l hl'
    · exact hCarg.2 l hl'
  obtain ⟨resta, hfit⟩ :=
    hrest (fa := .app fa aa)
      ⟨ConLeche.Expr.WScoped.instantiate1_gen hwa 0 hbodyw,
        ConLeche.Expr.looseBVarsBounded_instantiate1_gen hba hbodyb, hLbbody⟩
      hCbody hbody'
      (fun x hx => hargs x (List.mem_cons_of_mem arg hx)) hsp'
  refine ⟨resta, fun ρ hρ hLT hLargs hgT hgvs hlicP hmemA => ?_⟩
  have hokA : WellDenotedV V ρ aa := hgvs aa List.mem_cons_self
  have hokBody : WellDenotedV V ρ (bodya.inst aa) :=
    (WellDenotedV_inst0 hokA).mpr (hgT.pi_body _ hmemA)
  have hLbody : LeavesGr m φ d (body.instantiate1 arg) ρ := by
    intro l hl
    rcases hsubBody l hl with hl' | hl'
    · exact hLT l hl'
    · exact hLargs arg List.mem_cons_self l hl'
  have hlicP' : lic = true →
      WellDenotedV V ρ (AnnotTerm.mkAppN (.app fa aa) vs') ∧
        interp V ρ (.app fa aa) ∈ˢ interp V ρ (bodya.inst aa) := by
    intro hl
    obtain ⟨hokS, hfaM⟩ := hlicP hl
    refine ⟨hokS, ?_⟩
    have hoks : ∀ x ∈ [aa], WellDenotedV V ρ x := by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact hokA
    exact (mkAppN_of_fitA [aa] hgT (mkAppN_head (aa :: vs') hokS)
      hoks hfaM (TeleFitPA.cons hmemA .nil)).2
  obtain ⟨hfit', hgresta⟩ := hfit ρ hρ hLbody
    (fun x hx => hLargs x (List.mem_cons_of_mem arg hx)) hokBody
    (fun x hx => hgvs x (List.mem_cons_of_mem aa hx)) hlicP'
  exact ⟨.cons hmemA hfit', hgresta⟩

/-- **The licensed walk** (`Certs.licensed`): no certificate at all.

**Owed to task #342 L18** (the S4 sorry ledger).  Under the annotated
reading only a `.never` slot transferred its argument from the head
prefix's app slot (`slotTransfer`); with no datum, the transfer holds
where the application is not the point (a graph determines its domain,
`piR_dom_unique`), so the motive needs the fragment's conditional form
(`teleFit_of_ne_pt`). -/
theorem Certs.licensed_sound {d : Nat} {T : Expr} {args : List Expr} :
    CertsSem m φ d true T args := sorry

/-- The certified slot: the certificate's run supplies the membership. -/
theorem Certs.cert_sound {d : Nat} {lic : Bool}
    {ty body arg ta : Expr} {mb : BinderMeta} {rest : List Expr}
    (hta : InferSemIO m φ d arg ta) (hd : DefEqSem m φ d ta ty)
    (hrest : CertsSem m φ d lic (body.instantiate1 arg) rest) :
    CertsSem m φ d lic (.forallE ty body mb) (arg :: rest) := by
  intro hfT Δa Ta fa vs hCT hTa hargs hsp
  obtain ⟨hwty, hbty, hLbty⟩ := hfT
  obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d ty ∧ Expr.WScoped d body := by
    simpa [Expr.WScoped] using hwty
  obtain ⟨hdomb, hbodyb⟩ :
      ty.looseBVarsBounded 0 = true ∧ Expr.looseBVarsBounded 1 body = true := by
    simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hbty
  have hLbdom : Expr.LeavesBounded ty := fun l hl =>
    hLbty l (by simp [Expr.fvarLeaves, hl])
  have hCdom : CtxOkS m φ d Δa ty := hCT.forallE_ty
  obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteMeta_forallE_inv hTa
  cases hsp with | @cons _ aa _ vs' haa hsp' =>
  obtain ⟨hfarg, hCarg⟩ := hargs arg List.mem_cons_self
  obtain ⟨resta, hstep⟩ := certs_step (fa := fa) hrest hCT hargs hsp' hbodyw
    hbodyb hLbty hbodya haa hfarg hCarg
  -- the certificate's two runs, read outside the valuation
  obtain ⟨hfta, hsubta, taA, htaA, hA⟩ := hta hfarg hCarg haa
  refine ⟨resta, fun ρ hρ hLT hLargs hgT hgvs hlicP => hstep ρ hρ hLT hLargs hgT
    hgvs hlicP ?_⟩
  have hLarg : LeavesGr m φ d arg ρ := hLargs arg List.mem_cons_self
  obtain ⟨hgtaA, hmem⟩ := hA ρ hρ hLarg (hgvs aa List.mem_cons_self)
  have hokDom : WellDenotedTy V ρ doma := hgT.pi_dom
  -- "not pt" source (1): both sides of the slot comparison are types —
  -- the argument's inferred type and the binder's domain
  have heq := hd hfta ⟨hdomw, hdomb, hLbdom⟩ (hCarg.of_subset hsubta) hCdom
    htaA hdoma ρ hρ (hLarg.of_subset hsubta) hLT.forallE_ty hgtaA.1 hokDom.1
    hgtaA.ne_pt hokDom.ne_pt
  exact heq ▸ hmem

/-! ### The full-grade certificate (task #342 L10, ι's case 3) -/

theorem CertsF.nil_sound {d : Nat} {T : Expr} : CertsFSem m φ d T [] := by
  intro _ Δa Ta vs _ _ _ hsp
  cases hsp
  exact ⟨Ta, fun _ _ _ _ hgT => ⟨by simp, .nil, hgT⟩⟩

/-- The certified slot: the full-grade inference ESTABLISHES the
argument's grading and its membership in its inferred type, a type
equal to the binder's domain ("not pt" source (1)). -/
theorem CertsF.cert_sound {d : Nat} {ty body arg ta : Expr} {mb : BinderMeta}
    {rest : List Expr}
    (hta : InferSemFull m φ d arg ta) (hd : DefEqSem m φ d ta ty)
    (hrest : CertsFSem m φ d (body.instantiate1 arg) rest) :
    CertsFSem m φ d (.forallE ty body mb) (arg :: rest) := by
  intro hfT Δa Ta vs hCT hTa hargs hsp
  obtain ⟨hwty, hbty, hLbty⟩ := hfT
  obtain ⟨hdomw, hbodyw⟩ : Expr.WScoped d ty ∧ Expr.WScoped d body := by
    simpa [Expr.WScoped] using hwty
  obtain ⟨hdomb, hbodyb⟩ :
      ty.looseBVarsBounded 0 = true ∧ Expr.looseBVarsBounded 1 body = true := by
    simpa [Expr.looseBVarsBounded, Bool.and_eq_true] using hbty
  have hLbdom : Expr.LeavesBounded ty := fun l hl =>
    hLbty l (by simp [Expr.fvarLeaves, hl])
  have hCdom : CtxOkS m φ d Δa ty := hCT.forallE_ty
  obtain ⟨doma, bodya, hdoma, hbodya, rfl⟩ := denoteMeta_forallE_inv hTa
  cases hsp with | @cons _ aa _ vs' haa hsp' =>
  obtain ⟨hfarg, hCarg⟩ := hargs arg List.mem_cons_self
  obtain ⟨hwa, hba, hLa⟩ := hfarg
  have hbody' : denoteMeta m.acval env φ d (body.instantiate1 arg)
      = some (bodya.inst aa) := by
    rw [denoteMeta_beta m.acval_closed (acval_inst_self m)
      (ty := ty) hbodyw.fvarsBelow hwa hba haa 0, hbodya]
    rfl
  have hLbbody : Expr.LeavesBounded (body.instantiate1 arg) := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact hLbty l (by simp [Expr.fvarLeaves, hl'])
    · exact hLa l hl'
  have hsubBody : ∀ l ∈ (body.instantiate1 arg).fvarLeaves,
      l ∈ (Expr.forallE ty body mb).fvarLeaves ∨ l ∈ arg.fvarLeaves := by
    intro l hl
    rcases ConLeche.Expr.fvarLeaves_instantiate1 body 0 hl with hl' | hl'
    · exact Or.inl (by simp [Expr.fvarLeaves, hl'])
    · exact Or.inr hl'
  have hCbody : CtxOkS m φ d Δa (body.instantiate1 arg) := by
    refine ⟨hCT.1, fun l hl => ?_⟩
    rcases hsubBody l hl with hl' | hl'
    · exact hCT.2 l hl'
    · exact hCarg.2 l hl'
  obtain ⟨resta, hfit⟩ :=
    hrest ⟨ConLeche.Expr.WScoped.instantiate1_gen hwa 0 hbodyw,
        ConLeche.Expr.looseBVarsBounded_instantiate1_gen hba hbodyb, hLbbody⟩
      hCbody hbody' (fun x hx => hargs x (List.mem_cons_of_mem arg hx)) hsp'
  -- the certificate's two runs, read outside the valuation
  obtain ⟨hfta, hsubta, taA, htaA, hA⟩ := hta ⟨hwa, hba, hLa⟩ hCarg haa
  refine ⟨resta, fun ρ hρ hLT hLargs hgT => ?_⟩
  have hLarg : LeavesGr m φ d arg ρ := hLargs arg List.mem_cons_self
  obtain ⟨hokA, hgtaA, hmem⟩ := hA ρ hρ hLarg
  have hokDom : WellDenotedTy V ρ doma := hgT.pi_dom
  -- "not pt" source (1): both sides of the slot comparison are types
  have heq := hd hfta ⟨hdomw, hdomb, hLbdom⟩ (hCarg.of_subset hsubta) hCdom
    htaA hdoma ρ hρ (hLarg.of_subset hsubta) hLT.forallE_ty hgtaA.1 hokDom.1
    hgtaA.ne_pt hokDom.ne_pt
  have hmemA : interp V ρ aa ∈ˢ interp V ρ doma := heq ▸ hmem
  have hokBody : WellDenotedV V ρ (bodya.inst aa) :=
    (WellDenotedV_inst0 hokA).mpr (hgT.pi_body _ hmemA)
  have hLbody : LeavesGr m φ d (body.instantiate1 arg) ρ := by
    intro l hl
    rcases hsubBody l hl with hl' | hl'
    · exact hLT l hl'
    · exact hLarg l hl'
  obtain ⟨hgvs', hfit', hgresta⟩ := hfit ρ hρ hLbody
    (fun x hx => hLargs x (List.mem_cons_of_mem arg hx)) hokBody
  refine ⟨fun x hx => ?_, .cons hmemA hfit', hgresta⟩
  rcases List.mem_cons.mp hx with rfl | hx'
  · exact hokA
  · exact hgvs' x hx'

theorem DefEqList.nil_sound {d : Nat} : DefEqListSem m φ d [] [] := by
  refine ⟨rfl, ?_⟩
  intro Δa asa bsa _ _ hsa hsb _ _ _ _ _ _ p hp
  cases hsa
  cases hsb
  simp at hp

theorem DefEqList.cons_sound {d : Nat} {a b : Expr} {as bs : List Expr}
    (h : DefEqSem m φ d a b) (hs : DefEqListSem m φ d as bs) :
    DefEqListSem m φ d (a :: as) (b :: bs) := by
  refine ⟨by simp [hs.1], ?_⟩
  intro Δa asa bsa hfa hfb hsa hsb ρ hρ hLa hLb hga hgb p hp
  cases hsa with | @cons _ va _ vas hva hsa' =>
  cases hsb with | @cons _ vb _ vbs hvb hsb' =>
  obtain ⟨hfa1, hCa1⟩ := hfa a List.mem_cons_self
  obtain ⟨hfb1, hCb1⟩ := hfb b List.mem_cons_self
  simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact h hfa1 hfb1 hCa1 hCb1 hva hvb ρ hρ (hLa a List.mem_cons_self)
      (hLb b List.mem_cons_self) (hga va List.mem_cons_self)
      (hgb vb List.mem_cons_self)
  · exact hs.2 (fun x hx => hfa x (List.mem_cons_of_mem a hx))
      (fun x hx => hfb x (List.mem_cons_of_mem b hx)) hsa' hsb' ρ hρ
      (fun x hx => hLa x (List.mem_cons_of_mem a hx))
      (fun x hx => hLb x (List.mem_cons_of_mem b hx))
      (fun x hx => hga x (List.mem_cons_of_mem va hx))
      (fun x hx => hgb x (List.mem_cons_of_mem vb hx)) p hp

theorem EtaProjCerts.nil_sound {d : Nat} {T : Name} {us' : List Level}
    {targs : List Expr} {b : Expr} {lpsT : List Name} :
    EtaProjCertsSem m φ d T us' targs b lpsT [] := by
  intro i hi
  exact nomatch hi

theorem EtaProjCerts.cons_sound {d : Nat} {T : Name} {us' : List Level}
    {targs : List Expr} {b : Expr} {lpsT : List Name} {i : Nat}
    {rest : List Nat} {cvp : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    (hf : env.find? (projFnName T i) = some (.recInfo cvp mI rP rules))
    (hlps : cvp.levelParams = lpsT)
    (hstrip : (cvp.type.stripPis (targs.length + 1)).isSome = true)
    (hcerts : CertsSem m φ d false
      (cvp.type.instantiateLevelParams cvp.levelParams us') (targs ++ [b]))
    (hrest : EtaProjCertsSem m φ d T us' targs b lpsT rest) :
    EtaProjCertsSem m φ d T us' targs b lpsT (i :: rest) := by
  intro j hj
  rcases List.mem_cons.mp hj with rfl | hj'
  · exact ⟨cvp, mI, rP, rules, hf, hlps, hstrip, hcerts⟩
  · exact hrest j hj'

end ConLeche.Model.Rules
