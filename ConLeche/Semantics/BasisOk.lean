module

public import ConLeche.Semantics.BasisType
import ConLeche.Semantics.Interp
import ConLeche.Semantics.Univ
public import ConLeche.Semantics.WellDenoted

@[expose] public section

/-!
# `bval_mem_type` — every built-in inhabits its annotated type

The skeleton's `const` row's supplier: every built-in's value lies in
the reading of `BConst.typeAV`, over `piR`/`lamR`.

## The proof pattern

Each case is three moves, and the first two are mechanical:

1. `show` the value at its own tower (`bval` is a `match`, so this is
   definitional);
2. `simp only` with `BConst.typeAV`, the smart constructors it mentions,
   and the `interp` clause equations — this reduces
   `interp ρ (typeAV c us)` to the tower's *own space*, which is the
   whole point of having read the numeral convention off `Value.lean`
   rather than choosing one;
3. apply the tower's membership argument — `lamR_mem` down the
   binders, then the constant's own semantic fact.

No universe side condition is needed: `lamR_mem` has no premise beyond
the fibres and `app_mem_piR_pos` none at all.  `Empty.rec` is a *graph*
(`emptyRecV = lamR v … (lamR v ∅ …)`), so its case is two `lamR_mem`s
over a vacuous domain rather than a proof-point argument.

## The `Nat.succ` wrinkle

`typeAV`'s step premise mentions `Nat.succ`'s *value*
(`natSuccAV (.bvar 1)` interprets to `app (natSuccV V) n`) while
`natStepSpace` is written with the operator `natsucc`.  They agree on
`ω`, which is what the outer product quantifies over
(`natStepSpace_eq`).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.Term (BConst lv)
open ConLeche.SetTheory.Tower (mkTower projS)

universe w

variable (V : Type w) [SetTheory V]

/-! ## `Nat` -/

theorem bval_mem_nat (us : List Nat) (ρ : Nat → V) :
    bval V .nat us ∈ˢ interp V ρ (BConst.typeAV .nat us) := by
  show (omega : V) ∈ˢ _
  simp only [BConst.typeAV, interp_sort]
  exact omega_mem_univ_succ 0

theorem bval_mem_natZero (us : List Nat) (ρ : Nat → V) :
    bval V .natZero us ∈ˢ interp V ρ (BConst.typeAV .natZero us) := by
  show natzero ∈ˢ _
  simp only [BConst.typeAV, natTyAV, interp_const, bval]
  exact natzero_mem

theorem bval_mem_natSucc (us : List Nat) (ρ : Nat → V) :
    bval V .natSucc us ∈ˢ interp V ρ (BConst.typeAV .natSucc us) := by
  sorry

/-- The step space as `interp` produces it (with `Nat.succ`'s *value*
applied) is the one the tower is written with (`natsucc`): they agree
on `ω`. -/
theorem natStepSpace_eq {u : Nat} (M : V) :
    (piR u (omega : V) fun n =>
        piR u (app M n) fun _ => app M (app (natSuccV V) n))
      = natStepSpace V u M :=
  piR_congr fun n hn => by rw [natSuccV_app V hn]

/-- `Nat.rec`'s type, as `interp` produces it. -/
theorem interp_type_natRec (us : List Nat) (ρ : Nat → V) :
    interp V ρ (BConst.typeAV .natRec us) =
      piR (lv us 0) (natMotiveSpace V (lv us 0)) fun M =>
        piR (lv us 0) (app M natzero) fun _ =>
          piR (lv us 0) (natStepSpace V (lv us 0) M) fun _ =>
            piR (lv us 0) omega fun n => app M n := by
  sorry

theorem bval_mem_natRec (us : List Nat) (ρ : Nat → V) :
    bval V .natRec us ∈ˢ interp V ρ (BConst.typeAV .natRec us) := by
  rw [interp_type_natRec]
  show natRecV V (lv us 0) ∈ˢ _
  refine lamR_mem fun M hM => lamR_mem fun z hz =>
    lamR_mem fun s hs => ?_
  refine lamR_mem fun n hn => ?_
  exact natRecV_mem_fibre V hM hz hs hn

/-! ## `PUnit` -/

theorem bval_mem_punit (us : List Nat) (ρ : Nat → V) :
    bval V .punit us ∈ˢ interp V ρ (BConst.typeAV .punit us) := by
  show (unitSetAt (lv us 0) : V) ∈ˢ _
  simp only [BConst.typeAV, interp_sort]
  exact unitSetAt_mem_univ _

theorem bval_mem_punitUnit (us : List Nat) (ρ : Nat → V) :
    bval V .punitUnit us
      ∈ˢ interp V ρ (BConst.typeAV .punitUnit us) := by
  show (unitAt (lv us 0) : V) ∈ˢ _
  simp only [BConst.typeAV, punitAV, interp_const, bval]
  exact unitAt_mem_unitSetAt _

/-! ## `Empty` -/

theorem bval_mem_empty (us : List Nat) (ρ : Nat → V) :
    bval V .empty us ∈ˢ interp V ρ (BConst.typeAV .empty us) := by
  show (empty : V) ∈ˢ _
  simp only [BConst.typeAV, interp_sort]
  exact empty_mem_univ _

theorem bval_mem_emptyRec (us : List Nat) (ρ : Nat → V) :
    bval V .emptyRec us
      ∈ˢ interp V ρ (BConst.typeAV .emptyRec us) := by
  sorry

/-! ## The dependent pair `.psigma` -/

theorem bval_mem_psigma (us : List Nat) (ρ : Nat → V) :
    bval V .psigma us ∈ˢ interp V ρ (BConst.typeAV .psigma us) := by
  sorry

/-- **`.psigmaMk`** — the case the proof pattern does not reach.
`psigmaMkV`'s body carries no `if max u v = 0 then pt` tag (the
annotation squashes the tower instead), so the innermost pointwise
obligation would be `spair a b ∈ˢ sigmaSet 0 A B'` — **false**, since a
kind-`0` `sigmaSet` is a truth value and `spair a b ≠ pt`.  The kind-`0`
argument therefore moves from the leaf to the root: split first, then
exhibit the tower's *inhabitation* with `pt_mem_piR_zero`. -/
theorem bval_mem_psigmaMk (us : List Nat) (ρ : Nat → V) :
    bval V .psigmaMk us
      ∈ˢ interp V ρ (BConst.typeAV .psigmaMk us) := by
  sorry

/-! ## `Quot` -/

theorem bval_mem_quot (us : List Nat) (ρ : Nat → V) :
    bval V .quot us ∈ˢ interp V ρ (BConst.typeAV .quot us) := by
  sorry

theorem bval_mem_quotMk (us : List Nat) (ρ : Nat → V) :
    bval V .quotMk us ∈ˢ interp V ρ (BConst.typeAV .quotMk us) := by
  sorry

/-- **`Quot.lift`** — six binders, five of them `lamR_mem`, and the
tail is `quotLiftR_mem`.  Its kind-`0` fibre premise comes from the
third binder (`B ∈ˢ univ v`, and `univ 0 = univZero`), so nothing new
is needed. -/
theorem bval_mem_quotLift (us : List Nat) (ρ : Nat → V) :
    bval V .quotLift us
      ∈ˢ interp V ρ (BConst.typeAV .quotLift us) := by
  sorry

/-! ## The `pt`-valued propositions

`Quot.ind`, `Quot.sound` and `propext` have `bval = pt`, so their
cases are *inhabitation* arguments rather than typings: every binder is
`piR 0`, closed by `pt_mem_piR_zero_of`. -/

theorem bval_mem_quotInd (us : List Nat) (ρ : Nat → V) :
    bval V .quotInd us ∈ˢ interp V ρ (BConst.typeAV .quotInd us) := by
  sorry

theorem bval_mem_quotSound (us : List Nat) (ρ : Nat → V) :
    bval V .quotSound us
      ∈ˢ interp V ρ (BConst.typeAV .quotSound us) := by
  sorry

theorem bval_mem_propext (us : List Nat) (ρ : Nat → V) :
    bval V .propext us ∈ˢ interp V ρ (BConst.typeAV .propext us) := by
  sorry

/-! ## `Classical.choice` -/

theorem bval_mem_choice (us : List Nat) (ρ : Nat → V) :
    bval V .choice us ∈ˢ interp V ρ (BConst.typeAV .choice us) := by
  sorry

/-! ## `lfpFam` (task #188) -/

theorem bval_mem_lfpFam (us : List Nat) (ρ : Nat → V) :
    bval V .lfpFam us ∈ˢ interp V ρ (BConst.typeAV .lfpFam us) := by
  sorry

/-! ## `lfpTuple k` (#315)

The block carrier's constant binds two pair towers — the index-set
tuple `Is` and the family tuple — and reads the members' index sets off
`Is` with `projAV`.  Both towers are non-dependent (`ndTowerAV`), so
their readings and gradings need only that each component reads to the
carrier's own at the tower's depth and is itself graded; the tower's app slots are supplied by the `[r, r]`
instance of the pinned pair former's product membership, exactly as the
dependent tower kit's are. -/

/-- **The uniform projection spelling reads back as `projS`** — the
definitional commutation, no premises at all (matching the tier's
unconditional iota discipline). -/
theorem projAV_interp :
    ∀ (i : Nat) (e : AnnotTerm) (ρ : Nat → V),
      interp V ρ (projAV i e) = projS i (interp V ρ e)
  | 0, _, _ => rfl
  | i + 1, e, ρ => by
    show interp V ρ (projAV i (.snd e)) = projS i (ssnd (interp V ρ e))
    rw [projAV_interp i (.snd e) ρ]
    rfl

/-- The `[r, r]` instance of the pinned pair former's product
membership (`sigma_mem_univ` at the joint level `max r r = r`). -/
theorem psigmaV_rr_mem (r : Nat) :
    psigmaV V r r ∈ˢ piR (r + 1) (univ r : V)
      (fun A => piR (r + 1) (psigmaFibreSpace V r A) fun _ => (univ r : V)) := by
  rw [psigmaV, show Nat.max r r = r from Nat.max_self r]
  exact lamR_mem fun A hA => lamR_mem fun B hB => by
    have h := sigma_mem_univ (u := r) (v := r) hA
      (fun x hx => psigmaFibre_apply V hB hx)
    rwa [show Nat.max r r = r from Nat.max_self r] at h

/-- **The non-dependent tower reads back as its carrier.**  Its
components are read at the BASE frame `ρ` — the former lifted them to
their depth, so the tower's own binders do not reach them. -/
theorem ndTowerAV_interp {r : Nat} {F : Nat → V} {G : Nat → AnnotTerm} {ρ : Nat → V} :
    ∀ (n s d : Nat) (σ : Nat → V), shiftE d 0 σ = ρ →
      (∀ m, m < s + n → interp V ρ (G m) = F m) →
      (∀ m, m < s + n → F m ∈ˢ (univ r : V)) →
      interp V σ (ndTowerAV r G s d n) = ndTowerSet V r F s n := by
  sorry

/-- **The non-dependent tower is graded** (`WellDenoted`). -/
theorem ndTowerAV_wellDenoted {r : Nat} {F : Nat → V} {G : Nat → AnnotTerm} {ρ : Nat → V} :
    ∀ (n s d : Nat) (σ : Nat → V), shiftE d 0 σ = ρ →
      (∀ m, m < s + n → interp V ρ (G m) = F m) →
      (∀ m, m < s + n → WellDenoted V ρ (G m)) →
      (∀ m, m < s + n → F m ∈ˢ (univ r : V)) →
      WellDenoted V σ (ndTowerAV r G s d n) := by
  sorry

/-- **The projection chain into a tower is graded.** -/
theorem projAV_wellDenoted_ndTower {r : Nat} (hr : r ≠ 0) {F : Nat → V} :
    ∀ (i n s : Nat) (e : AnnotTerm) (ρ : Nat → V), i < n →
      (∀ m, m < s + n → F m ∈ˢ (univ r : V)) →
      WellDenoted V ρ e → interp V ρ e ∈ˢ ndTowerSet V r F s n →
      WellDenoted V ρ (projAV i e)
  | _, 0, _, _, _, hi, _, _, _ => absurd hi (Nat.not_lt_zero _)
  | 0, n + 1, s, e, ρ, _, hF, hok, he => by
    have he' : interp V ρ e ∈ˢ sigmaSet r (F s) fun _ => ndTowerSet V r F (s + 1) n := he
    show WellDenoted V ρ (.fst e)
    rw [WellDenoted_fst]
    refine ⟨hok, r, r, F s, (fun _ => ndTowerSet V r F (s + 1) n), ?_, hF s (by omega),
      fun _ _ => ndTowerSet_mem_univ V n (s + 1) fun m hm => hF m (by omega)⟩
    rwa [show Nat.max r r = r from Nat.max_self r]
  | i + 1, n + 1, s, e, ρ, hi, hF, hok, he => by
    have he' : interp V ρ e ∈ˢ sigmaSet r (F s) fun _ => ndTowerSet V r F (s + 1) n := he
    obtain ⟨a, b, ha, hb, -, hpos⟩ := mem_sigma_elim he'
    have hsnd : WellDenoted V ρ (.snd e) := by
      rw [WellDenoted_snd]
      refine ⟨hok, r, r, F s, (fun _ => ndTowerSet V r F (s + 1) n), ?_, hF s (by omega),
        fun _ _ => ndTowerSet_mem_univ V n (s + 1) fun m hm => hF m (by omega)⟩
      rwa [show Nat.max r r = r from Nat.max_self r]
    have hmem : interp V ρ (.snd e) ∈ˢ ndTowerSet V r F (s + 1) n := by
      show ssnd (interp V ρ e) ∈ˢ _
      rw [hpos hr, ssnd_spair]
      exact hb
    exact projAV_wellDenoted_ndTower hr i n (s + 1) (.snd e) ρ
      (Nat.lt_of_succ_lt_succ hi) (fun m hm => hF m (by omega)) hsnd hmem

/-! ### The two towers of `lfpTuple k`'s type -/

/-- **The index-set tuple's type**: its value and its grading, at every
environment (its components are closed sorts). -/
theorem tupleSortsAV_facts (k : Nat) (us : List Nat) (ρ : Nat → V) :
    interp V ρ (tupleSortsAV k us) = tupleSortsSpace V k us ∧
      WellDenoted V ρ (tupleSortsAV k us) :=
  ⟨ndTowerAV_interp V (ρ := ρ) k 0 0 ρ (shiftE_zero_zero ρ) (fun _ _ => rfl)
      (fun m _ => univ_lv_mem_tupleIdxSort V us m),
   ndTowerAV_wellDenoted V (ρ := ρ) k 0 0 ρ (shiftE_zero_zero ρ) (fun _ _ => rfl)
      (fun _ _ => trivial) (fun m _ => univ_lv_mem_tupleIdxSort V us m)⟩

/-- The family tuple's components live in the family tuple's own
universe, below `k`. -/
theorem famComp_mem_univ {k : Nat} {us : List Nat} {Is : V}
    (hIs : Is ∈ˢ tupleSortsSpace V k us) (m : Nat) (hm : m < k) :
    lfpFamSpace V (lv us k) (projS m Is) ∈ˢ (univ (ConLeche.Term.tupleFamSort k us) : V) := by
  have hproj : projS m Is ∈ˢ (univ (lv us m) : V) := by
    have := projS_mem_ndTowerSet V (tupleIdxSort_ne_zero us) k 0 hIs m hm
    rwa [Nat.zero_add] at this
  have h := piR_mem_univ (u := lv us m) (v := lv us k + 1) hproj
    (fun _ _ => univ_mem_univ (lv us k))
  rw [ite_eq_right (Nat.succ_ne_zero _)] at h
  refine univ_mono ?_ _ h
  refine Nat.max_le_of_le_of_le ?_ ?_
  · exact Nat.le_trans (ConLeche.Term.lv_le_levMax us m) (Nat.le_max_left _ _)
  · exact Nat.le_max_right _ _

/-- The index-set tuples are a type. -/
theorem IsTy_tupleSortsSpace (k : Nat) (us : List Nat) : IsTy (tupleSortsSpace V k us) :=
  IsTy_of_mem_univ (ndTowerSet_mem_univ V k 0 fun m _ => univ_lv_mem_tupleIdxSort V us m)

/-- The family tuples at an index-set tuple are a type. -/
theorem IsTy_tupleFamsSpace {k : Nat} {us : List Nat} {Is : V}
    (hIs : Is ∈ˢ tupleSortsSpace V k us) : IsTy (tupleFamsSpace V k us Is) :=
  IsTy_of_mem_univ (ndTowerSet_mem_univ V k 0 fun m hm => famComp_mem_univ V hIs m (by omega))

/-- **The family tuple's type**: its value and its grading, at an
environment whose `j`-th variable is an index-set tuple. -/
theorem tupleFamsAV_facts {k : Nat} {us : List Nat} {j : Nat} {ρ : Nat → V}
    (hIs : ρ j ∈ˢ tupleSortsSpace V k us) :
    interp V ρ (tupleFamsAV k us j) = tupleFamsSpace V k us (ρ j) ∧
      WellDenoted V ρ (tupleFamsAV k us j) := by
  sorry

theorem bval_mem_lfpTuple (k : Nat) (us : List Nat) (ρ : Nat → V) :
    bval V (.lfpTuple k) us ∈ˢ interp V ρ (BConst.typeAV (.lfpTuple k) us) := by
  sorry

/-! ## The capstone

`bval_mem_type`, over `interp` and `BConst.typeAV`: what the skeleton's
`const` row waits on. -/

/-- **Every built-in constant inhabits its annotated type.** -/
theorem bval_mem_type (c : BConst) (us : List Nat) (ρ : Nat → V) :
    bval V c us ∈ˢ interp V ρ (BConst.typeAV c us) := by
  cases c with
  | nat => exact bval_mem_nat V us ρ
  | natZero => exact bval_mem_natZero V us ρ
  | natSucc => exact bval_mem_natSucc V us ρ
  | natRec => exact bval_mem_natRec V us ρ
  | punit => exact bval_mem_punit V us ρ
  | punitUnit => exact bval_mem_punitUnit V us ρ
  | psigma => exact bval_mem_psigma V us ρ
  | psigmaMk => exact bval_mem_psigmaMk V us ρ
  | empty => exact bval_mem_empty V us ρ
  | emptyRec => exact bval_mem_emptyRec V us ρ
  | quot => exact bval_mem_quot V us ρ
  | quotMk => exact bval_mem_quotMk V us ρ
  | quotLift => exact bval_mem_quotLift V us ρ
  | quotInd => exact bval_mem_quotInd V us ρ
  | quotSound => exact bval_mem_quotSound V us ρ
  | propext => exact bval_mem_propext V us ρ
  | choice => exact bval_mem_choice V us ρ
  | lfpFam => exact bval_mem_lfpFam V us ρ
  | lfpTuple k => exact bval_mem_lfpTuple V k us ρ

end ConLeche.Semantics
