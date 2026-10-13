module

public import ConLeche.Cached.CheckerC

@[expose] public section

/-!
# The parsed-declaration driver on the cached representation

One `CState` for the whole stream, the environment-dependent caches
flushed per declaration, declarations consumed as `Declaration` records
straight from the direct parse (`ConLeche/Frontend/ExportC.lean`, task
#171 — no conversion detour).

`checkDeclStepC` is the fold's step for every declaration kind that is
checked as it is installed: axioms, inductive and basis blocks, the
pinned `Nat`-operation definitions and `reduce*` opaques.  The
declaration fold itself, `checkDecls` (`ConLeche/Cached/Installed.lean`),
installs every record first (a separable value declaration — every
theorem, every other definition and opaque — by its own install half,
pushed with its check recorded; everything else by this step) and
checks the recorded declarations afterwards, so this step never sees a
separable value declaration: it throws an internal error on one; the
binary's driver (`ConLeche/Driver/*`) runs that fold with a heartbeat between
the steps and returns its environment together with the proof that
`checkDecls` returns it.  The fold runs at `.verified` and at
`.trusted` alike (the trusted mode is the same fold at the other
mode, and nothing else): acceptance at
`.verified` is covered by the main corollary
`no_False_declaration` (`ConLeche/MainTheorem.lean`, through
`no_False_theorem_accepted` in `ConLeche/Verify/Cached/StreamThm.lean`), and the two
modes agree on the install skeletons whenever both accept
(`trusted_agrees_skels_D`, `ConLeche/Verify/Cached/AgreeFloor.lean`).

The driver's parameter is the `CheckMode` itself (task #185): the knot it
ties (`coreKnotI mode`) and the install-time stages all take the same
mode.
-/

namespace ConLeche.Cached

open ConLeche

/-! ## The parsed-declaration checker -/

variable (mode : CheckMode)

/-- Parsed `ensureSort` (no per-call conversion). -/
def opSIxC (fe : FEnv) (d : Nat) (i : Expr) : CheckCM Level :=
  ensureSortI (coreKnotI mode fe checkFuel) d i

/-- `checkConstantVal` on a parsed declaration: the checks of
`checkConstantValF` with the syntactic passes memoized on the `Expr`
DAG and the cached operations on its nodes. -/
def checkConstantValC (fe : FEnv) (cv : ConstantVal) :
    CheckCM Unit := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  if cv.name.isProjFnShape then
    throw (.invalid s!"reserved projection name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless Expr.looseBVarsBounded 0 cv.type do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if Expr.hasFvar cv.type then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  unless Expr.allLevelParamsDefinedC cv.levelParams cv.type do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC fe cv.type do
    throw (unresolvedConstsErrorL (strLitSupportedF fe) s!"type of {cv.name}" cv.type)
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 cv.type
  let _u ← opSIxC mode fe 0 jsty

/-- `checkShapeless` (`ConLeche/Kernel/CheckDecl.lean`) through the index:
a block the recogniser does not read has its type formers checked as
constants, then declines.  It never returns an index. -/
def checkShapelessS (fe : FEnv) (block : List ConstantInfo) : CheckCM FEnv := do
  block.foldlM (fun (_ : Unit) ci => match ci with
    | .indInfo cv _ => discard <| checkConstantValC mode fe cv
    | _ => pure ()) ()
  throw (.notImplemented s!"inductive block \
    {(block.head?.map (·.name)).getD .anonymous}: shape not recognised")

/-- Check a definition's value against its declared type, returning the
record to install, unpushed: the pinned `Nat`-operation arm of
`checkDeclC` certifies against an overlay before it pushes. -/
def checkDefnValCI (fe : FEnv) (cvA : ConstantVal)
    (value : Expr) (hint : ReducibilityHint) : CheckCM ConstantInfo := do
  unless Expr.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv := value
  unless Expr.allLevelParamsDefinedC cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (unresolvedConstsErrorL (strLitSupportedF fe) s!"value of {cvA.name}" jv)
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt cvA.type do
    throw (.invalid s!"type mismatch in definition {cvA.name}")
  pure (.defnInfo cvA jv hint)

/-- Check an opaque's value against its declared type, returning the
axiom record to install, unpushed (as `checkDefnValCI`). -/
def checkOpaqueValCI (fe : FEnv) (cvA : ConstantVal)
    (value : Expr) : CheckCM ConstantInfo := do
  unless Expr.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv := value
  unless Expr.allLevelParamsDefinedC cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (unresolvedConstsErrorL (strLitSupportedF fe) s!"value of {cvA.name}" jv)
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt cvA.type do
    throw (.invalid s!"type mismatch in opaque {cvA.name}")
  pure (.axiomInfo cvA)

/-- `checkBasisDecl`'s cached twin: the body the three records that
install a pinned basis block share (task #293). -/
def checkBasisDeclC (fe : FEnv) (kind : BasisKind) : CheckCM FEnv := do
  if kind = .quotK then
    unless fe.find? eqName = some eqA do
      throw (.notImplemented "quotient basis requires the pinned Eq basis")
  kind.declsA.foldlM installBasisDeclF fe

/-- One converted declaration (inductive and basis blocks reuse the
`Expr`-level drivers).  A separable value declaration (a theorem, a
definition other than a pinned `Nat` operation, an opaque other than a
`reduce*` one) never reaches it — phase A installs it by its install
half (`installStepC`, `ConLeche/Cached/Installed.lean`) — and is an
internal error here.
`pins` is the `Nat.div`/`Nat.mod` pin-variant list the install gate
tries (task #304), threaded from the fold.

**The pinned arms push last.**  A pinned `Nat`-operation definition and
a `reduce*` opaque are certified against the environment before the
push (`fe`) AND after it.  Holding both alive across a push would copy
the whole index, so the value check returns the record unpushed
(`checkDefnValCI`, `checkOpaqueValCI`), the "after" environment is an
overlay sharing `fe`'s index (`FEnv.overlay`, read-only; on the
install's environments it answers `find?` as the push would,
`find?_overlay_push`), and the push comes last, onto an index nothing
else holds. -/
def checkDeclC (pins : List NatOpPinSet) (fe : FEnv) (pd : Declaration) :
    CheckCM FEnv :=
  match pd with
  | .defnDecl cv value hint => do
    checkConstantValC mode fe cv
    let cvA := cv
    if natOpNames.contains cvA.name || natDivModNames.contains cvA.name then
      let ci ← checkDefnValCI mode fe cvA value hint
      let fe2 := fe.overlay [ci]
      if natOpNames.contains cvA.name then
        unless natOpGuardF fe2 cvA.name &&
            (natOpDeps cvA.name).all (natOpStoredOkF fe2) do
          throw (.notImplemented
            s!"nonstandard structural Nat operation environment ({cvA.name})")
        match fe2.find? cvA.name with
        | some (.defnInfo _ value' _) =>
          let ok ← certifyNatEqs (sharedOpsC mode fe) fe.env
            ((natOpEquations 0 cvA.name).map fun eq =>
              (Expr.substConst0 cvA.name value' eq.1,
               Expr.substConst0 cvA.name value' eq.2))
          unless ok do
            throw (.notImplemented
              s!"nonstandard structural Nat operation ({cvA.name})")
        | _ => throw (.internal
            s!"structural Nat operation not stored ({cvA.name})")
      if natDivModNames.contains cvA.name then
        checkDivModPinF (sharedOpsC mode fe) pins fe fe2 cvA.name
      pure (fe.push ci)
    else
      throw (.internal s!"definition {cvA.name} reached the ordinary step")
  | .thmDecl cv _ =>
    throw (.internal s!"theorem {cv.name} reached the ordinary step")
  | .opaqueDecl cv value => do
    checkConstantValC mode fe cv
    let cvA := cv
    -- only a `reduce*` opaque reaches this step: phase A installs the
    -- others (`installStepC`)
    if reduceOpNames.contains cvA.name then do
      let ci ← checkOpaqueValCI mode fe cvA value
      checkReducePinF (sharedOpsC mode fe) fe (fe.overlay [ci]) cvA.name value
      pure (fe.push ci)
    else
      throw (.internal s!"opaque {cvA.name} reached the ordinary step")
  | .axiomDecl cv =>
    -- `checkDecl`'s twin (task #293): `Quot.sound` is the pinned
    -- quotient block's own record — compared with the pin, installing
    -- nothing, declining on a mismatch.
    if cv.name = quotSoundName then
      (if ConstantInfo.canonEq (.axiomInfo cv) (quotBasis.getD 4 (.axiomInfo default)) then
        pure fe
      else
        throw (.notImplemented "quotient soundness axiom mismatch"))
    else do
      checkConstantValC mode fe cv
      let cvA := cv
      if stdAxiomOkF fe cvA then
        pure (fe.push (.axiomInfo cvA))
      else if cvA.name = trustCompilerName then
        if trustCompilerOkF fe cvA then
          pure (fe.push (.axiomInfo cvA))
        else throw (.notImplemented
          s!"unsupported Lean.trustCompiler shape ({cv.name})")
      else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
        if ofReduceAxOkF fe cvA then
          pure (fe.push (.axiomInfo cvA))
        else throw (.notImplemented
          s!"unsupported compiler-trust axiom environment ({cv.name})")
      else if cvA.name = propextName ∨ cvA.name = choiceName then
        throw (.notImplemented s!"standard axiom shape mismatch ({cv.name})")
      else if cvA.name = sorryAxName then
        pure fe
      else
        throw (.notImplemented s!"non-standard axiom ({cv.name})")
  | .basisDecl kind => checkBasisDeclC fe kind
  | .indDecl block nP =>
    -- **THE PINNED BASIS BLOCKS** (`checkDecl`'s twin, task #293): the
    -- stream's own `Nat` block, recognised here and installed as the
    -- pin; a block under a pinned name that does not match falls
    -- through and the reserved-name check rejects it.
    match basisPinHit block with
    | some kind => checkBasisDeclC fe kind
    | none =>
    -- TASK #228: the stream's DECLARED parameter count, checked before
    -- the dispatch (`checkDecl`'s twin).
    if indParamsOk nP block then
      -- ONE ROUTE (task #210), dispatched by the RECOGNISER alone (task
      -- #219): a recognised block is the installer's, nested ones
      -- included; any other declines (`checkShapelessS`).
      match blockParts? nP block with
      | some p => checkBlockKS mode fe block p
      | none => checkShapelessS mode fe block
    else throw (.invalid "number of parameters mismatch")
  | .quotDecl k cv =>
    -- `checkDecl`'s twin (task #293): the `type` record installs the
    -- pinned block whole, the other members install nothing, and a
    -- record that does not match its pin is a positive decline.
    if quotPinHit k cv then
      (match k with
       | .type => checkBasisDeclC fe .quotK
       | _ => pure fe)
    else throw (.notImplemented (match k with
      | .sound => "quotient soundness axiom mismatch"
      | _ => "quotient declaration mismatch"))

/-! ## Names and durations for the driver's messages -/

/-- Milliseconds as `s.d` seconds (`12345` ↦ `"12.3"`).  `Nat`
arithmetic — no `Float` formatting on a message path. -/
def msSecs (ms : Nat) : String := s!"{ms / 1000}.{(ms % 1000) / 100}"

/-- A parsed declaration's display label (`ConLeche.Driver.declCName`,
shared with the driver's progress callback so the two can never
drift). -/
def declCLabel : Declaration → String
  | .defnDecl cv _ _ => s!"def {cv.name}"
  | .thmDecl cv _ => s!"theorem {cv.name}"
  | .opaqueDecl cv _ => s!"opaque {cv.name}"
  | .axiomDecl cv => s!"axiom {cv.name}"
  | .indDecl b _ => s!"inductive {(b.head?.map (·.name)).getD .anonymous}"
  | .basisDecl k => s!"basis block {repr k}"
  | .quotDecl _ cv => s!"quot {cv.name}"

/-- One step of the converted-declaration fold: flush, then check. -/
def checkDeclStepC (pins : List NatOpPinSet) (fe : FEnv) (pd : Declaration) :
    CheckCM FEnv := do
  flushC
  checkDeclC mode pins fe pd

end ConLeche.Cached
