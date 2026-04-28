import Vegas.FOSG.Observed.Behavioral

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace Observed
/-! ## Pure profile candidate

The pure transport is the deterministic counterpart of the behavioral transport
above. It is needed to state the Kuhn correspondence against GameTheory's FOSG
strategy API without weakening the Vegas strategy spaces.
-/

noncomputable def movePureAtProgramCursor
    (g : WFProgram P L) (_hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P)
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p)
    (view : ViewEnv who Γ) :
    Option (ProgramAction g.prog who) :=
  match p with
  | .commit x owner (b := b) R k =>
      if howner : owner = who then
        by
          cases howner
          let σp : ProgramPureProfile (.commit x who R k) :=
            suffix.pureProfile (fun i => (σ i).val)
          exact some
            (ProgramAction.commitAt suffix
              ((ProgramPureStrategy.headKernel (σp who)) view))
      else
        none
  | _ => none

noncomputable def movePureStrategyAtProgramCursor
    (g : WFProgram P L) (_hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p)
    (view : ViewEnv who Γ) :
    Option (ProgramAction g.prog who) :=
  match p with
  | .commit x owner (b := b) R k =>
      if howner : owner = who then
        by
          cases howner
          let σp : ProgramPureStrategy (P := P) (L := L) who
              (.commit x who R k) :=
            suffix.pureStrategy who σ.val
          exact some
            (ProgramAction.commitAt suffix
              ((ProgramPureStrategy.headKernel (σp)) view))
      else
        none
  | _ => none

theorem movePureAtProgramCursor_eq_strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P) {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p)
    (view : ViewEnv who Γ) :
    movePureAtProgramCursor g hctx σ who suffix view =
      movePureStrategyAtProgramCursor g hctx who (σ who) suffix view := by
  cases p with
  | ret payoffs =>
      simp [movePureAtProgramCursor, movePureStrategyAtProgramCursor]
  | letExpr x e k =>
      simp [movePureAtProgramCursor, movePureStrategyAtProgramCursor]
  | sample x D k =>
      simp [movePureAtProgramCursor, movePureStrategyAtProgramCursor]
  | reveal y owner x hx k =>
      simp [movePureAtProgramCursor, movePureStrategyAtProgramCursor]
  | commit x owner R k =>
      by_cases howner : owner = who
      · cases howner
        simp [movePureAtProgramCursor, movePureStrategyAtProgramCursor,
          ProgramSuffix.pureProfile_apply]
      · simp [movePureAtProgramCursor, movePureStrategyAtProgramCursor, howner]

@[simp] theorem movePureAtProgramCursor_commit_owner
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (view : ViewEnv who Γ) :
    movePureAtProgramCursor g hctx σ who suffix view =
      some
        (ProgramAction.commitAt suffix
          ((ProgramPureStrategy.headKernel (P := P) (L := L)
            ((suffix.pureProfile (fun i => (σ i).val)) who)) view)) := by
  simp [movePureAtProgramCursor]

theorem headPureKernel_legal_atCursor
    (g : WFProgram P L) (_hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (ρ : Env L.Val (eraseVCtx Γ)) :
    evalGuard (Player := P) (L := L) R
      ((ProgramPureStrategy.headKernel (P := P) (L := L)
        ((suffix.pureProfile (fun i => (σ i).val)) who))
        (projectViewEnv who ρ)) ρ = true := by
  let raw : ProgramPureProfile g.prog :=
    fun i => (σ i).val
  have hraw : raw.IsLegal := fun i => (σ i).2
  have hcursor : (suffix.pureProfile raw).IsLegal :=
    suffix.pureProfile_isLegal hraw
  have hsite := hcursor who
  simp [ProgramPureStrategy.IsLegal] at hsite
  simpa [raw] using hsite.1 ρ

theorem headPureStrategyKernel_legal_atCursor
    (g : WFProgram P L) (_hctx : WFCtx g.Γ)
    {who : P} (σ : LegalProgramPureStrategy g who)
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (ρ : Env L.Val (eraseVCtx Γ)) :
    evalGuard (Player := P) (L := L) R
      ((ProgramPureStrategy.headKernel (P := P) (L := L)
        (suffix.pureStrategy who σ.val))
        (projectViewEnv who ρ)) ρ = true := by
  have hcursor :
      (suffix.pureStrategy who σ.val).IsLegal
        (.commit x who R k) :=
    suffix.pureStrategy_isLegal who σ.2
  let σc :
      PureKernel (P := P) (L := L) who Γ b ×
        ProgramPureStrategy (P := P) (L := L) who k := by
    simpa [ProgramPureStrategy] using suffix.pureStrategy who σ.val
  have hsite :
      σc.1.IsLegalAt (P := P) (L := L) (x := x) (who := who)
          (b := b) R ∧ σc.2.IsLegal k := by
    simpa [ProgramPureStrategy.IsLegal, σc] using hcursor
  simpa [ProgramPureStrategy.headKernel, σc] using hsite.1 ρ

noncomputable def movePureAtCursorWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P) (w : CursorCheckedWorld g) :
    Option (ProgramAction g.prog who) :=
  movePureAtProgramCursor g hctx σ who w.1.suffix
    (projectViewEnv who (VEnv.eraseEnv w.1.env))

noncomputable def movePureStrategyAtCursorWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (w : CursorCheckedWorld g) :
    Option (ProgramAction g.prog who) :=
  movePureStrategyAtProgramCursor g hctx who σ w.1.suffix
    (projectViewEnv who (VEnv.eraseEnv w.1.env))

set_option linter.flexible false in
theorem movePureAtProgramCursor_availableAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P) {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p)
    (env : VEnv L Γ) :
    movePureAtProgramCursor g hctx σ who suffix
        (projectViewEnv who (VEnv.eraseEnv env)) ∈
      CursorCheckedWorld.availableProgramMovesAt
        p env suffix who := by
  cases p with
  | ret payoffs =>
      simp [movePureAtProgramCursor, CursorCheckedWorld.availableProgramMovesAt, active]
  | letExpr x e k =>
      simp [movePureAtProgramCursor, CursorCheckedWorld.availableProgramMovesAt, active]
  | sample x D k =>
      simp [movePureAtProgramCursor, CursorCheckedWorld.availableProgramMovesAt, active]
  | reveal y owner x hx k =>
      simp [movePureAtProgramCursor, CursorCheckedWorld.availableProgramMovesAt, active]
  | commit x owner R k =>
      by_cases howner : owner = who
      · cases howner
        have hguard :
            evalGuard (Player := P) (L := L) R
              ((ProgramPureStrategy.headKernel (P := P) (L := L)
                ((suffix.pureProfile (fun i => (σ i).val)) who))
                (projectViewEnv who (VEnv.eraseEnv env)))
              (VEnv.eraseEnv env) = true := by
          exact headPureKernel_legal_atCursor
            g hctx σ suffix (VEnv.eraseEnv env)
        simp [movePureAtProgramCursor, CursorCheckedWorld.availableProgramMovesAt,
          CursorCheckedWorld.availableProgramActionsAt, active,
          Vegas.FOSGBridge.availableActions, ProgramAction.toAction]
        constructor
        · refine ⟨
            (ProgramPureStrategy.headKernel (P := P) (L := L)
              ((suffix.pureProfile (fun i => (σ i).val)) who))
              (projectViewEnv who (VEnv.eraseEnv env)),
            ⟨⟨ProgramSuffix.ty_commitCursor suffix, ?_⟩,
              hguard⟩⟩
          exact cast_heq _ _
        · refine ⟨x, who, _, R, k, ?_, rfl, ?_⟩
          · exact ⟨rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩
          · rfl
      · have hnot : who ≠ owner := fun h => howner h.symm
        simp [movePureAtProgramCursor, CursorCheckedWorld.availableProgramMovesAt,
          active, howner, hnot]

set_option linter.flexible false in
theorem movePureStrategyAtProgramCursor_availableAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p)
    (env : VEnv L Γ) :
    movePureStrategyAtProgramCursor g hctx who σ suffix
        (projectViewEnv who (VEnv.eraseEnv env)) ∈
      CursorCheckedWorld.availableProgramMovesAt
        p env suffix who := by
  cases p with
  | ret payoffs =>
      simp [movePureStrategyAtProgramCursor,
        CursorCheckedWorld.availableProgramMovesAt, active]
  | letExpr x e k =>
      simp [movePureStrategyAtProgramCursor,
        CursorCheckedWorld.availableProgramMovesAt, active]
  | sample x D k =>
      simp [movePureStrategyAtProgramCursor,
        CursorCheckedWorld.availableProgramMovesAt, active]
  | reveal y owner x hx k =>
      simp [movePureStrategyAtProgramCursor,
        CursorCheckedWorld.availableProgramMovesAt, active]
  | commit x owner R k =>
      by_cases howner : owner = who
      · cases howner
        have hguard :
            evalGuard (Player := P) (L := L) R
              ((ProgramPureStrategy.headKernel (P := P) (L := L)
                (suffix.pureStrategy who σ.val))
                (projectViewEnv who (VEnv.eraseEnv env)))
              (VEnv.eraseEnv env) = true := by
          exact headPureStrategyKernel_legal_atCursor
            g hctx σ suffix (VEnv.eraseEnv env)
        simp [movePureStrategyAtProgramCursor,
          CursorCheckedWorld.availableProgramMovesAt,
          CursorCheckedWorld.availableProgramActionsAt, active,
          Vegas.FOSGBridge.availableActions, ProgramAction.toAction]
        constructor
        · refine ⟨
            (ProgramPureStrategy.headKernel (P := P) (L := L)
              (suffix.pureStrategy who σ.val))
              (projectViewEnv who (VEnv.eraseEnv env)),
            ⟨⟨ProgramSuffix.ty_commitCursor suffix, ?_⟩,
              hguard⟩⟩
          exact cast_heq _ _
        · refine ⟨x, who, _, R, k, ?_, rfl, ?_⟩
          · exact ⟨rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩
          · rfl
      · have hnot : who ≠ owner := fun h => howner h.symm
        simp [movePureStrategyAtProgramCursor,
          CursorCheckedWorld.availableProgramMovesAt,
          active, howner, hnot]

theorem movePureAtCursorWorld_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P) (w : CursorCheckedWorld g) :
    movePureAtCursorWorld g hctx σ who w ∈
      (observedProgramFOSG g hctx).availableMovesAtState w who := by
  have hlocal :=
    movePureAtProgramCursor_availableAt
      g hctx σ who w.1.suffix w.1.env
  cases hmove : movePureAtCursorWorld g hctx σ who w with
  | none =>
      change movePureAtProgramCursor g hctx σ who w.1.suffix
          (projectViewEnv who (VEnv.eraseEnv w.1.env)) = none at hmove
      rw [hmove] at hlocal
      simpa [movePureAtCursorWorld, observedProgramFOSG,
        GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, CursorCheckedWorld.active,
        CursorCheckedWorld.availableProgramMovesAt, CursorCheckedWorld.toWorld,
        hmove] using hlocal
  | some ai =>
      change movePureAtProgramCursor g hctx σ who w.1.suffix
          (projectViewEnv who (VEnv.eraseEnv w.1.env)) = some ai at hmove
      rw [hmove] at hlocal
      simpa [movePureAtCursorWorld, observedProgramFOSG,
        GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, CursorCheckedWorld.active,
        CursorCheckedWorld.availableProgramActions,
        CursorCheckedWorld.availableProgramActionsAt,
        CursorCheckedWorld.availableProgramMovesAt, CursorCheckedWorld.availableActions,
        CursorCheckedWorld.toWorld, availableActions, hmove] using hlocal

theorem movePureStrategyAtCursorWorld_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (w : CursorCheckedWorld g) :
    movePureStrategyAtCursorWorld g hctx who σ w ∈
      (observedProgramFOSG g hctx).availableMovesAtState w who := by
  have hlocal :=
    movePureStrategyAtProgramCursor_availableAt
      g hctx who σ w.1.suffix w.1.env
  cases hmove : movePureStrategyAtCursorWorld g hctx who σ w with
  | none =>
      change movePureStrategyAtProgramCursor g hctx who σ w.1.suffix
          (projectViewEnv who (VEnv.eraseEnv w.1.env)) = none at hmove
      rw [hmove] at hlocal
      simpa [movePureStrategyAtCursorWorld, observedProgramFOSG,
        GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, CursorCheckedWorld.active,
        CursorCheckedWorld.availableProgramMovesAt, CursorCheckedWorld.toWorld,
        hmove] using hlocal
  | some ai =>
      change movePureStrategyAtProgramCursor g hctx who σ w.1.suffix
          (projectViewEnv who (VEnv.eraseEnv w.1.env)) = some ai at hmove
      rw [hmove] at hlocal
      simpa [movePureStrategyAtCursorWorld, observedProgramFOSG,
        GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, CursorCheckedWorld.active,
        CursorCheckedWorld.availableProgramActions,
        CursorCheckedWorld.availableProgramActionsAt,
        CursorCheckedWorld.availableProgramMovesAt, CursorCheckedWorld.availableActions,
        CursorCheckedWorld.toWorld, availableActions, hmove] using hlocal

theorem moveAtProgramCursor_toBehavioral_eq_pure
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P) {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p)
    (view : ViewEnv who Γ) :
    moveAtProgramCursor g hctx (LegalProgramPureProfile.toBehavioral σ) who suffix view =
      PMF.pure (movePureAtProgramCursor g hctx σ who suffix view) := by
  cases p with
  | ret payoffs =>
      simp [moveAtProgramCursor, movePureAtProgramCursor]
  | letExpr x e k =>
      simp [moveAtProgramCursor, movePureAtProgramCursor]
  | sample x D k =>
      simp [moveAtProgramCursor, movePureAtProgramCursor]
  | reveal y owner x hx k =>
      simp [moveAtProgramCursor, movePureAtProgramCursor]
  | commit x owner R k =>
      by_cases howner : owner = who
      · cases howner
        let raw : ProgramPureProfile g.prog :=
          fun i => (σ i).val
        have hprofile :
            suffix.behavioralProfile
                (fun i => ((LegalProgramPureProfile.toBehavioral (g := g) σ) i).val) =
              ProgramPureProfile.toBehavioral (P := P) (L := L)
                (.commit x who R k) (suffix.pureProfile raw) := by
          simpa [raw, LegalProgramPureProfile.toBehavioral] using
            ProgramSuffix.behavioralProfile_toBehavioral
              (s := suffix) raw
        simp [moveAtProgramCursor, movePureAtProgramCursor, hprofile,
          ProgramPureProfile.toBehavioral, ProgramBehavioralStrategy.headKernel,
          FDist.toPMF_pure, PMF.pure_map, raw]
      · simp [moveAtProgramCursor, movePureAtProgramCursor, howner]

theorem moveAtCursorWorld_toBehavioral_eq_pure
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P) (w : CursorCheckedWorld g) :
    moveAtCursorWorld g hctx (LegalProgramPureProfile.toBehavioral σ) who w =
      PMF.pure (movePureAtCursorWorld g hctx σ who w) := by
  exact moveAtProgramCursor_toBehavioral_eq_pure
    g hctx σ who w.1.suffix
      (projectViewEnv who (VEnv.eraseEnv w.1.env))

/-- Program-action observation lookup for the final `observedProgramFOSG`
target. -/
noncomputable def moveAtProgramObservation?
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (obs : PrivateObs g who × PublicObs g hctx) :
    PMF (Option (ProgramAction g.prog who)) := by
  let priv := obs.1
  exact moveAtProgramCursor g hctx σ who priv.cursor.toSuffix
    (VEnv.eraseEnv priv.env)

theorem moveAtProgramObservation?_of_cursorWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) (w : CursorCheckedWorld g) :
    moveAtProgramObservation? g hctx σ who
      (privateObsOfCursorWorld who w, publicObsOfCursorWorld w) =
      moveAtCursorWorld g hctx σ who w := by
  unfold moveAtProgramObservation? moveAtCursorWorld
  change moveAtProgramCursor g hctx σ who
      (privateObsOfCursorWorld who w).cursor.toSuffix
      (VEnv.eraseEnv (privateObsOfCursorWorld who w).env) =
    moveAtProgramCursor g hctx σ who w.1.suffix
      (projectViewEnv who (VEnv.eraseEnv w.1.env))
  rw [privateObsOfCursorWorld_eraseEnv]
  rfl

/-- Program-action pure observation lookup for the final `observedProgramFOSG`
target. -/
noncomputable def movePureAtProgramObservation?
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P)
    (obs : PrivateObs g who × PublicObs g hctx) :
    Option (ProgramAction g.prog who) := by
  let priv := obs.1
  exact movePureAtProgramCursor g hctx σ who priv.cursor.toSuffix
    (VEnv.eraseEnv priv.env)

noncomputable def movePureStrategyAtProgramObservation?
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (obs : PrivateObs g who × PublicObs g hctx) :
    Option (ProgramAction g.prog who) := by
  let priv := obs.1
  exact movePureStrategyAtProgramCursor g hctx who σ priv.cursor.toSuffix
    (VEnv.eraseEnv priv.env)

theorem movePureAtProgramObservation?_eq_strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P)
    (obs : PrivateObs g who × PublicObs g hctx) :
    movePureAtProgramObservation? g hctx σ who obs =
      movePureStrategyAtProgramObservation? g hctx who (σ who) obs := by
  unfold movePureAtProgramObservation? movePureStrategyAtProgramObservation?
  exact movePureAtProgramCursor_eq_strategy g hctx σ who _ _

theorem movePureAtProgramObservation?_of_cursorWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P) (w : CursorCheckedWorld g) :
    movePureAtProgramObservation? g hctx σ who
      (privateObsOfCursorWorld who w, publicObsOfCursorWorld w) =
      movePureAtCursorWorld g hctx σ who w := by
  unfold movePureAtProgramObservation? movePureAtCursorWorld
  change movePureAtProgramCursor g hctx σ who
      (privateObsOfCursorWorld who w).cursor.toSuffix
      (VEnv.eraseEnv (privateObsOfCursorWorld who w).env) =
    movePureAtProgramCursor g hctx σ who w.1.suffix
      (projectViewEnv who (VEnv.eraseEnv w.1.env))
  rw [privateObsOfCursorWorld_eraseEnv]
  rfl

theorem movePureStrategyAtProgramObservation?_of_cursorWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (w : CursorCheckedWorld g) :
    movePureStrategyAtProgramObservation? g hctx who σ
      (privateObsOfCursorWorld who w, publicObsOfCursorWorld w) =
      movePureStrategyAtCursorWorld g hctx who σ w := by
  unfold movePureStrategyAtProgramObservation? movePureStrategyAtCursorWorld
  change movePureStrategyAtProgramCursor g hctx who σ
      (privateObsOfCursorWorld who w).cursor.toSuffix
      (VEnv.eraseEnv (privateObsOfCursorWorld who w).env) =
    movePureStrategyAtProgramCursor g hctx who σ w.1.suffix
      (projectViewEnv who (VEnv.eraseEnv w.1.env))
  rw [privateObsOfCursorWorld_eraseEnv]
  rfl

/-- Raw pure profile induced by a Vegas legal pure profile for the final
program-action FOSG. Use `toObservedProgramLegalPureProfile` when the target
type requires FOSG legality. -/
noncomputable def programPureProfileCandidate
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    GameTheory.FOSG.PureProfile (observedProgramFOSG g hctx) :=
  fun who s =>
    match programLatestObservation? g hctx who s with
    | none => movePureAtCursorWorld g hctx σ who (CursorCheckedWorld.initial g hctx)
    | some obs => movePureAtProgramObservation? g hctx σ who obs

noncomputable def programPureStrategyCandidate
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who) :
    GameTheory.FOSG.PureStrategy (observedProgramFOSG g hctx) who :=
  fun s =>
    match programLatestObservation? g hctx who s with
    | none =>
        movePureStrategyAtProgramCursor g hctx who σ
          (ProgramSuffix.here (root := g.prog))
          (projectViewEnv who (VEnv.eraseEnv g.env))
    | some obs => movePureStrategyAtProgramObservation? g hctx who σ obs

theorem programPureProfileCandidate_eq_strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) (who : P) :
    programPureProfileCandidate g hctx σ who =
      programPureStrategyCandidate g hctx who (σ who) := by
  funext s
  unfold programPureProfileCandidate programPureStrategyCandidate
  split
  · simp [movePureAtCursorWorld, CursorCheckedWorld.initial,
      CursorWorldData.suffix, ProgramCursor.toSuffix,
      ProgramCursor.toSuffixFrom, movePureAtProgramCursor_eq_strategy]
    rfl
  · rw [movePureAtProgramObservation?_eq_strategy]

@[simp] theorem programPureStrategyCandidate_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who) :
    programPureStrategyCandidate g hctx who σ
      ((GameTheory.FOSG.History.nil (observedProgramFOSG g hctx)).playerView who) =
      movePureStrategyAtCursorWorld g hctx who σ
        (CursorCheckedWorld.initial g hctx) := by
  simp [programPureStrategyCandidate, programLatestObservation?,
    programObservationEvents, last?, movePureStrategyAtCursorWorld,
    CursorCheckedWorld.initial, CursorWorldData.suffix, ProgramCursor.toSuffix,
    ProgramCursor.toSuffixFrom]
  rfl

@[simp] theorem programPureStrategyCandidate_snoc
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (h : (observedProgramFOSG g hctx).History)
    (a : (observedProgramFOSG g hctx).LegalAction h.lastState)
    (dst : CursorCheckedWorld g)
    (support : (observedProgramFOSG g hctx).transition h.lastState a dst ≠ 0) :
    programPureStrategyCandidate g hctx who σ
      ((h.snoc a dst support).playerView who) =
      movePureStrategyAtCursorWorld g hctx who σ dst := by
  rw [programPureStrategyCandidate,
    programLatestObservation?_history_snoc g hctx who h a dst support]
  simp [movePureStrategyAtProgramObservation?_of_cursorWorld]

@[simp] theorem programPureStrategyCandidate_appendStep
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (h : (observedProgramFOSG g hctx).History)
    (e : (observedProgramFOSG g hctx).Step)
    (hsrc : e.src = h.lastState) :
    programPureStrategyCandidate g hctx who σ
      ((h.appendStep e hsrc).playerView who) =
      movePureStrategyAtCursorWorld g hctx who σ
        (h.appendStep e hsrc).lastState := by
  cases e with
  | mk src act dst support =>
      cases hsrc
      change
        programPureStrategyCandidate g hctx who σ
          ((h.snoc act dst support).playerView who) =
        movePureStrategyAtCursorWorld g hctx who σ
          (h.snoc act dst support).lastState
      simpa using
        programPureStrategyCandidate_snoc
          g hctx who σ h act dst support

theorem programPureStrategyCandidate_history
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (h : (observedProgramFOSG g hctx).History) :
    programPureStrategyCandidate g hctx who σ (h.playerView who) =
      movePureStrategyAtCursorWorld g hctx who σ h.lastState := by
  let G := observedProgramFOSG g hctx
  cases h with
  | mk steps chain =>
      induction steps using List.reverseRecOn with
      | nil =>
          simp [programPureStrategyCandidate,
            GameTheory.FOSG.History.playerView,
            GameTheory.FOSG.History.playerViewFrom,
            GameTheory.FOSG.History.lastState,
            GameTheory.FOSG.lastStateFrom,
            programLatestObservation?, programObservationEvents, last?,
            observedProgramFOSG, movePureStrategyAtCursorWorld,
            CursorCheckedWorld.initial, CursorWorldData.suffix,
            ProgramCursor.toSuffix, ProgramCursor.toSuffixFrom]
          rfl
      | append_singleton steps e ih =>
          let hprefix : G.History :=
            { steps := steps
              chain := GameTheory.FOSG.StepChainFrom.left
                (G := G) (es₁ := steps) (es₂ := [e]) chain }
          have hright :
              G.StepChainFrom (G.lastStateFrom G.init steps) [e] :=
            GameTheory.FOSG.StepChainFrom.right
              (G := G) (es₁ := steps) (es₂ := [e]) chain
          have hsrc : e.src = hprefix.lastState := by
            simpa [hprefix, GameTheory.FOSG.History.lastState,
              GameTheory.FOSG.StepChainFrom] using hright.1
          let hfull : G.History := hprefix.appendStep e hsrc
          have hEq : ({ steps := steps ++ [e], chain := chain } : G.History) = hfull := by
            ext
            rfl
          rw [hEq]
          exact programPureStrategyCandidate_appendStep
            g hctx who σ hprefix e hsrc

theorem programPureStrategyCandidate_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (h : (observedProgramFOSG g hctx).History) :
    programPureStrategyCandidate g hctx who σ (h.playerView who) ∈
      (observedProgramFOSG g hctx).availableMoves h who := by
  rw [programPureStrategyCandidate_history g hctx who σ h]
  simpa [GameTheory.FOSG.availableMoves,
    GameTheory.FOSG.availableMovesAtState] using
    movePureStrategyAtCursorWorld_available g hctx who σ h.lastState

@[simp] theorem programPureProfileCandidate_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) (who : P) :
    programPureProfileCandidate g hctx σ who
      ((GameTheory.FOSG.History.nil (observedProgramFOSG g hctx)).playerView who) =
      movePureAtCursorWorld g hctx σ who (CursorCheckedWorld.initial g hctx) := by
  simp [programPureProfileCandidate, programLatestObservation?,
    programObservationEvents, last?]

@[simp] theorem programPureProfileCandidate_snoc
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (a : (observedProgramFOSG g hctx).LegalAction h.lastState)
    (dst : CursorCheckedWorld g)
    (support : (observedProgramFOSG g hctx).transition h.lastState a dst ≠ 0) :
    programPureProfileCandidate g hctx σ who
      ((h.snoc a dst support).playerView who) =
      movePureAtCursorWorld g hctx σ who dst := by
  rw [programPureProfileCandidate,
    programLatestObservation?_history_snoc g hctx who h a dst support]
  simp [movePureAtProgramObservation?_of_cursorWorld]

@[simp] theorem programPureProfileCandidate_appendStep
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (e : (observedProgramFOSG g hctx).Step)
    (hsrc : e.src = h.lastState) :
    programPureProfileCandidate g hctx σ who
      ((h.appendStep e hsrc).playerView who) =
      movePureAtCursorWorld g hctx σ who (h.appendStep e hsrc).lastState := by
  cases e with
  | mk src act dst support =>
      cases hsrc
      change
        programPureProfileCandidate g hctx σ who
          ((h.snoc act dst support).playerView who) =
        movePureAtCursorWorld g hctx σ who (h.snoc act dst support).lastState
      simpa using
        programPureProfileCandidate_snoc
          g hctx σ who h act dst support

theorem programPureProfileCandidate_history
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History) :
    programPureProfileCandidate g hctx σ who (h.playerView who) =
      movePureAtCursorWorld g hctx σ who h.lastState := by
  let G := observedProgramFOSG g hctx
  cases h with
  | mk steps chain =>
      induction steps using List.reverseRecOn with
      | nil =>
          simp [programPureProfileCandidate,
            GameTheory.FOSG.History.playerView,
            GameTheory.FOSG.History.playerViewFrom,
            GameTheory.FOSG.History.lastState,
            GameTheory.FOSG.lastStateFrom,
            programLatestObservation?, programObservationEvents, last?,
            observedProgramFOSG]
      | append_singleton steps e ih =>
          let hprefix : G.History :=
            { steps := steps
              chain := GameTheory.FOSG.StepChainFrom.left
                (G := G) (es₁ := steps) (es₂ := [e]) chain }
          have hright :
              G.StepChainFrom (G.lastStateFrom G.init steps) [e] :=
            GameTheory.FOSG.StepChainFrom.right
              (G := G) (es₁ := steps) (es₂ := [e]) chain
          have hsrc : e.src = hprefix.lastState := by
            simpa [hprefix, GameTheory.FOSG.History.lastState,
              GameTheory.FOSG.StepChainFrom] using hright.1
          let hfull : G.History := hprefix.appendStep e hsrc
          have hEq : ({ steps := steps ++ [e], chain := chain } : G.History) = hfull := by
            ext
            rfl
          rw [hEq]
          exact programPureProfileCandidate_appendStep
            g hctx σ who hprefix e hsrc

theorem programPureProfileCandidate_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History) :
    programPureProfileCandidate g hctx σ who (h.playerView who) ∈
      (observedProgramFOSG g hctx).availableMoves h who := by
  rw [programPureProfileCandidate_history g hctx σ who h]
  simpa [GameTheory.FOSG.availableMoves,
    GameTheory.FOSG.availableMovesAtState] using
    movePureAtCursorWorld_available g hctx σ who h.lastState

/-- Transport a Vegas guard-legal pure profile to a legal pure profile of the
finite observed-program FOSG. -/
noncomputable def toObservedProgramLegalPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    (observedProgramFOSG g hctx).LegalPureProfile :=
  fun who =>
    ⟨programPureProfileCandidate g hctx σ who, by
      intro h
      exact programPureProfileCandidate_available g hctx σ who h⟩

@[simp] theorem toObservedProgramLegalPureProfile_apply
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) (who : P) :
    ((toObservedProgramLegalPureProfile g hctx σ who).1) =
      programPureProfileCandidate g hctx σ who := rfl

/-- Transport a Vegas guard-legal pure profile to the reachable-information
strategy space of the observed-program FOSG. This is the finite strategy space
used by the reachable-coordinate FOSG Kuhn theorem. -/
noncomputable def toObservedProgramReachableLegalPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    (observedProgramFOSG g hctx).ReachableLegalPureProfile :=
  fun who =>
    (toObservedProgramLegalPureProfile g hctx σ who).restrictReachable

noncomputable def toObservedProgramReachableLegalPureStrategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who) :
    (observedProgramFOSG g hctx).ReachableLegalPureStrategy who := by
  refine ⟨(programPureStrategyCandidate g hctx who σ).restrictReachable, ?_⟩
  intro h
  simpa [GameTheory.FOSG.PureStrategy.restrictReachable] using
    programPureStrategyCandidate_available g hctx who σ h

noncomputable def toObservedProgramReachableMixedPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    GameTheory.FOSG.Kuhn.ReachableMixedProfile
      (G := observedProgramFOSG g hctx) :=
  fun who =>
    PMF.map (toObservedProgramReachableLegalPureStrategy g hctx who) (μ who)

theorem toObservedProgramReachableLegalPureProfile_eq_component
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    toObservedProgramReachableLegalPureProfile g hctx σ =
      fun who => toObservedProgramReachableLegalPureStrategy g hctx who (σ who) := by
  funext who
  apply Subtype.ext
  funext s
  change
    (programPureProfileCandidate g hctx σ who).restrictReachable s =
      (programPureStrategyCandidate g hctx who (σ who)).restrictReachable s
  rw [programPureProfileCandidate_eq_strategy]

theorem toObservedProgramReachableMixedPureProfile_joint
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who, Fintype (LegalProgramPureStrategy g who)]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    [Fintype (observedProgramFOSG g hctx).History]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    GameTheory.FOSG.Kuhn.reachableMixedProfileJoint
        (G := observedProgramFOSG g hctx)
        (toObservedProgramReachableMixedPureProfile g hctx μ) =
      PMF.map (toObservedProgramReachableLegalPureProfile g hctx)
        (Math.PMFProduct.pmfPi μ) := by
  classical
  change Math.PMFProduct.pmfPi
      (fun who =>
        PMF.map (toObservedProgramReachableLegalPureStrategy g hctx who)
          (μ who)) =
    PMF.map
      (fun σ => toObservedProgramReachableLegalPureProfile g hctx σ)
      (Math.PMFProduct.pmfPi μ)
  have hmap :
      (fun σ => toObservedProgramReachableLegalPureProfile g hctx σ) =
        (fun σ => fun who =>
          toObservedProgramReachableLegalPureStrategy g hctx who (σ who)) := by
    funext σ
    exact toObservedProgramReachableLegalPureProfile_eq_component g hctx σ
  rw [hmap]
  exact (Math.PMFProduct.pmfPi_push_coordwise μ
    (fun who => toObservedProgramReachableLegalPureStrategy g hctx who)).symm

@[simp] theorem toObservedProgramReachableLegalPureProfile_apply
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) (who : P) :
    ((toObservedProgramReachableLegalPureProfile g hctx σ who).1) =
      (programPureProfileCandidate g hctx σ who).restrictReachable := rfl

theorem moveAtProgramObservation?_toBehavioral_eq_pure
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P)
    (obs : PrivateObs g who × PublicObs g hctx) :
    moveAtProgramObservation? g hctx (LegalProgramPureProfile.toBehavioral σ) who obs =
      PMF.pure (movePureAtProgramObservation? g hctx σ who obs) := by
  unfold moveAtProgramObservation? movePureAtProgramObservation?
  simp [moveAtProgramCursor_toBehavioral_eq_pure]

/-- Raw behavioral profile induced by a Vegas legal behavioral profile for the
final program-action FOSG. The `Candidate` suffix means this is the unbundled
profile function; use `toObservedProgramLegalBehavioralProfile` when the target
type requires a legal FOSG profile. -/
noncomputable def programBehavioralProfileCandidate
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    GameTheory.FOSG.BehavioralProfile (observedProgramFOSG g hctx) :=
  fun who s =>
    match programLatestObservation? g hctx who s with
    | none => moveAtCursorWorld g hctx σ who (CursorCheckedWorld.initial g hctx)
    | some obs => moveAtProgramObservation? g hctx σ who obs

@[simp] theorem programBehavioralProfileCandidate_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    programBehavioralProfileCandidate g hctx σ who
      ((GameTheory.FOSG.History.nil (observedProgramFOSG g hctx)).playerView who) =
      moveAtCursorWorld g hctx σ who (CursorCheckedWorld.initial g hctx) := by
  simp [programBehavioralProfileCandidate, programLatestObservation?,
    programObservationEvents, last?]

@[simp] theorem programBehavioralProfileCandidate_snoc
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (a : (observedProgramFOSG g hctx).LegalAction h.lastState)
    (dst : CursorCheckedWorld g)
    (support : (observedProgramFOSG g hctx).transition h.lastState a dst ≠ 0) :
    programBehavioralProfileCandidate g hctx σ who
      ((h.snoc a dst support).playerView who) =
      moveAtCursorWorld g hctx σ who dst := by
  rw [programBehavioralProfileCandidate,
    programLatestObservation?_history_snoc g hctx who h a dst support]
  simp [moveAtProgramObservation?_of_cursorWorld]

@[simp] theorem programBehavioralProfileCandidate_appendStep
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (e : (observedProgramFOSG g hctx).Step)
    (hsrc : e.src = h.lastState) :
    programBehavioralProfileCandidate g hctx σ who
      ((h.appendStep e hsrc).playerView who) =
      moveAtCursorWorld g hctx σ who (h.appendStep e hsrc).lastState := by
  cases e with
  | mk src act dst support =>
      cases hsrc
      change
        programBehavioralProfileCandidate g hctx σ who
          ((h.snoc act dst support).playerView who) =
        moveAtCursorWorld g hctx σ who (h.snoc act dst support).lastState
      simpa using
        programBehavioralProfileCandidate_snoc
          g hctx σ who h act dst support

/-- At every realized history of the observed-program FOSG, the transported
profile reads exactly the Vegas strategy at the current cursor world. -/
theorem programBehavioralProfileCandidate_history
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History) :
    programBehavioralProfileCandidate g hctx σ who (h.playerView who) =
      moveAtCursorWorld g hctx σ who h.lastState := by
  let G := observedProgramFOSG g hctx
  cases h with
  | mk steps chain =>
      induction steps using List.reverseRecOn with
      | nil =>
          simp [programBehavioralProfileCandidate,
            GameTheory.FOSG.History.playerView,
            GameTheory.FOSG.History.playerViewFrom,
            GameTheory.FOSG.History.lastState,
            GameTheory.FOSG.lastStateFrom,
            programLatestObservation?, programObservationEvents, last?,
            observedProgramFOSG]
      | append_singleton steps e ih =>
          let hprefix : G.History :=
            { steps := steps
              chain := GameTheory.FOSG.StepChainFrom.left
                (G := G) (es₁ := steps) (es₂ := [e]) chain }
          have hright :
              G.StepChainFrom (G.lastStateFrom G.init steps) [e] :=
            GameTheory.FOSG.StepChainFrom.right
              (G := G) (es₁ := steps) (es₂ := [e]) chain
          have hsrc : e.src = hprefix.lastState := by
            simpa [hprefix, GameTheory.FOSG.History.lastState,
              GameTheory.FOSG.StepChainFrom] using hright.1
          let hfull : G.History := hprefix.appendStep e hsrc
          have hEq : ({ steps := steps ++ [e], chain := chain } : G.History) = hfull := by
            ext
            rfl
          rw [hEq]
          exact programBehavioralProfileCandidate_appendStep
            g hctx σ who hprefix e hsrc

theorem programBehavioralProfileCandidate_support_available_snoc
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (a : (observedProgramFOSG g hctx).LegalAction h.lastState)
    (dst : CursorCheckedWorld g)
    (support : (observedProgramFOSG g hctx).transition h.lastState a dst ≠ 0)
    {oi : Option (ProgramAction g.prog who)}
    (hoi : oi ∈
      (programBehavioralProfileCandidate g hctx σ who
        ((h.snoc a dst support).playerView who)).support) :
    oi ∈ (observedProgramFOSG g hctx).availableMoves
      (h.snoc a dst support) who := by
  rw [programBehavioralProfileCandidate,
    programLatestObservation?_history_snoc g hctx who h a dst support] at hoi
  simp only at hoi
  rw [moveAtProgramObservation?_of_cursorWorld] at hoi
  simpa [GameTheory.FOSG.availableMoves,
    GameTheory.FOSG.availableMovesAtState] using
    moveAtCursorWorld_support_available g hctx σ who dst hoi

theorem programBehavioralProfileCandidate_support_available_appendStep
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (e : (observedProgramFOSG g hctx).Step)
    (hsrc : e.src = h.lastState)
    {oi : Option (ProgramAction g.prog who)}
    (hoi : oi ∈
      (programBehavioralProfileCandidate g hctx σ who
        ((h.appendStep e hsrc).playerView who)).support) :
    oi ∈ (observedProgramFOSG g hctx).availableMoves
      (h.appendStep e hsrc) who := by
  cases e with
  | mk src act dst support =>
      cases hsrc
      simpa [GameTheory.FOSG.History.appendStep_eq_snoc] using
        programBehavioralProfileCandidate_support_available_snoc
          g hctx σ who h act dst support hoi

theorem programBehavioralProfileCandidate_support_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History)
    {oi : Option (ProgramAction g.prog who)}
    (hoi : oi ∈
      (programBehavioralProfileCandidate g hctx σ who (h.playerView who)).support) :
    oi ∈ (observedProgramFOSG g hctx).availableMoves h who := by
  let G := observedProgramFOSG g hctx
  cases h with
  | mk steps chain =>
      induction steps using List.reverseRecOn with
      | nil =>
          have hoi' : oi ∈
              (moveAtCursorWorld g hctx σ who
                (CursorCheckedWorld.initial g hctx)).support := by
            simpa [G, programBehavioralProfileCandidate,
              GameTheory.FOSG.History.playerView,
              GameTheory.FOSG.History.playerViewFrom,
              programLatestObservation?, programObservationEvents, last?] using hoi
          simpa [G, GameTheory.FOSG.availableMoves,
            GameTheory.FOSG.availableMovesAtState,
            GameTheory.FOSG.History.lastState,
            GameTheory.FOSG.lastStateFrom] using
            moveAtCursorWorld_support_available
              g hctx σ who (CursorCheckedWorld.initial g hctx) hoi'
      | append_singleton steps e ih =>
          let hprefix : G.History :=
            { steps := steps
              chain := GameTheory.FOSG.StepChainFrom.left
                (G := G) (es₁ := steps) (es₂ := [e]) chain }
          have hright :
              G.StepChainFrom (G.lastStateFrom G.init steps) [e] :=
            GameTheory.FOSG.StepChainFrom.right
              (G := G) (es₁ := steps) (es₂ := [e]) chain
          have hsrc : e.src = hprefix.lastState := by
            simpa [hprefix, GameTheory.FOSG.History.lastState,
              GameTheory.FOSG.StepChainFrom] using hright.1
          let hfull : G.History := hprefix.appendStep e hsrc
          have hEq : ({ steps := steps ++ [e], chain := chain } : G.History) = hfull := by
            ext
            rfl
          rw [hEq] at hoi ⊢
          exact programBehavioralProfileCandidate_support_available_appendStep
            g hctx σ who hprefix e hsrc hoi

/-- Transport a Vegas guard-legal behavioral profile to a legal behavioral
profile of the finite observed-program FOSG. -/
noncomputable def toObservedProgramLegalBehavioralProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    (observedProgramFOSG g hctx).LegalBehavioralProfile :=
  fun who =>
    ⟨programBehavioralProfileCandidate g hctx σ who, by
      intro h oi hoi
      exact programBehavioralProfileCandidate_support_available g hctx σ who h hoi⟩

@[simp] theorem toObservedProgramLegalBehavioralProfile_apply
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    ((toObservedProgramLegalBehavioralProfile g hctx σ who).1) =
      programBehavioralProfileCandidate g hctx σ who := rfl

/-- Transport a Vegas guard-legal behavioral profile to the reachable-information
strategy space of the observed-program FOSG. -/
noncomputable def toObservedProgramReachableLegalBehavioralProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    (observedProgramFOSG g hctx).ReachableLegalBehavioralProfile :=
  fun who =>
    (toObservedProgramLegalBehavioralProfile g hctx σ who).restrictReachable

@[simp] theorem toObservedProgramReachableLegalBehavioralProfile_apply
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    ((toObservedProgramReachableLegalBehavioralProfile g hctx σ who).1) =
      (programBehavioralProfileCandidate g hctx σ who).restrictReachable := rfl

@[simp] theorem toObservedProgramReachableLegalBehavioralProfile_extend_apply_history
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (h : (observedProgramFOSG g hctx).History) (who : P) :
    ((toObservedProgramReachableLegalBehavioralProfile g hctx σ).extend.toProfile
        who (h.playerView who)) =
      (toObservedProgramLegalBehavioralProfile g hctx σ).toProfile
        who (h.playerView who) := by
  simp [GameTheory.FOSG.ReachableLegalBehavioralProfile.extend,
    GameTheory.FOSG.ReachableBehavioralStrategy.extend,
    GameTheory.FOSG.BehavioralStrategy.restrictReachable]

theorem observedProgramRunDist_reachable_extend_eq
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    observedProgramRunDist g hctx LF
        (toObservedProgramReachableLegalBehavioralProfile g hctx σ).extend =
      observedProgramRunDist g hctx LF
        (toObservedProgramLegalBehavioralProfile g hctx σ) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  unfold observedProgramRunDist
  exact GameTheory.FOSG.runDist_congr
    (G := observedProgramFOSG g hctx)
    (syntaxSteps g.prog)
    (toObservedProgramReachableLegalBehavioralProfile g hctx σ).extend
    (toObservedProgramLegalBehavioralProfile g hctx σ)
    (by
      intro h who
      exact toObservedProgramReachableLegalBehavioralProfile_extend_apply_history
        g hctx σ h who)

theorem observedProgramProjectedPayoff_terminalWeight_reachable_eq_runDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P,
        Fintype (Option (ProgramAction g.prog who)) :=
      fun who =>
        observedProgramFOSG.instFintypeOptionAction
          g hctx LF who
    letI : Fintype (observedProgramFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory g hctx LF
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    ∑ h : (observedProgramFOSG g hctx).History,
      (GameTheory.FOSG.History.terminalWeight
          (G := observedProgramFOSG g hctx)
          (toObservedProgramReachableLegalBehavioralProfile
            g hctx σ).toProfile.extend
          h).toReal *
        (observedProgramHistoryOutcome g hctx h who : ℝ) =
      ∑ h : (observedProgramFOSG g hctx).History,
        (observedProgramRunDist g hctx LF
          (toObservedProgramLegalBehavioralProfile g hctx σ) h).toReal *
          (observedProgramHistoryOutcome g hctx h who : ℝ) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  calc
    ∑ h : (observedProgramFOSG g hctx).History,
      (GameTheory.FOSG.History.terminalWeight
          (G := observedProgramFOSG g hctx)
          (toObservedProgramReachableLegalBehavioralProfile
            g hctx σ).toProfile.extend
          h).toReal *
        (observedProgramHistoryOutcome g hctx h who : ℝ)
      = ∑ h : (observedProgramFOSG g hctx).History,
          (observedProgramRunDist g hctx LF
            (toObservedProgramReachableLegalBehavioralProfile g hctx σ).extend h).toReal *
            (observedProgramHistoryOutcome g hctx h who : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro h _
          have hrun :
              observedProgramRunDist g hctx LF
                  (toObservedProgramReachableLegalBehavioralProfile
                    g hctx σ).extend h =
                GameTheory.FOSG.History.terminalWeight
                  (G := observedProgramFOSG g hctx)
                  (toObservedProgramReachableLegalBehavioralProfile
                    g hctx σ).toProfile.extend h := by
            simpa [observedProgramRunDist,
              GameTheory.FOSG.ReachableLegalBehavioralProfile.extend] using
              GameTheory.FOSG.runDist_eq_terminalWeight_of_boundedHorizon
                (G := observedProgramFOSG g hctx)
                (observedProgramFOSG_boundedHorizon g hctx)
                (toObservedProgramReachableLegalBehavioralProfile g hctx σ).extend h
          rw [← hrun]
    _ = ∑ h : (observedProgramFOSG g hctx).History,
        (observedProgramRunDist g hctx LF
          (toObservedProgramLegalBehavioralProfile g hctx σ) h).toReal *
          (observedProgramHistoryOutcome g hctx h who : ℝ) := by
          rw [observedProgramRunDist_reachable_extend_eq
            g hctx LF σ]

/-- Reachable-coordinate FOSG Kuhn theorem specialized to the observed-program
terminal-history game.

This is still a theorem about the native FOSG terminal-history game. The
separate outcome-preservation theorem below identifies the projected Vegas
outcome kernel with `toKernelGame g`. -/
theorem observedProgramTerminalHistory_behavioral_to_mixed_eu_reachable
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P,
        Fintype (ProgramAction g.prog who) :=
      fun who =>
        ProgramAction.instFintype LF g.prog who
    letI : ∀ who : P,
        Fintype (Option (ProgramAction g.prog who)) :=
      fun who =>
        observedProgramFOSG.instFintypeOptionAction
          g hctx LF who
    letI : Fintype (observedProgramFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory g hctx LF
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    ∑ π,
      (GameTheory.FOSG.Kuhn.reachableBehavioralToMixedJoint
          (G := observedProgramFOSG g hctx)
          (toObservedProgramReachableLegalBehavioralProfile
            g hctx σ).toProfile π).toReal *
        (∑ h : (observedProgramFOSG g hctx).History,
          (GameTheory.FOSG.History.terminalWeight
              (G := observedProgramFOSG g hctx)
              ((observedProgramFOSG g hctx).pureToBehavioral π.extend)
              h).toReal *
            GameTheory.FOSG.History.utility h who) =
      (observedProgramTerminalHistoryGame
          g hctx LF).eu
        (toObservedProgramReachableLegalBehavioralProfile
          g hctx σ).extend
        who := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (ProgramAction g.prog who) :=
    fun who =>
      ProgramAction.instFintype LF g.prog who
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  exact GameTheory.FOSG.Kuhn.behavioral_to_mixed_eu_reachable
    (G := observedProgramFOSG g hctx)
    (observedProgramFOSG.hasNormalizedTerminalLaw g hctx LF)
    (toObservedProgramReachableLegalBehavioralProfile
      g hctx σ)
    who

/-- Reachable-coordinate FOSG Kuhn theorem specialized to Vegas' projected
payoff on terminal histories.

Unlike `observedProgramTerminalHistory_behavioral_to_mixed_eu_reachable`, this
statement uses the Vegas outcome projection as the payoff function, not the
native FOSG cumulative reward. This is the payoff expression needed for the
Vegas-facing Kuhn bridge. -/
theorem observedProgramProjectedPayoff_behavioral_to_mixed_reachable
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P,
        Fintype (ProgramAction g.prog who) :=
      fun who =>
        ProgramAction.instFintype LF g.prog who
    letI : ∀ who : P,
        Fintype (Option (ProgramAction g.prog who)) :=
      fun who =>
        observedProgramFOSG.instFintypeOptionAction
          g hctx LF who
    letI : Fintype (observedProgramFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory g hctx LF
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    ∑ π,
      (GameTheory.FOSG.Kuhn.reachableBehavioralToMixedJoint
          (G := observedProgramFOSG g hctx)
          (toObservedProgramReachableLegalBehavioralProfile
            g hctx σ).toProfile π).toReal *
        (∑ h : (observedProgramFOSG g hctx).History,
          (GameTheory.FOSG.History.terminalWeight
              (G := observedProgramFOSG g hctx)
              ((observedProgramFOSG g hctx).pureToBehavioral π.extend)
              h).toReal *
            (observedProgramHistoryOutcome g hctx h who : ℝ)) =
      ∑ h : (observedProgramFOSG g hctx).History,
        (GameTheory.FOSG.History.terminalWeight
            (G := observedProgramFOSG g hctx)
            (toObservedProgramReachableLegalBehavioralProfile
              g hctx σ).toProfile.extend
            h).toReal *
          (observedProgramHistoryOutcome g hctx h who : ℝ) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (ProgramAction g.prog who) :=
    fun who =>
      ProgramAction.instFintype LF g.prog who
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  exact GameTheory.FOSG.Kuhn.reachable_marginal_terminalExpectation
    (G := observedProgramFOSG g hctx)
    (toObservedProgramReachableLegalBehavioralProfile
      g hctx σ).toProfile
    (fun h =>
      (observedProgramHistoryOutcome g hctx h who : ℝ))

theorem programBehavioralProfileCandidate_toBehavioral_eq_pure
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who) :
    programBehavioralProfileCandidate g hctx
        (LegalProgramPureProfile.toBehavioral σ) who s =
      PMF.pure (programPureProfileCandidate g hctx σ who s) := by
  unfold programBehavioralProfileCandidate programPureProfileCandidate
  cases hobs : programLatestObservation? g hctx who s with
  | none =>
      simpa [hobs] using
        moveAtCursorWorld_toBehavioral_eq_pure
          g hctx σ who (CursorCheckedWorld.initial g hctx)
  | some obs =>
      simpa [hobs] using
        moveAtProgramObservation?_toBehavioral_eq_pure
          g hctx σ who obs

theorem toObservedProgramLegalBehavioralProfile_toBehavioral
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    toObservedProgramLegalBehavioralProfile g hctx
        (LegalProgramPureProfile.toBehavioral σ) =
      (observedProgramFOSG g hctx).legalPureToBehavioral
        (toObservedProgramLegalPureProfile g hctx σ) := by
  funext who
  apply Subtype.ext
  funext s
  simp [GameTheory.FOSG.legalPureToBehavioral,
    GameTheory.FOSG.pureToBehavioral,
    programBehavioralProfileCandidate_toBehavioral_eq_pure]

/-- The FOSG legal-action law induced by a transported Vegas profile has the
same marginal over any player's optional move as the Vegas strategy currently
visible at the history endpoint. This is the product-law collapse needed for
the `commit` case of outcome preservation. -/
theorem observedProgramLegalActionLaw_bind_coord
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    (σ : LegalProgramBehavioralProfile g)
    (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState)
    (who : P) {β : Type}
    (f : Option (ProgramAction g.prog who) → PMF β) :
    ((observedProgramFOSG g hctx).legalActionLaw
        (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm).bind
        (fun a => f (a.1 who)) =
      (moveAtCursorWorld g hctx σ who h.lastState).bind f := by
  rw [GameTheory.FOSG.legalActionLaw_bind_coord
    (G := observedProgramFOSG g hctx)
    (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm who f]
  simp [GameTheory.FOSG.LegalBehavioralProfile.toProfile,
    toObservedProgramLegalBehavioralProfile_apply,
    programBehavioralProfileCandidate_history]

end Observed

end FOSGBridge
end Vegas
