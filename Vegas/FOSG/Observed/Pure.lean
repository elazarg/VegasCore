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
          let σp : ProgramPureStrategy who
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
          ((ProgramPureStrategy.headKernel
            ((suffix.pureProfile (fun i => (σ i).val)) who)) view)) := by
  simp [movePureAtProgramCursor]

@[simp] theorem movePureStrategyAtProgramCursor_commit_owner
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {who : P} (σ : LegalProgramPureStrategy g who)
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (view : ViewEnv who Γ) :
    movePureStrategyAtProgramCursor g hctx who σ suffix view =
      some
        (ProgramAction.commitAt suffix
          ((ProgramPureStrategy.headKernel
            (suffix.pureStrategy who σ.val)) view)) := by
  simp [movePureStrategyAtProgramCursor]

theorem headPureKernel_legal_atCursor
    (g : WFProgram P L) (_hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (ρ : Env L.Val (eraseVCtx Γ)) :
    evalGuard (Player := P) (L := L) R
      ((ProgramPureStrategy.headKernel
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
      ((ProgramPureStrategy.headKernel
        (suffix.pureStrategy who σ.val))
        (projectViewEnv who ρ)) ρ = true := by
  have hcursor :
      (suffix.pureStrategy who σ.val).IsLegal
        (.commit x who R k) :=
    suffix.pureStrategy_isLegal who σ.2
  let σc :
      PureKernel who Γ b ×
        ProgramPureStrategy who k := by
    simpa [ProgramPureStrategy] using suffix.pureStrategy who σ.val
  have hsite :
      σc.1.IsLegalAt (x := x) (who := who)
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
              ((ProgramPureStrategy.headKernel
                ((suffix.pureProfile (fun i => (σ i).val)) who))
                (projectViewEnv who (VEnv.eraseEnv env)))
              (VEnv.eraseEnv env) = true := by
          exact headPureKernel_legal_atCursor
            g hctx σ suffix (VEnv.eraseEnv env)
        rw [movePureAtProgramCursor_commit_owner]
        exact CursorCheckedWorld.availableProgramMovesAt_commit_owner_commitAt
          env suffix
          ((ProgramPureStrategy.headKernel
            ((suffix.pureProfile (fun i => (σ i).val)) who))
            (projectViewEnv who (VEnv.eraseEnv env)))
          hguard
      · have hnot : who ≠ owner := fun h => howner h.symm
        simp [movePureAtProgramCursor, CursorCheckedWorld.availableProgramMovesAt,
          active, howner, hnot]

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
              ((ProgramPureStrategy.headKernel
                (suffix.pureStrategy who σ.val))
                (projectViewEnv who (VEnv.eraseEnv env)))
              (VEnv.eraseEnv env) = true := by
          exact headPureStrategyKernel_legal_atCursor
            g hctx σ suffix (VEnv.eraseEnv env)
        rw [movePureStrategyAtProgramCursor_commit_owner]
        exact CursorCheckedWorld.availableProgramMovesAt_commit_owner_commitAt
          env suffix
          ((ProgramPureStrategy.headKernel
            (suffix.pureStrategy who σ.val))
            (projectViewEnv who (VEnv.eraseEnv env)))
          hguard
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

theorem moveAtProgramCursorPMF_toBehavioralPMF_eq_pure
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P) {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p)
    (view : ViewEnv who Γ) :
    moveAtProgramCursorPMF g hctx
        (LegalProgramPureProfile.toBehavioralPMF σ) who suffix view =
      PMF.pure (movePureAtProgramCursor g hctx σ who suffix view) := by
  cases p with
  | ret payoffs =>
      simp [moveAtProgramCursorPMF, movePureAtProgramCursor]
  | letExpr x e k =>
      simp [moveAtProgramCursorPMF, movePureAtProgramCursor]
  | sample x D k =>
      simp [moveAtProgramCursorPMF, movePureAtProgramCursor]
  | reveal y owner x hx k =>
      simp [moveAtProgramCursorPMF, movePureAtProgramCursor]
  | commit x owner R k =>
      by_cases howner : owner = who
      · cases howner
        let raw : ProgramPureProfile g.prog :=
          fun i => (σ i).val
        have hprofile :
            suffix.behavioralProfilePMF
                (fun i => ((LegalProgramPureProfile.toBehavioralPMF
                  (g := g) σ) i).val) =
              ProgramPureProfile.toBehavioralPMF
                (.commit x who R k) (suffix.pureProfile raw) := by
          simpa [raw, LegalProgramPureProfile.toBehavioralPMF] using
            ProgramSuffix.behavioralProfilePMF_toBehavioralPMF
              (s := suffix) raw
        simp [moveAtProgramCursorPMF, movePureAtProgramCursor, hprofile,
          ProgramPureProfile.toBehavioralPMF,
          ProgramBehavioralStrategyPMF.headKernel,
          PMF.pure_map, raw]
      · simp [moveAtProgramCursorPMF, movePureAtProgramCursor, howner]

theorem moveAtCursorWorldPMF_toBehavioralPMF_eq_pure
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P) (w : CursorCheckedWorld g) :
    moveAtCursorWorldPMF g hctx
        (LegalProgramPureProfile.toBehavioralPMF σ) who w =
      PMF.pure (movePureAtCursorWorld g hctx σ who w) := by
  exact moveAtProgramCursorPMF_toBehavioralPMF_eq_pure
    g hctx σ who w.1.suffix
      (projectViewEnv who (VEnv.eraseEnv w.1.env))

noncomputable def moveAtProgramObservationPMF?
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P)
    (obs : PrivateObs g who × PublicObs g hctx) :
    PMF (Option (ProgramAction g.prog who)) := by
  let priv := obs.1
  exact moveAtProgramCursorPMF g hctx σ who priv.cursor.toSuffix
    (priv.env)

theorem moveAtProgramObservationPMF?_of_cursorWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P) (w : CursorCheckedWorld g) :
    moveAtProgramObservationPMF? g hctx σ who
      (privateObsOfCursorWorld who w, publicObsOfCursorWorld w) =
      moveAtCursorWorldPMF g hctx σ who w := by
  unfold moveAtProgramObservationPMF? moveAtCursorWorldPMF
  change moveAtProgramCursorPMF g hctx σ who
      (privateObsOfCursorWorld who w).cursor.toSuffix
      ((privateObsOfCursorWorld who w).env) =
    moveAtProgramCursorPMF g hctx σ who w.1.suffix
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
    (priv.env)

noncomputable def movePureStrategyAtProgramObservation?
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (obs : PrivateObs g who × PublicObs g hctx) :
    Option (ProgramAction g.prog who) := by
  let priv := obs.1
  exact movePureStrategyAtProgramCursor g hctx who σ priv.cursor.toSuffix
    (priv.env)

theorem moveAtProgramObservationPMF?_toBehavioralPMF_eq_pure
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P)
    (obs : PrivateObs g who × PublicObs g hctx) :
    moveAtProgramObservationPMF? g hctx
        (LegalProgramPureProfile.toBehavioralPMF σ) who obs =
      PMF.pure (movePureAtProgramObservation? g hctx σ who obs) := by
  unfold moveAtProgramObservationPMF? movePureAtProgramObservation?
  exact moveAtProgramCursorPMF_toBehavioralPMF_eq_pure
    g hctx σ who obs.1.cursor.toSuffix obs.1.env

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
      ((privateObsOfCursorWorld who w).env) =
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
      ((privateObsOfCursorWorld who w).env) =
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
  GameTheory.FOSG.PureProfile.ofLatestObservation
    (G := observedProgramFOSG g hctx)
    (fun who =>
      movePureAtCursorWorld g hctx σ who (CursorCheckedWorld.initial g hctx))
    (fun who obs => movePureAtProgramObservation? g hctx σ who obs)

noncomputable def programPureStrategyCandidate
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who) :
    GameTheory.FOSG.PureStrategy (observedProgramFOSG g hctx) who :=
  GameTheory.FOSG.PureStrategy.ofLatestObservation
    (G := observedProgramFOSG g hctx)
    (i := who)
    (movePureStrategyAtProgramCursor g hctx who σ
      (ProgramSuffix.here (root := g.prog))
      (projectViewEnv who (VEnv.eraseEnv g.env)))
    (movePureStrategyAtProgramObservation? g hctx who σ)

theorem programPureProfileCandidate_eq_strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) (who : P) :
    programPureProfileCandidate g hctx σ who =
      programPureStrategyCandidate g hctx who (σ who) := by
  funext s
  unfold programPureProfileCandidate programPureStrategyCandidate
  cases hobs :
      GameTheory.FOSG.InfoState.latestObservation?
        (G := observedProgramFOSG g hctx) (i := who) s with
  | none =>
      simp [GameTheory.FOSG.PureProfile.ofLatestObservation,
        GameTheory.FOSG.PureStrategy.ofLatestObservation, hobs,
        movePureAtCursorWorld, CursorCheckedWorld.initial,
      CursorWorldData.suffix, ProgramCursor.toSuffix,
      ProgramCursor.toSuffixFrom, movePureAtProgramCursor_eq_strategy]
      rfl
  | some obs =>
      simp [GameTheory.FOSG.PureProfile.ofLatestObservation,
        GameTheory.FOSG.PureStrategy.ofLatestObservation, hobs,
        movePureAtProgramObservation?_eq_strategy]

@[simp] theorem programPureStrategyCandidate_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who) :
    programPureStrategyCandidate g hctx who σ
      ((GameTheory.FOSG.History.nil (observedProgramFOSG g hctx)).playerView who) =
      movePureStrategyAtCursorWorld g hctx who σ
        (CursorCheckedWorld.initial g hctx) := by
  simp [programPureStrategyCandidate,
    GameTheory.FOSG.PureStrategy.ofLatestObservation,
    movePureStrategyAtCursorWorld,
    CursorCheckedWorld.initial, CursorWorldData.suffix, ProgramCursor.toSuffix,
    ProgramCursor.toSuffixFrom]
  rfl

theorem programPureStrategyCandidate_history
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (h : (observedProgramFOSG g hctx).History) :
    programPureStrategyCandidate g hctx who σ (h.playerView who) =
      movePureStrategyAtCursorWorld g hctx who σ h.lastState := by
  by_cases hnil : h.steps = []
  · have hh :
        h = GameTheory.FOSG.History.nil (observedProgramFOSG g hctx) := by
      cases h with
      | mk steps chain =>
          cases hnil
          rfl
    rw [hh]
    simpa using programPureStrategyCandidate_nil g hctx who σ
  · have hlatest :
        GameTheory.FOSG.InfoState.latestObservation?
            (G := observedProgramFOSG g hctx) (i := who)
            (h.playerView who) =
          some (privateObsOfCursorWorld who h.lastState,
            publicObsOfCursorWorld h.lastState) := by
      simpa [programLatestObservation?] using
        programLatestObservation?_history_of_ne_nil g hctx who h hnil
    simp [programPureStrategyCandidate,
      GameTheory.FOSG.PureStrategy.ofLatestObservation, hlatest,
      movePureStrategyAtProgramObservation?_of_cursorWorld]

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
  simp [programPureProfileCandidate,
    GameTheory.FOSG.PureProfile.ofLatestObservation]

theorem programPureProfileCandidate_history
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History) :
    programPureProfileCandidate g hctx σ who (h.playerView who) =
      movePureAtCursorWorld g hctx σ who h.lastState := by
  by_cases hnil : h.steps = []
  · have hh :
        h = GameTheory.FOSG.History.nil (observedProgramFOSG g hctx) := by
      cases h with
      | mk steps chain =>
          cases hnil
          rfl
    rw [hh]
    simpa using programPureProfileCandidate_nil g hctx σ who
  · have hlatest :
        GameTheory.FOSG.InfoState.latestObservation?
            (G := observedProgramFOSG g hctx) (i := who)
            (h.playerView who) =
          some (privateObsOfCursorWorld who h.lastState,
            publicObsOfCursorWorld h.lastState) := by
      simpa [programLatestObservation?] using
        programLatestObservation?_history_of_ne_nil g hctx who h hnil
    simp [programPureProfileCandidate,
      GameTheory.FOSG.PureProfile.ofLatestObservation,
      GameTheory.FOSG.PureStrategy.ofLatestObservation, hlatest,
      movePureAtProgramObservation?_of_cursorWorld]

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

noncomputable def programBehavioralProfilePMFCandidate
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g) :
    GameTheory.FOSG.BehavioralProfile (observedProgramFOSG g hctx) :=
  GameTheory.FOSG.BehavioralProfile.ofLatestObservation
    (G := observedProgramFOSG g hctx)
    (fun who =>
      moveAtCursorWorldPMF g hctx σ who (CursorCheckedWorld.initial g hctx))
    (fun who obs => moveAtProgramObservationPMF? g hctx σ who obs)

@[simp] theorem programBehavioralProfilePMFCandidate_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g) (who : P) :
    programBehavioralProfilePMFCandidate g hctx σ who
      ((GameTheory.FOSG.History.nil (observedProgramFOSG g hctx)).playerView who) =
      moveAtCursorWorldPMF g hctx σ who (CursorCheckedWorld.initial g hctx) := by
  simp [programBehavioralProfilePMFCandidate,
    GameTheory.FOSG.BehavioralProfile.ofLatestObservation]

theorem programBehavioralProfilePMFCandidate_history
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History) :
    programBehavioralProfilePMFCandidate g hctx σ who (h.playerView who) =
      moveAtCursorWorldPMF g hctx σ who h.lastState := by
  by_cases hnil : h.steps = []
  · have hh :
        h = GameTheory.FOSG.History.nil (observedProgramFOSG g hctx) := by
      cases h with
      | mk steps chain =>
          cases hnil
          rfl
    rw [hh]
    simpa using programBehavioralProfilePMFCandidate_nil g hctx σ who
  · have hlatest :
        GameTheory.FOSG.InfoState.latestObservation?
            (G := observedProgramFOSG g hctx) (i := who)
            (h.playerView who) =
          some (privateObsOfCursorWorld who h.lastState,
            publicObsOfCursorWorld h.lastState) := by
      simpa [programLatestObservation?] using
        programLatestObservation?_history_of_ne_nil g hctx who h hnil
    simp [programBehavioralProfilePMFCandidate,
      GameTheory.FOSG.BehavioralProfile.ofLatestObservation,
      GameTheory.FOSG.BehavioralStrategy.ofLatestObservation, hlatest,
      moveAtProgramObservationPMF?_of_cursorWorld]

theorem programBehavioralProfilePMFCandidate_toBehavioralPMF_eq_pure
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who) :
    programBehavioralProfilePMFCandidate g hctx
        (LegalProgramPureProfile.toBehavioralPMF σ) who s =
      PMF.pure (programPureProfileCandidate g hctx σ who s) := by
  unfold programBehavioralProfilePMFCandidate programPureProfileCandidate
  cases hobs :
      GameTheory.FOSG.InfoState.latestObservation?
        (G := observedProgramFOSG g hctx) (i := who) s with
  | none =>
      simpa [GameTheory.FOSG.BehavioralProfile.ofLatestObservation,
        GameTheory.FOSG.BehavioralStrategy.ofLatestObservation,
        GameTheory.FOSG.PureProfile.ofLatestObservation,
        GameTheory.FOSG.PureStrategy.ofLatestObservation, hobs] using
        moveAtCursorWorldPMF_toBehavioralPMF_eq_pure
          g hctx σ who (CursorCheckedWorld.initial g hctx)
  | some obs =>
      simpa [GameTheory.FOSG.BehavioralProfile.ofLatestObservation,
        GameTheory.FOSG.BehavioralStrategy.ofLatestObservation,
        GameTheory.FOSG.PureProfile.ofLatestObservation,
        GameTheory.FOSG.PureStrategy.ofLatestObservation, hobs] using
        moveAtProgramObservationPMF?_toBehavioralPMF_eq_pure
          g hctx σ who obs

theorem programBehavioralProfilePMFCandidate_support_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History)
    {oi : Option (ProgramAction g.prog who)}
    (hoi : oi ∈
      (programBehavioralProfilePMFCandidate g hctx σ who
        (h.playerView who)).support) :
    oi ∈ (observedProgramFOSG g hctx).availableMoves h who := by
  rw [programBehavioralProfilePMFCandidate_history g hctx σ who h] at hoi
  simpa [GameTheory.FOSG.availableMoves,
    GameTheory.FOSG.availableMovesAtState] using
    moveAtCursorWorldPMF_support_available g hctx σ who h.lastState hoi

/-- Transport a Vegas guard-legal PMF behavioral profile to a legal behavioral
profile of the finite observed-program FOSG. -/
noncomputable def toObservedProgramLegalBehavioralProfilePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g) :
    (observedProgramFOSG g hctx).LegalBehavioralProfile :=
  fun who =>
    ⟨programBehavioralProfilePMFCandidate g hctx σ who, by
      intro h oi hoi
      exact programBehavioralProfilePMFCandidate_support_available
        g hctx σ who h hoi⟩

@[simp] theorem toObservedProgramLegalBehavioralProfilePMF_apply
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g) (who : P) :
    ((toObservedProgramLegalBehavioralProfilePMF g hctx σ who).1) =
      programBehavioralProfilePMFCandidate g hctx σ who := rfl

theorem toObservedProgramLegalBehavioralProfilePMF_toBehavioralPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    toObservedProgramLegalBehavioralProfilePMF g hctx
        (LegalProgramPureProfile.toBehavioralPMF σ) =
      (observedProgramFOSG g hctx).legalPureToBehavioral
        (toObservedProgramLegalPureProfile g hctx σ) := by
  funext who
  apply Subtype.ext
  funext s
  simp [GameTheory.FOSG.legalPureToBehavioral,
    GameTheory.FOSG.pureToBehavioral,
    programBehavioralProfilePMFCandidate_toBehavioralPMF_eq_pure,
    toObservedProgramLegalPureProfile]

end Observed

end FOSGBridge
end Vegas
