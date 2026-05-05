import Vegas.FOSG.Cursor.Behavioral

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Pure profile candidate

The pure transport is the deterministic counterpart of the behavioral transport
above. It is needed to state the Kuhn correspondence against GameTheory's FOSG
strategy API without weakening the Vegas strategy spaces.
-/

noncomputable def movePureAtProgramCursor
    (g : WFProgram P L) (_hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g)
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
    (who : P) (σ : FeasibleProgramPureStrategy g who)
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
    (σ : FeasibleProgramPureProfile g)
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
    (σ : FeasibleProgramPureProfile g)
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
    {who : P} (σ : FeasibleProgramPureStrategy g who)
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
    (σ : FeasibleProgramPureProfile g)
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
  have hraw : raw.RespectsGuards := fun i => (σ i).2
  have hcursor : (suffix.pureProfile raw).RespectsGuards :=
    suffix.pureProfile_isLegal hraw
  have hsite := hcursor who
  simp [ProgramPureStrategy.RespectsGuards] at hsite
  simpa [raw] using hsite.1 ρ

theorem headPureStrategyKernel_legal_atCursor
    (g : WFProgram P L) (_hctx : WFCtx g.Γ)
    {who : P} (σ : FeasibleProgramPureStrategy g who)
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
      (suffix.pureStrategy who σ.val).RespectsGuards
        (.commit x who R k) :=
    suffix.pureStrategy_isLegal who σ.2
  let σc :
      PureKernel who Γ b ×
        ProgramPureStrategy who k := by
    simpa [ProgramPureStrategy] using suffix.pureStrategy who σ.val
  have hsite :
      σc.1.RespectsGuard (x := x) (who := who)
          (b := b) R ∧ σc.2.RespectsGuards k := by
    simpa [ProgramPureStrategy.RespectsGuards, σc] using hcursor
  simpa [ProgramPureStrategy.headKernel, σc] using hsite.1 ρ

noncomputable def movePureAtCursorWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g)
    (who : P) (w : CursorCheckedWorld g) :
    Option (ProgramAction g.prog who) :=
  movePureAtProgramCursor g hctx σ who w.1.suffix
    (projectViewEnv who (VEnv.eraseEnv w.1.env))

noncomputable def movePureStrategyAtCursorWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : FeasibleProgramPureStrategy g who)
    (w : CursorCheckedWorld g) :
    Option (ProgramAction g.prog who) :=
  movePureStrategyAtProgramCursor g hctx who σ w.1.suffix
    (projectViewEnv who (VEnv.eraseEnv w.1.env))

theorem movePureAtProgramCursor_availableAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g)
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
    (who : P) (σ : FeasibleProgramPureStrategy g who)
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
    (σ : FeasibleProgramPureProfile g)
    (who : P) (w : CursorCheckedWorld g) :
    movePureAtCursorWorld g hctx σ who w ∈
      (cursorFOSG g hctx).availableMovesAtState w who := by
  have hlocal :=
    movePureAtProgramCursor_availableAt
      g hctx σ who w.1.suffix w.1.env
  cases hmove : movePureAtCursorWorld g hctx σ who w with
  | none =>
      change movePureAtProgramCursor g hctx σ who w.1.suffix
          (projectViewEnv who (VEnv.eraseEnv w.1.env)) = none at hmove
      rw [hmove] at hlocal
      simpa [movePureAtCursorWorld, cursorFOSG,
        GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, active,
        CursorCheckedWorld.availableProgramMovesAt, CursorCheckedWorld.toWorld,
        hmove] using hlocal
  | some ai =>
      change movePureAtProgramCursor g hctx σ who w.1.suffix
          (projectViewEnv who (VEnv.eraseEnv w.1.env)) = some ai at hmove
      rw [hmove] at hlocal
      simpa [movePureAtCursorWorld, cursorFOSG,
        GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, active,
        CursorCheckedWorld.availableProgramActions,
        CursorCheckedWorld.availableProgramActionsAt,
        CursorCheckedWorld.availableProgramMovesAt, availableActions,
        CursorCheckedWorld.toWorld, availableActions, hmove] using hlocal

theorem movePureStrategyAtCursorWorld_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : FeasibleProgramPureStrategy g who)
    (w : CursorCheckedWorld g) :
    movePureStrategyAtCursorWorld g hctx who σ w ∈
      (cursorFOSG g hctx).availableMovesAtState w who := by
  have hlocal :=
    movePureStrategyAtProgramCursor_availableAt
      g hctx who σ w.1.suffix w.1.env
  cases hmove : movePureStrategyAtCursorWorld g hctx who σ w with
  | none =>
      change movePureStrategyAtProgramCursor g hctx who σ w.1.suffix
          (projectViewEnv who (VEnv.eraseEnv w.1.env)) = none at hmove
      rw [hmove] at hlocal
      simpa [movePureStrategyAtCursorWorld, cursorFOSG,
        GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, active,
        CursorCheckedWorld.availableProgramMovesAt, CursorCheckedWorld.toWorld,
        hmove] using hlocal
  | some ai =>
      change movePureStrategyAtProgramCursor g hctx who σ w.1.suffix
          (projectViewEnv who (VEnv.eraseEnv w.1.env)) = some ai at hmove
      rw [hmove] at hlocal
      simpa [movePureStrategyAtCursorWorld, cursorFOSG,
        GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, active,
        CursorCheckedWorld.availableProgramActions,
        CursorCheckedWorld.availableProgramActionsAt,
        CursorCheckedWorld.availableProgramMovesAt, availableActions,
        CursorCheckedWorld.toWorld, availableActions, hmove] using hlocal

theorem moveAtProgramCursorPMF_toBehavioralPMF_eq_pure
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g)
    (who : P) {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p)
    (view : ViewEnv who Γ) :
    moveAtProgramCursorPMF g hctx
        (FeasibleProgramPureProfile.toBehavioralPMF σ) who suffix view =
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
                (fun i => ((FeasibleProgramPureProfile.toBehavioralPMF
                  (g := g) σ) i).val) =
              ProgramPureProfile.toBehavioralPMF
                (.commit x who R k) (suffix.pureProfile raw) := by
          simpa [raw, FeasibleProgramPureProfile.toBehavioralPMF] using
            ProgramSuffix.behavioralProfilePMF_toBehavioralPMF
              (s := suffix) raw
        simp [moveAtProgramCursorPMF, movePureAtProgramCursor, hprofile,
          ProgramPureProfile.toBehavioralPMF,
          ProgramBehavioralStrategyPMF.headKernel,
          PMF.pure_map, raw]
      · simp [moveAtProgramCursorPMF, movePureAtProgramCursor, howner]

theorem moveAtCursorWorldPMF_toBehavioralPMF_eq_pure
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g)
    (who : P) (w : CursorCheckedWorld g) :
    moveAtCursorWorldPMF g hctx
        (FeasibleProgramPureProfile.toBehavioralPMF σ) who w =
      PMF.pure (movePureAtCursorWorld g hctx σ who w) := by
  exact moveAtProgramCursorPMF_toBehavioralPMF_eq_pure
    g hctx σ who w.1.suffix
      (projectViewEnv who (VEnv.eraseEnv w.1.env))

noncomputable def moveAtProgramObservationPMF?
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (who : P)
    (obs : PrivateObs g who × PublicObs g hctx) :
    PMF (Option (ProgramAction g.prog who)) := by
  let priv := obs.1
  exact moveAtProgramCursorPMF g hctx σ who priv.cursor.toSuffix
    (priv.env)

theorem moveAtProgramObservationPMF?_of_cursorWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramBehavioralProfilePMF g)
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

/-- Program-action pure observation lookup for the final `cursorFOSG`
target. -/
noncomputable def movePureAtProgramObservation?
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g)
    (who : P)
    (obs : PrivateObs g who × PublicObs g hctx) :
    Option (ProgramAction g.prog who) := by
  let priv := obs.1
  exact movePureAtProgramCursor g hctx σ who priv.cursor.toSuffix
    (priv.env)

noncomputable def movePureStrategyAtProgramObservation?
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : FeasibleProgramPureStrategy g who)
    (obs : PrivateObs g who × PublicObs g hctx) :
    Option (ProgramAction g.prog who) := by
  let priv := obs.1
  exact movePureStrategyAtProgramCursor g hctx who σ priv.cursor.toSuffix
    (priv.env)

theorem moveAtProgramObservationPMF?_toBehavioralPMF_eq_pure
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g)
    (who : P)
    (obs : PrivateObs g who × PublicObs g hctx) :
    moveAtProgramObservationPMF? g hctx
        (FeasibleProgramPureProfile.toBehavioralPMF σ) who obs =
      PMF.pure (movePureAtProgramObservation? g hctx σ who obs) := by
  unfold moveAtProgramObservationPMF? movePureAtProgramObservation?
  exact moveAtProgramCursorPMF_toBehavioralPMF_eq_pure
    g hctx σ who obs.1.cursor.toSuffix obs.1.env

theorem movePureAtProgramObservation?_eq_strategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g)
    (who : P)
    (obs : PrivateObs g who × PublicObs g hctx) :
    movePureAtProgramObservation? g hctx σ who obs =
      movePureStrategyAtProgramObservation? g hctx who (σ who) obs := by
  unfold movePureAtProgramObservation? movePureStrategyAtProgramObservation?
  exact movePureAtProgramCursor_eq_strategy g hctx σ who _ _

theorem movePureAtProgramObservation?_of_cursorWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramPureProfile g)
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
    (who : P) (σ : FeasibleProgramPureStrategy g who)
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

end Vegas
