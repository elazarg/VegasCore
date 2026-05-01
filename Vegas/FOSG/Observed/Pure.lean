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

theorem movePureAtProgramCursor_suffix_cast
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) (who : P)
    {Γ : VCtx P L} {p q : VegasCore P L Γ}
    (h : p = q)
    (suffix : ProgramSuffix g.prog p)
    (view : ViewEnv who Γ) :
    movePureAtProgramCursor g hctx σ who suffix view =
      movePureAtProgramCursor g hctx σ who (h ▸ suffix) view := by
  cases h
  rfl

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

theorem movePureStrategyAtProgramCursor_suffix_cast
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    {Γ : VCtx P L} {p q : VegasCore P L Γ}
    (h : p = q)
    (suffix : ProgramSuffix g.prog p)
    (view : ViewEnv who Γ) :
    movePureStrategyAtProgramCursor g hctx who σ suffix view =
      movePureStrategyAtProgramCursor g hctx who σ (h ▸ suffix) view := by
  cases h
  rfl

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

@[simp] theorem movePureStrategyAtProgramCursor_commit_nonowner
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {owner who : P} (σ : LegalProgramPureStrategy g who)
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden owner b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x owner R k))
    (view : ViewEnv who Γ) (howner : owner ≠ who) :
    movePureStrategyAtProgramCursor g hctx who σ suffix view = none := by
  simp [movePureStrategyAtProgramCursor, howner]

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
              ProgramPureProfile.toBehavioral
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
    (priv.env)

noncomputable def moveAtProgramObservationPMF?
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P)
    (obs : PrivateObs g who × PublicObs g hctx) :
    PMF (Option (ProgramAction g.prog who)) := by
  let priv := obs.1
  exact moveAtProgramCursorPMF g hctx σ who priv.cursor.toSuffix
    (priv.env)

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
      ((privateObsOfCursorWorld who w).env) =
    moveAtProgramCursor g hctx σ who w.1.suffix
      (projectViewEnv who (VEnv.eraseEnv w.1.env))
  rw [privateObsOfCursorWorld_eraseEnv]
  rfl

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

theorem moveAtProgramObservationPMF?_toPMFProfile_eq
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    (obs : PrivateObs g who × PublicObs g hctx) :
    moveAtProgramObservationPMF? g hctx
        (LegalProgramBehavioralProfile.toPMFProfile σ) who obs =
      moveAtProgramObservation? g hctx σ who obs := by
  unfold moveAtProgramObservationPMF? moveAtProgramObservation?
  exact moveAtProgramCursorPMF_toPMFProfile_eq
    g hctx σ who obs.1.cursor.toSuffix obs.1.env

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
  have hlatest :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := observedProgramFOSG g hctx) (i := who)
          (h.playerView who ++
            (⟨h.lastState, a, dst, support⟩ :
              (observedProgramFOSG g hctx).Step).playerView who) =
        some (privateObsOfCursorWorld who dst,
          publicObsOfCursorWorld dst) := by
    rw [← GameTheory.FOSG.History.playerView_snoc]
    simpa [programLatestObservation?] using
      programLatestObservation?_history_snoc g hctx who h a dst support
  simp [programPureStrategyCandidate,
    GameTheory.FOSG.PureStrategy.ofLatestObservation, hlatest,
    movePureStrategyAtProgramObservation?_of_cursorWorld]

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
  simp [programPureProfileCandidate,
    GameTheory.FOSG.PureProfile.ofLatestObservation]

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
  have hlatest :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := observedProgramFOSG g hctx) (i := who)
          (h.playerView who ++
            (⟨h.lastState, a, dst, support⟩ :
              (observedProgramFOSG g hctx).Step).playerView who) =
        some (privateObsOfCursorWorld who dst,
          publicObsOfCursorWorld dst) := by
    rw [← GameTheory.FOSG.History.playerView_snoc]
    simpa [programLatestObservation?] using
      programLatestObservation?_history_snoc g hctx who h a dst support
  simp [programPureProfileCandidate,
    GameTheory.FOSG.PureProfile.ofLatestObservation,
    GameTheory.FOSG.PureStrategy.ofLatestObservation, hlatest,
    movePureAtProgramObservation?_of_cursorWorld]

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
  GameTheory.FOSG.BehavioralProfile.ofLatestObservation
    (G := observedProgramFOSG g hctx)
    (fun who =>
      moveAtCursorWorld g hctx σ who (CursorCheckedWorld.initial g hctx))
    (fun who obs => moveAtProgramObservation? g hctx σ who obs)

@[simp] theorem programBehavioralProfileCandidate_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    programBehavioralProfileCandidate g hctx σ who
      ((GameTheory.FOSG.History.nil (observedProgramFOSG g hctx)).playerView who) =
      moveAtCursorWorld g hctx σ who (CursorCheckedWorld.initial g hctx) := by
  simp [programBehavioralProfileCandidate,
    GameTheory.FOSG.BehavioralProfile.ofLatestObservation]

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
  have hlatest :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := observedProgramFOSG g hctx) (i := who)
          (h.playerView who ++
            (⟨h.lastState, a, dst, support⟩ :
              (observedProgramFOSG g hctx).Step).playerView who) =
        some (privateObsOfCursorWorld who dst,
          publicObsOfCursorWorld dst) := by
    rw [← GameTheory.FOSG.History.playerView_snoc]
    simpa [programLatestObservation?] using
      programLatestObservation?_history_snoc g hctx who h a dst support
  simp [programBehavioralProfileCandidate,
    GameTheory.FOSG.BehavioralProfile.ofLatestObservation,
    GameTheory.FOSG.BehavioralStrategy.ofLatestObservation, hlatest,
    moveAtProgramObservation?_of_cursorWorld]

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
  have hlatest :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := observedProgramFOSG g hctx) (i := who)
          (h.playerView who ++
            (⟨h.lastState, a, dst, support⟩ :
              (observedProgramFOSG g hctx).Step).playerView who) =
        some (privateObsOfCursorWorld who dst,
          publicObsOfCursorWorld dst) := by
    rw [← GameTheory.FOSG.History.playerView_snoc]
    simpa [programLatestObservation?] using
      programLatestObservation?_history_snoc g hctx who h a dst support
  simp [programBehavioralProfileCandidate,
    GameTheory.FOSG.BehavioralProfile.ofLatestObservation,
    GameTheory.FOSG.BehavioralStrategy.ofLatestObservation, hlatest,
    moveAtProgramObservation?_of_cursorWorld] at hoi
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

@[simp] theorem programBehavioralProfilePMFCandidate_snoc
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (a : (observedProgramFOSG g hctx).LegalAction h.lastState)
    (dst : CursorCheckedWorld g)
    (support : (observedProgramFOSG g hctx).transition h.lastState a dst ≠ 0) :
    programBehavioralProfilePMFCandidate g hctx σ who
      ((h.snoc a dst support).playerView who) =
      moveAtCursorWorldPMF g hctx σ who dst := by
  have hlatest :
      GameTheory.FOSG.InfoState.latestObservation?
          (G := observedProgramFOSG g hctx) (i := who)
          (h.playerView who ++
            (⟨h.lastState, a, dst, support⟩ :
              (observedProgramFOSG g hctx).Step).playerView who) =
        some (privateObsOfCursorWorld who dst,
          publicObsOfCursorWorld dst) := by
    rw [← GameTheory.FOSG.History.playerView_snoc]
    simpa [programLatestObservation?] using
      programLatestObservation?_history_snoc g hctx who h a dst support
  simp [programBehavioralProfilePMFCandidate,
    GameTheory.FOSG.BehavioralProfile.ofLatestObservation,
    GameTheory.FOSG.BehavioralStrategy.ofLatestObservation, hlatest,
    moveAtProgramObservationPMF?_of_cursorWorld]

@[simp] theorem programBehavioralProfilePMFCandidate_appendStep
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (e : (observedProgramFOSG g hctx).Step)
    (hsrc : e.src = h.lastState) :
    programBehavioralProfilePMFCandidate g hctx σ who
      ((h.appendStep e hsrc).playerView who) =
      moveAtCursorWorldPMF g hctx σ who (h.appendStep e hsrc).lastState := by
  cases e with
  | mk src act dst support =>
      cases hsrc
      change
        programBehavioralProfilePMFCandidate g hctx σ who
          ((h.snoc act dst support).playerView who) =
        moveAtCursorWorldPMF g hctx σ who (h.snoc act dst support).lastState
      simpa using
        programBehavioralProfilePMFCandidate_snoc
          g hctx σ who h act dst support

theorem programBehavioralProfilePMFCandidate_history
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P)
    (h : (observedProgramFOSG g hctx).History) :
    programBehavioralProfilePMFCandidate g hctx σ who (h.playerView who) =
      moveAtCursorWorldPMF g hctx σ who h.lastState := by
  let G := observedProgramFOSG g hctx
  cases h with
  | mk steps chain =>
      induction steps using List.reverseRecOn with
      | nil =>
          simp [programBehavioralProfilePMFCandidate,
            GameTheory.FOSG.History.playerView,
            GameTheory.FOSG.History.playerViewFrom,
            GameTheory.FOSG.History.lastState,
            GameTheory.FOSG.lastStateFrom,
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
          exact programBehavioralProfilePMFCandidate_appendStep
            g hctx σ who hprefix e hsrc

theorem programBehavioralProfilePMFCandidate_toPMFProfile_eq
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    programBehavioralProfilePMFCandidate g hctx
        (LegalProgramBehavioralProfile.toPMFProfile σ) =
      programBehavioralProfileCandidate g hctx σ := by
  funext who s
  unfold programBehavioralProfilePMFCandidate
    programBehavioralProfileCandidate
  cases hobs :
      GameTheory.FOSG.InfoState.latestObservation?
        (G := observedProgramFOSG g hctx) (i := who) s with
  | none =>
      simp [GameTheory.FOSG.BehavioralProfile.ofLatestObservation,
        GameTheory.FOSG.BehavioralStrategy.ofLatestObservation, hobs,
        moveAtCursorWorldPMF_toPMFProfile_eq]
  | some obs =>
      simp [GameTheory.FOSG.BehavioralProfile.ofLatestObservation,
        GameTheory.FOSG.BehavioralStrategy.ofLatestObservation, hobs,
        moveAtProgramObservationPMF?_toPMFProfile_eq]

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

noncomputable def toObservedProgramLegalBehavioralProfilePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g) :
    (observedProgramFOSG g hctx).LegalBehavioralProfile :=
  fun who =>
    ⟨programBehavioralProfilePMFCandidate g hctx σ who, by
      intro h oi hoi
      exact programBehavioralProfilePMFCandidate_support_available
        g hctx σ who h hoi⟩

@[simp] theorem toObservedProgramLegalBehavioralProfile_apply
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    ((toObservedProgramLegalBehavioralProfile g hctx σ who).1) =
      programBehavioralProfileCandidate g hctx σ who := rfl

@[simp] theorem toObservedProgramLegalBehavioralProfilePMF_apply
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g) (who : P) :
    ((toObservedProgramLegalBehavioralProfilePMF g hctx σ who).1) =
      programBehavioralProfilePMFCandidate g hctx σ who := rfl

theorem toObservedProgramLegalBehavioralProfilePMF_toPMFProfile_eq
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    toObservedProgramLegalBehavioralProfilePMF g hctx
        (LegalProgramBehavioralProfile.toPMFProfile σ) =
      toObservedProgramLegalBehavioralProfile g hctx σ := by
  funext who
  apply Subtype.ext
  exact congrFun
    (programBehavioralProfilePMFCandidate_toPMFProfile_eq
      g hctx σ) who

/-- Transport a Vegas guard-legal behavioral profile to the reachable-information
strategy space of the observed-program FOSG. -/
noncomputable def toObservedProgramReachableLegalBehavioralProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    (observedProgramFOSG g hctx).ReachableLegalBehavioralProfile :=
  fun who =>
    (toObservedProgramLegalBehavioralProfile g hctx σ who).restrictReachable

noncomputable def toObservedProgramReachableLegalBehavioralProfilePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g) :
    (observedProgramFOSG g hctx).ReachableLegalBehavioralProfile :=
  fun who =>
    (toObservedProgramLegalBehavioralProfilePMF g hctx σ who).restrictReachable

theorem programBehavioralProfileCandidate_toBehavioral_eq_pure
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g)
    (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who) :
    programBehavioralProfileCandidate g hctx
        (LegalProgramPureProfile.toBehavioral σ) who s =
      PMF.pure (programPureProfileCandidate g hctx σ who s) := by
  unfold programBehavioralProfileCandidate programPureProfileCandidate
  cases hobs :
      GameTheory.FOSG.InfoState.latestObservation?
        (G := observedProgramFOSG g hctx) (i := who) s with
  | none =>
      simpa [GameTheory.FOSG.BehavioralProfile.ofLatestObservation,
        GameTheory.FOSG.BehavioralStrategy.ofLatestObservation,
        GameTheory.FOSG.PureProfile.ofLatestObservation,
        GameTheory.FOSG.PureStrategy.ofLatestObservation, hobs] using
        moveAtCursorWorld_toBehavioral_eq_pure
          g hctx σ who (CursorCheckedWorld.initial g hctx)
  | some obs =>
      simpa [GameTheory.FOSG.BehavioralProfile.ofLatestObservation,
        GameTheory.FOSG.BehavioralStrategy.ofLatestObservation,
        GameTheory.FOSG.PureProfile.ofLatestObservation,
        GameTheory.FOSG.PureStrategy.ofLatestObservation, hobs] using
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

end Observed

end FOSGBridge
end Vegas
