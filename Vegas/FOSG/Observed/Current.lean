import Vegas.FOSG.Observed.Pure

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace Observed

/-!
## Current-observation Kuhn model

The reachable FOSG theorem indexes behavioral strategies by full player-event
histories. The total Vegas strategy space is indexed by the current program
cursor and current player view. This file starts the direct bridge: an
`ObsModelCore` whose information state is exactly the current private
observation and whose local actions are optional program moves legal at every
cursor world with that private observation.
-/

/-- Optional program moves that are legal for every cursor world matching the
given current private observation. This is the local action carrier for the
current-observation Kuhn model. -/
abbrev CurrentProgramMove
    (g : WFProgram P L) (who : P) (priv : PrivateObs g who) : Type :=
  { oi : Option (ProgramAction g.prog who) //
    ∀ w : CursorCheckedWorld g,
      privateObsOfCursorWorld who w = priv →
        oi ∈ CursorCheckedWorld.availableProgramMovesAt
          w.1.prog w.1.env w.1.suffix who }

namespace CurrentProgramMove

@[simp] theorem val_mk
    {g : WFProgram P L} {who : P} {priv : PrivateObs g who}
    (oi : Option (ProgramAction g.prog who))
    (h) : ((⟨oi, h⟩ : CurrentProgramMove g who priv).1) = oi := rfl

end CurrentProgramMove

/-- Current private observations are finite for concrete finite expression
languages. -/
@[reducible] noncomputable def PrivateObs.instFintype
    (g : WFProgram P L) (LF : FiniteValuation L) (who : P) :
    Fintype (PrivateObs g who) := by
  classical
  let _ : Fintype (ProgramCursor g.prog) :=
    ProgramCursor.instFintype g.prog
  have hEnv : ∀ c : ProgramCursor g.prog,
      Fintype (VEnv L (viewVCtx who c.Γ)) := fun _ =>
    VEnv.instFintype LF
  let e :
      PrivateObs g who ≃
        Sigma (fun c : ProgramCursor g.prog =>
          VEnv L (viewVCtx who c.Γ)) :=
    { toFun := fun obs => ⟨obs.cursor, obs.env⟩
      invFun := fun obs => { cursor := obs.1, env := obs.2 }
      left_inv := by
        intro obs
        cases obs
        rfl
      right_inv := by
        intro obs
        cases obs
        rfl }
  let _ : ∀ c : ProgramCursor g.prog,
      Fintype (VEnv L (viewVCtx who c.Γ)) := hEnv
  exact Fintype.ofEquiv
    (Sigma (fun c : ProgramCursor g.prog =>
      VEnv L (viewVCtx who c.Γ))) e.symm

/-- Legal current moves are finite because they are a subtype of the finite
program-local optional action carrier. -/
@[reducible] noncomputable def CurrentProgramMove.instFintype
    (g : WFProgram P L) (LF : FiniteValuation L)
    (who : P) (priv : PrivateObs g who) :
    Fintype (CurrentProgramMove g who priv) := by
  classical
  let _ : Fintype (ProgramAction g.prog who) :=
    ProgramAction.instFintype LF g.prog who
  exact Fintype.ofFinite (CurrentProgramMove g who priv)

/-- A legal pure Vegas strategy supplies a legal current-observation move at
every private observation. This is used as the nonempty/fallback witness for
the current-observation Kuhn model. -/
noncomputable def currentProgramMoveOfPureStrategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (priv : PrivateObs g who) :
    CurrentProgramMove g who priv := by
  refine ⟨
    movePureStrategyAtProgramCursor g hctx who σ
      (ProgramCursor.toSuffix priv.cursor)
      (VEnv.eraseEnv priv.env), ?_⟩
  intro w hpriv
  cases hpriv
  have hmove :
      movePureStrategyAtProgramCursor g hctx who σ
          (ProgramCursor.toSuffix (privateObsOfCursorWorld who w).cursor)
          (VEnv.eraseEnv (privateObsOfCursorWorld who w).env) =
        movePureStrategyAtCursorWorld g hctx who σ w := by
    unfold movePureStrategyAtCursorWorld
    rw [privateObsOfCursorWorld_eraseEnv]
    rfl
  rw [hmove]
  exact movePureStrategyAtProgramCursor_availableAt
    g hctx who σ w.1.suffix w.1.env

/-- A pure profile supplies fallback/nonempty witnesses for all players'
current-observation local action types. -/
@[reducible] noncomputable def currentProgramMoveNonemptyOfPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    ∀ who (priv : PrivateObs g who),
      Nonempty (CurrentProgramMove g who priv) :=
  fun who priv => ⟨currentProgramMoveOfPureStrategy g hctx who (σ who) priv⟩

/-- Erase a current-observation joint action to the program-local optional
joint action used by the cursor transition. -/
def currentProgramJointActionRaw
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    (a : ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w)) :
    ProgramJointAction g :=
  fun who => (a who).1

theorem currentProgramJointActionLegal
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    (a : ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w))
    (hterm : ¬ CursorCheckedWorld.terminal w) :
    CursorProgramJointActionLegal w (currentProgramJointActionRaw w a) := by
  constructor
  · exact hterm
  · intro who
    have hmem :
        (currentProgramJointActionRaw w a who) ∈
          CursorCheckedWorld.availableProgramMovesAt
            w.1.prog w.1.env w.1.suffix who :=
      (a who).2 w rfl
    cases hmove : currentProgramJointActionRaw w a who with
    | none =>
        rw [hmove] at hmem
        simpa [currentProgramJointActionRaw,
          CursorProgramJointActionLegal,
          CursorCheckedWorld.availableProgramMovesAt,
          CursorCheckedWorld.active]
          using hmem
    | some ai =>
        rw [hmove] at hmem
        simpa [currentProgramJointActionRaw,
          CursorProgramJointActionLegal,
          CursorCheckedWorld.availableProgramMovesAt,
          CursorCheckedWorld.active,
          CursorCheckedWorld.availableProgramActions]
          using hmem

/-- One-step transition of the current-observation Kuhn model. -/
noncomputable def currentProgramStep
    (g : WFProgram P L)
    (w : CursorCheckedWorld g)
    (a : ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w)) :
    PMF (CursorCheckedWorld g) := by
  classical
  exact
    if hterm : CursorCheckedWorld.terminal w then
      PMF.pure w
    else
      cursorProgramTransition w
        ⟨currentProgramJointActionRaw w a,
          currentProgramJointActionLegal w a hterm⟩

/-- Kuhn core model whose information state is exactly Vegas' current private
observation. Its behavioral profiles are the semantic target for total
Vegas-view PMF behavioral strategies. -/
noncomputable def currentObsModel
    (g : WFProgram P L) (_hctx : WFCtx g.Γ) :
    ObsModelCore P (CursorCheckedWorld g)
      (fun who => PrivateObs g who)
      (fun who priv => CurrentProgramMove g who priv) where
  infoState := fun who => InfoStateCore.identity (PrivateObs g who)
  observe := fun who w => privateObsOfCursorWorld who w
  machine :=
    { init := CursorCheckedWorld.initial g _hctx
      step := fun w a => currentProgramStep g w a }

/-- Embed a legal Vegas pure strategy as a local strategy of the
current-observation Kuhn model. -/
noncomputable def currentLocalPureStrategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who) :
    (currentObsModel g hctx).LocalStrategy who :=
  fun priv => currentProgramMoveOfPureStrategy g hctx who σ priv

/-- Profile-level embedding of legal Vegas pure strategies into the
current-observation Kuhn model. -/
noncomputable def currentLocalPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    (currentObsModel g hctx).PureProfile :=
  fun who => currentLocalPureStrategy g hctx who (σ who)

@[simp] theorem currentLocalPureStrategy_apply_observe
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (w : CursorCheckedWorld g) :
    ((currentLocalPureStrategy g hctx who σ)
        (privateObsOfCursorWorld who w)).1 =
      movePureStrategyAtCursorWorld g hctx who σ w := by
  unfold currentLocalPureStrategy currentProgramMoveOfPureStrategy
  simp only
  unfold movePureStrategyAtCursorWorld
  rw [privateObsOfCursorWorld_eraseEnv]
  rfl

@[simp] theorem currentObsModel_init
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (currentObsModel g hctx).init = CursorCheckedWorld.initial g hctx := rfl

@[simp] theorem currentObsModel_observe
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (w : CursorCheckedWorld g) :
    (currentObsModel g hctx).observe who w =
      privateObsOfCursorWorld who w := rfl

@[simp] theorem currentObsModel_currentObs
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (priv : (currentObsModel g hctx).InfoState who) :
    (currentObsModel g hctx).currentObs who priv = priv := rfl

/-- With identity information states, a projected state trace is exactly the
current private observation at the trace endpoint. This is the deterministic
current-view fact the total Vegas strategy space relies on. -/
theorem currentObsModel_projectStates
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (ss : List (CursorCheckedWorld g)) :
    (currentObsModel g hctx).projectStates who ss =
      privateObsOfCursorWorld who ((currentObsModel g hctx).lastState ss) := by
  have h :=
    (currentObsModel g hctx).currentObs_projectStates who ss
  simpa using h

@[simp] theorem currentObsModel_projectStates_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) :
    (currentObsModel g hctx).projectStates who [] =
      privateObsOfCursorWorld who (CursorCheckedWorld.initial g hctx) := by
  simpa using currentObsModel_projectStates g hctx who []

end Observed

end FOSGBridge
end Vegas
