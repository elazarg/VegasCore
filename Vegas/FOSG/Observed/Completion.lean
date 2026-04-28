import Vegas.FOSG.Observed.Current

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace Observed

/-!
## Completing reachable FOSG behavior to total Vegas behavior

The FOSG M→B proof naturally constructs behavioral choices only at reachable
information states. A Vegas PMF behavioral strategy is total over syntactic
views. This module completes a reachable FOSG profile by using it at reachable
current observations and a legal pure fallback elsewhere.
-/

noncomputable def currentMoveOfAvailableAtHistory
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (h : (observedProgramFOSG g hctx).History)
    (oi : Option (ProgramAction g.prog who))
    (hoi : oi ∈ (observedProgramFOSG g hctx).availableMoves h who) :
    CurrentProgramMove g who (privateObsOfCursorWorld who h.lastState) where
  val := oi
  property := by
    intro w hpriv
    have hEq :=
      observedProgram_availableMovesAtState_eq_of_privateObs_eq
        g hctx who h.lastState w hpriv.symm
    have hoiState :
        oi ∈ (observedProgramFOSG g hctx).availableMovesAtState
          h.lastState who := by
      simpa [GameTheory.FOSG.availableMoves] using hoi
    have hoiW :
        oi ∈ (observedProgramFOSG g hctx).availableMovesAtState
          w who := by
      simpa [hEq] using hoiState
    cases oi with
    | none =>
        simpa [observedProgramFOSG, GameTheory.FOSG.availableMovesAtState,
          GameTheory.FOSG.locallyLegalAtState,
          CursorCheckedWorld.availableProgramMovesAt,
          CursorCheckedWorld.toWorld, CursorCheckedWorld.active] using hoiW
    | some ai =>
        simpa [observedProgramFOSG, GameTheory.FOSG.availableMovesAtState,
          GameTheory.FOSG.locallyLegalAtState,
          CursorCheckedWorld.availableProgramMovesAt,
          CursorCheckedWorld.availableProgramActions,
          CursorCheckedWorld.availableProgramActionsAt,
          CursorCheckedWorld.availableActions, CursorCheckedWorld.toWorld,
          CursorCheckedWorld.active, availableActions] using hoiW

noncomputable def currentMoveOfAvailableAtPrivateObs
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (fallback : LegalProgramPureProfile g)
    (who : P) (priv : PrivateObs g who)
    (h : (observedProgramFOSG g hctx).History)
    (hpriv : privateObsOfCursorWorld who h.lastState = priv)
    (oi : Option (ProgramAction g.prog who)) :
    CurrentProgramMove g who priv := by
  classical
  exact
    if hoi : oi ∈ (observedProgramFOSG g hctx).availableMoves h who then
      hpriv ▸ currentMoveOfAvailableAtHistory g hctx who h oi hoi
    else
      currentProgramMoveOfPureStrategy g hctx who (fallback who) priv

@[simp] theorem currentMoveOfAvailableAtPrivateObs_val_of_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (fallback : LegalProgramPureProfile g)
    (who : P) (priv : PrivateObs g who)
    (h : (observedProgramFOSG g hctx).History)
    (hpriv : privateObsOfCursorWorld who h.lastState = priv)
    (oi : Option (ProgramAction g.prog who))
    (hoi : oi ∈ (observedProgramFOSG g hctx).availableMoves h who) :
    (currentMoveOfAvailableAtPrivateObs
      g hctx fallback who priv h hpriv oi).1 = oi := by
  classical
  unfold currentMoveOfAvailableAtPrivateObs
  simp [hoi]
  cases hpriv
  rfl

noncomputable def completeReachableBehavioralCurrentProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : (observedProgramFOSG g hctx).ReachableLegalBehavioralProfile)
    (fallback : LegalProgramPureProfile g) :
    ObsModelCore.BehavioralProfile (currentObsModel g hctx) := by
  classical
  intro who priv
  by_cases hreach :
      ∃ h : (observedProgramFOSG g hctx).History,
        privateObsOfCursorWorld who h.lastState = priv
  · let h := Classical.choose hreach
    let hpriv : privateObsOfCursorWorld who h.lastState = priv :=
      Classical.choose_spec hreach
    exact PMF.map
      (currentMoveOfAvailableAtPrivateObs
        g hctx fallback who priv h hpriv)
      ((β who).1 ⟨h.playerView who, ⟨h, rfl⟩⟩)
  · exact PMF.pure
      (currentProgramMoveOfPureStrategy g hctx who (fallback who) priv)

end Observed

end FOSGBridge
end Vegas
