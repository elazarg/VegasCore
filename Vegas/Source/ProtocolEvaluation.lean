/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProtocolPolicy
import Vegas.Source.ProtocolTermination

/-! # Agreement with source execution

The continuation law below selects the existing source runner at the current
program point. The protocol law agrees with it after every history, not only
from initialization. The horizon counts remaining source instructions; it is
not a renewed runtime deadline or service budget.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

def joint {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : ∀ who, PurePolicy who program)
    (state : ProtocolState program) : Player → Option (OwnAction Player L) :=
  fun who => (profile who).protocolAction program (observe who program state)

/-- Select the existing source continuation at this program point. -/
def continuationLaw : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (BehavioralProfile program) →
    ProtocolState program → FinDist (State L program.terminalCtx)
  | _, _, .ret _ => fun _ config => FinDist.pure config.state
  | _, _, .sample name fresh law next => fun profile =>
      Sum.elim
        (fun config => runFrom (.sample name fresh law next)
          profile config)
        (continuationLaw next profile)
  | _, _, .commit name owner fresh guard next => fun profile =>
      Sum.elim
        (fun config => runFrom (.commit name owner fresh guard next)
          profile config)
        (continuationLaw next (fun who => (profile who).2))
  | _, _, .reveal published owner name fresh source unresolved next => fun profile =>
      Sum.elim
        (fun config => runFrom (.reveal published owner name fresh source unresolved next)
          profile config)
        (continuationLaw next (fun who => (profile who).2))

@[simp] theorem continuationLaw_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (config : Config Player L Γ) :
    continuationLaw program profile (entry program config) =
      runFrom program profile config := by
  cases program <;> rfl

/-- Read a terminal store only at a return point. -/
def readout : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program →
    Option (State L program.terminalCtx)
  | _, _, .ret _ => fun config => some config.state
  | _, _, .sample _ _ _ next => Sum.elim (fun _ => none) (readout next)
  | _, _, .commit _ _ _ _ next => Sum.elim (fun _ => none) (readout next)
  | _, _, .reveal _ _ _ _ _ _ next => Sum.elim (fun _ => none) (readout next)

theorem continuationLaw_terminal : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (profile : BehavioralProfile program) →
    (state : ProtocolState program) → terminal program state →
    (continuationLaw program profile state).map some = FinDist.pure (readout program state)
  | _, _, .ret _, _, _, _ => FinDist.map_pure _ _
  | _, _, .sample _ _ _ next, profile, state, stopped => by
      cases state with
      | inl config => exact stopped.elim
      | inr rest => exact continuationLaw_terminal next profile rest stopped
  | _, _, .commit _ _ _ _ next, profile, state, stopped => by
      cases state with
      | inl config => exact stopped.elim
      | inr rest => exact continuationLaw_terminal next (fun who => (profile who).2) rest stopped
  | _, _, .reveal _ _ _ _ _ _ next, profile, state, stopped => by
      cases state with
      | inl config => exact stopped.elim
      | inr rest => exact continuationLaw_terminal next (fun who => (profile who).2) rest stopped

theorem continuationLaw_step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (profile : ∀ who, PurePolicy who program) →
    (state : ProtocolState program) → ¬ terminal program state →
    (step program state (joint program profile state)).bind (continuationLaw program
      (fun who => (profile who).toBehavioral program)) =
      continuationLaw program (fun who => (profile who).toBehavioral program) state
  | _, _, .ret _, _, _, running => (running trivial).elim
  | _, _, .sample _ _ _ next, profile, state, running => by
      cases state with
      | inl config =>
          simp [step, continuationLaw, FinDist.bind_map, runFrom_sample,
            PurePolicy.toBehavioral]
          rfl
      | inr rest =>
          dsimp only [step, continuationLaw, Sum.elim]
          rw [FinDist.bind_map]
          exact continuationLaw_step next profile rest running
  | _, _, .commit _ _ _ _ next, profile, state, running => by
      cases state with
      | inl config =>
          simp [step, joint, observe, PurePolicy.protocolAction, continuationLaw,
            runFrom_commit, commitKernel, PurePolicy.toBehavioral, Config.view]
          rfl
      | inr rest =>
          dsimp only [step, continuationLaw, Sum.elim]
          rw [FinDist.bind_map]
          exact continuationLaw_step next (fun who => (profile who).2) rest running
  | _, _, .reveal _ _ _ _ _ _ next, profile, state, running => by
      cases state with
      | inl config =>
          simp [step, joint, observe, PurePolicy.protocolAction, continuationLaw,
            runFrom_reveal, revealKernel, PurePolicy.toBehavioral,
            Config.view, OwnAction.disclosure]
          rfl
      | inr rest =>
          dsimp only [step, continuationLaw, Sum.elim]
          rw [FinDist.bind_map]
          exact continuationLaw_step next (fun who => (profile who).2) rest running

end ProtocolState

/-- The same information-local choices, presented to the canonical state
runner for the execution-law proof. -/
def protocolChooser {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) (profile : ∀ who, PurePolicy who program)
    (permitted : ∀ who, (profile who).Admitted program admission) :
    (executionProtocol program admission initial).Chooser := fun state running =>
  ⟨ProtocolState.joint program profile state, running, by
    intro who
    have legal := (profile who).protocolAction_mem_menu program admission
      (permitted who) (ProtocolState.observe who program state)
    change ProtocolView.menu who program admission (ProtocolState.observe who program state)
      (ProtocolState.joint program profile state who) at legal
    cases selected : ProtocolState.joint program profile state who <;>
      simpa only [ProtocolView.menu, selected, executionProtocol] using legal⟩

theorem protocol_runFor_eq {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) (profile : ∀ who, PurePolicy who program)
    (permitted : ∀ who, (profile who).Admitted program admission) (fuel : Nat)
    (state : ProtocolState program) (enough : ProtocolState.remaining program state ≤ fuel) :
    ((executionProtocol program admission initial).runFor
      (protocolChooser program admission initial profile permitted) fuel state).map
        (ProtocolState.readout program) =
      (ProtocolState.continuationLaw program
        (fun who => (profile who).toBehavioral program) state).map some := by
  induction fuel generalizing state with
  | zero =>
      have stopped := (ProtocolState.remaining_zero_iff_terminal program state).mp (by omega)
      simpa using (ProtocolState.continuationLaw_terminal program
        (fun who => (profile who).toBehavioral program) state stopped).symm
  | succ fuel ih =>
      by_cases stopped : ProtocolState.terminal program state
      · rw [ExecutionProtocol.runFor_of_terminal _ _ stopped, FinDist.map_pure]
        exact (ProtocolState.continuationLaw_terminal program
          (fun who => (profile who).toBehavioral program) state stopped).symm
      · rw [ExecutionProtocol.runFor_succ_of_not_terminal _ _ stopped, FinDist.map_bind]
        change (ProtocolState.step program state (ProtocolState.joint program profile state)).bind
          _ = _
        calc
          _ = (ProtocolState.step program state (ProtocolState.joint program profile state)).bind
                (fun after => (ProtocolState.continuationLaw program
                (fun who => (profile who).toBehavioral program) after).map some) := by
            apply FinDist.bind_congr
            intro after reached
            have consumed := ProtocolState.remaining_step program state after
              (ProtocolState.joint program profile state) stopped reached
            exact ih after (by omega)
          _ = ((ProtocolState.step program state (ProtocolState.joint program profile state)).bind
              (ProtocolState.continuationLaw program
                (fun who => (profile who).toBehavioral program))).map some :=
            (FinDist.map_bind _ _ _).symm
          _ = _ := congrArg (fun law => law.map some)
            (ProtocolState.continuationLaw_step program profile state stopped)

theorem protocol_historyChooser_eq {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) (profile : ∀ who, PurePolicy who program)
    (permitted : ∀ who, (profile who).Admitted program admission) :
    (informationModel program admission initial).historyChooser
        (fun who => (profile who).toProtocol program admission (permitted who)) =
      (protocolChooser program admission initial profile permitted).toHistoryChooser := by
  funext history running
  apply Subtype.ext
  funext who
  change (profile who).protocolAction program
      ((protocolSignals program admission initial).infoOf who history.trace) =
    (profile who).protocolAction program (ProtocolState.observe who program history.state)
  rw [protocol_info]

/-- Exact agreement at every canonical history, including histories outside
the compiled profile's support. Private state and own-action recall are kept
at the supplied prefix. -/
theorem protocol_runFrom_eq {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) (profile : ∀ who, PurePolicy who program)
    (permitted : ∀ who, (profile who).Admitted program admission) (fuel : Nat)
    (history : (executionProtocol program admission initial).History)
    (enough : ProtocolState.remaining program history.state ≤ fuel) :
    ((informationModel program admission initial).runFrom
      (fun who => (profile who).toProtocol program admission (permitted who)) fuel history).map
        (fun final => ProtocolState.readout program final.state) =
      (ProtocolState.continuationLaw program
        (fun who => (profile who).toBehavioral program) history.state).map some := by
  unfold InformationModel.runFrom
  rw [protocol_historyChooser_eq]
  calc
    _ = (((executionProtocol program admission initial).runHistoryFor
        (protocolChooser program admission initial profile permitted).toHistoryChooser
        fuel history).map ExecutionProtocol.History.state).map
          (ProtocolState.readout program) := by rw [FinDist.map_comp]; rfl
    _ = _ := by
      rw [ExecutionProtocol.map_state_runHistoryFor]
      exact protocol_runFor_eq program admission initial profile permitted fuel history.state enough

/-- Initialization is the empty-prefix case of the continuation law. -/
theorem protocol_run_eq {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) (profile : ∀ who, PurePolicy who program)
    (permitted : ∀ who, (profile who).Admitted program admission) :
    ((informationModel program admission initial).run
      (fun who => (profile who).toProtocol program admission (permitted who))
      (instructionCount program)).map (fun final => ProtocolState.readout program final.state) =
      (runFrom program (fun who => (profile who).toBehavioral program) initial).map some := by
  unfold InformationModel.run
  rw [protocol_runFrom_eq program admission initial profile permitted
    (instructionCount program) _ (by simp [executionProtocol, ExecutionProtocol.initHistory])]
  exact congrArg (fun law => law.map some)
    (ProtocolState.continuationLaw_entry program
      (fun who => (profile who).toBehavioral program) initial)

end Vegas.SourceProgram
