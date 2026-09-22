/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.SetupProtocolPolicy

/-! # Source protocol laws across private setup

At the initial chance position the law integrates over setup. After the draw
it evaluates the retained configuration. The theorem preserves the complete
terminal store, hence every joint reading of persistent types and public data.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def continuationLaw (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) :
    setup.ProtocolState → FinDist (State L setup.program.terminalCtx)
  | none => setup.run profile
  | some state => SourceProgram.ProtocolState.continuationLaw setup.program profile state

def protocolReadout (setup : Setup (Player := Player) (L := L))
    (state : setup.ProtocolState) : Option (State L setup.program.terminalCtx) :=
  state.bind (SourceProgram.ProtocolState.readout setup.program)

def protocolJoint (setup : Setup (Player := Player) (L := L))
    (profile : ∀ who, PurePolicy who setup.program) :
    setup.ProtocolState → Player → Option (OwnAction Player L)
  | none => fun _ => none
  | some state => SourceProgram.ProtocolState.joint setup.program profile state

theorem continuationLaw_terminal (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) (state : setup.ProtocolState)
    (stopped : state.elim False (SourceProgram.ProtocolState.terminal setup.program)) :
    (setup.continuationLaw profile state).map some =
      FinDist.pure (setup.protocolReadout state) := by
  cases state with
  | none => exact stopped.elim
  | some state =>
      exact SourceProgram.ProtocolState.continuationLaw_terminal setup.program profile state stopped

theorem continuationLaw_step (setup : Setup (Player := Player) (L := L))
    (profile : ∀ who, PurePolicy who setup.program) (state : setup.ProtocolState)
    (running : ¬ state.elim False (SourceProgram.ProtocolState.terminal setup.program)) :
    (setup.protocolStep state (setup.protocolJoint profile state)).bind
        (setup.continuationLaw
          (fun who => (profile who).toBehavioral setup.program)) =
      setup.continuationLaw (fun who => (profile who).toBehavioral setup.program) state := by
  cases state with
  | none =>
      simp [protocolStep, FinDist.bind_map, continuationLaw, run, initialConfig,
        SourceProgram.run, runFrom]
  | some state =>
      simp only [protocolStep, FinDist.bind_map, continuationLaw, protocolJoint]
      exact SourceProgram.ProtocolState.continuationLaw_step setup.program profile state running

def protocolChooser (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (profile : ∀ who, PurePolicy who setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission) :
    (setup.executionProtocol admission).Chooser := fun state running =>
  ⟨setup.protocolJoint profile state, running, by
    intro who
    cases state with
    | none => exact fun impossible => impossible
    | some state =>
        have legal := (profile who).protocolAction_mem_menu setup.program admission
          (permitted who) (SourceProgram.ProtocolState.observe who setup.program state)
        change SourceProgram.ProtocolView.menu who setup.program admission
          (SourceProgram.ProtocolState.observe who setup.program state)
          (SourceProgram.ProtocolState.joint setup.program profile state who) at legal
        cases selected : SourceProgram.ProtocolState.joint setup.program profile state who <;>
          simpa only [SourceProgram.ProtocolView.menu, selected, executionProtocol,
            protocolJoint, protocolObserve, Option.map_some, Option.elim_some] using legal⟩

theorem protocol_runFor_eq (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (profile : ∀ who, PurePolicy who setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission) (fuel : Nat)
    (state : setup.ProtocolState) (enough : setup.protocolRemaining state ≤ fuel) :
    ((setup.executionProtocol admission).runFor
      (setup.protocolChooser admission profile permitted) fuel state).map setup.protocolReadout =
      (setup.continuationLaw
        (fun who => (profile who).toBehavioral setup.program) state).map some := by
  induction fuel generalizing state with
  | zero =>
      cases state with
      | none => simp [protocolRemaining] at enough
      | some state =>
          have stopped := (SourceProgram.ProtocolState.remaining_zero_iff_terminal
            setup.program state).mp (Nat.eq_zero_of_le_zero enough)
          simpa using (setup.continuationLaw_terminal
            (fun who => (profile who).toBehavioral setup.program) (some state) stopped).symm
  | succ fuel ih =>
      by_cases stopped : (setup.executionProtocol admission).terminal state
      · rw [ExecutionProtocol.runFor_of_terminal _ _ stopped, FinDist.map_pure]
        exact (setup.continuationLaw_terminal
          (fun who => (profile who).toBehavioral setup.program) state stopped).symm
      · rw [ExecutionProtocol.runFor_succ_of_not_terminal _ _ stopped, FinDist.map_bind]
        change (setup.protocolStep state (setup.protocolJoint profile state)).bind _ = _
        calc
          _ = (setup.protocolStep state (setup.protocolJoint profile state)).bind
                (fun after => (setup.continuationLaw
                (fun who => (profile who).toBehavioral setup.program) after).map some) := by
            apply FinDist.bind_congr
            intro after reached
            have consumed := setup.protocol_remaining_step state after
              (setup.protocolJoint profile state) stopped reached
            exact ih after (by omega)
          _ = ((setup.protocolStep state (setup.protocolJoint profile state)).bind
              (setup.continuationLaw
                (fun who => (profile who).toBehavioral setup.program))).map some :=
            (FinDist.map_bind _ _ _).symm
          _ = _ := congrArg (fun law => law.map some)
            (setup.continuationLaw_step profile state stopped)

theorem protocol_historyChooser_eq (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (profile : ∀ who, PurePolicy who setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission) :
    (setup.informationModel admission).historyChooser
        (fun who => setup.toProtocolPolicy admission who (profile who) (permitted who)) =
      (setup.protocolChooser admission profile permitted).toHistoryChooser := by
  funext history running
  apply Subtype.ext
  funext who
  change (setup.toProtocolPolicy admission who (profile who) (permitted who)
      ((setup.protocolSignals admission).infoOf who history.trace)).1 =
    setup.protocolJoint profile history.state who
  rw [protocol_info]
  cases history.state <;> rfl

/-- Exact source continuation law at every history of the game with private
setup. In particular, a supplied prefix never triggers another setup draw. -/
theorem protocol_runFrom_eq (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (profile : ∀ who, PurePolicy who setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission) (fuel : Nat)
    (history : (setup.executionProtocol admission).History)
    (enough : setup.protocolRemaining history.state ≤ fuel) :
    ((setup.informationModel admission).runFrom
      (fun who => setup.toProtocolPolicy admission who (profile who) (permitted who))
      fuel history).map (fun final => setup.protocolReadout final.state) =
      (setup.continuationLaw
        (fun who => (profile who).toBehavioral setup.program) history.state).map some := by
  unfold InformationModel.runFrom
  rw [protocol_historyChooser_eq]
  calc
    _ = (((setup.executionProtocol admission).runHistoryFor
        (setup.protocolChooser admission profile permitted).toHistoryChooser fuel history).map
        ExecutionProtocol.History.state).map setup.protocolReadout := by
      rw [FinDist.map_comp]; rfl
    _ = _ := by
      rw [ExecutionProtocol.map_state_runHistoryFor]
      exact setup.protocol_runFor_eq admission profile permitted fuel history.state enough

theorem protocol_run_eq (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    (profile : ∀ who, PurePolicy who setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission) :
    ((setup.informationModel admission).run
      (fun who => setup.toProtocolPolicy admission who (profile who) (permitted who))
      (instructionCount setup.program + 1)).map (fun final => setup.protocolReadout final.state) =
      (setup.run (fun who => (profile who).toBehavioral setup.program)).map some := by
  exact setup.protocol_runFrom_eq admission profile permitted _ _ (Nat.le_refl _)

end Vegas.SourceProgram.Setup
