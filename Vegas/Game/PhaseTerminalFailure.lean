/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompiledRevealReadback
import Vegas.Compile.CompiledRevealOrigins
import Vegas.Compile.EventGraphParameterReadout
import Vegas.Pending.PhaseFailureCoverage
import Vegas.Game.PhaseExclusionPayoff
import Vegas.Game.PhaseRecoveryInformation
import Vegas.Game.RecoveryExclusionPayoff
import Vegas.Game.RevealServiceRosterContinuation

/-! # Failed terminal source publications have physically excluded owners

Every reveal cell in the actual terminal decoder names its compiled publication
event. Surviving phase failure coverage therefore forces the owner of a failed
terminal source reveal into the real permanent exclusion set. The phase payoff
uses its existing utility without any additional failure valuation.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A failed source terminal reveal is an actual failed owned native publication;
failure coverage forces permanent exclusion, independently of utility. -/
theorem phase_terminal_failedReveal_excluded
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (state : PhaseRuntimeState (serviceGraph setup mode))
    (coverage : state.FailureCoverage)
    (terminal : State L setup.program.terminalCtx)
    (decoded : decodeState? (terminalRefs setup.program) state.current.native.config.store =
      some terminal) (who : Player)
    (failed : 0 < failedReveals setup.program who (publicOutcome setup.program terminal)) :
    who ∈ state.current.excluded := by
  obtain ⟨cell, selected⟩ := List.exists_mem_of_ne_nil _ (List.length_pos_iff.mp failed)
  obtain ⟨member, selected⟩ := List.mem_filter.mp selected
  obtain ⟨owned, failure⟩ := Bool.and_eq_true_iff.mp selected
  have owner : cell.owner = who := of_decide_eq_true owned
  have failedCell : terminal.get cell.cell = .failure := by
    cases result : terminal.get cell.cell with
    | failure => rfl
    | success value =>
        rw [RevealCell.failed_publicOutcome_of_success setup.program cell terminal result]
          at failure
        cases failure
  obtain ⟨index, sourceOutput, actor, field⟩ := terminalRefsWith_revealCell_output setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
    cell member
  let event : (serviceGraph setup mode).EventId := index
  have outputEq : (serviceGraph setup mode).outputLayout event = .publication cell.payload :=
    sourceOutput
  have acting : (serviceGraph setup mode).actor? event = some who := by
    have native : (toEventGraph setup.program).actor? event = some who := by
      simpa only [event, eventOwner?_eq_actor, owner] using actor
    cases mode <;> exact native
  have same : (terminalRefs setup.program).get cell.cell =
      (⟨.inr event, outputEq⟩ : FieldRef (serviceGraph setup mode).layout
        (.publication cell.payload)) := by
    cases selected : (terminalRefs setup.program).get cell.cell with
    | mk selectedField selectedLayout =>
        change ((terminalRefs setup.program).get cell.cell).field = .inr event at field
        rw [selected] at field
        cases field
        rfl
  have read := decodeState?_agrees (terminalRefs setup.program) _ terminal decoded cell.cell
  rw [same, failedCell] at read
  have publicFailure : state.current.native.PublicFailure event := by
    cases viewed : nodeView (serviceGraph setup mode) event with
    | bind owner payload kind code => cases kind.symm.trans outputEq
    | sample payload distribution kind code => cases kind.symm.trans outputEq
    | resolve owner payload binding checks kind code =>
        have aligned : payload = cell.payload := by
          have eq := kind.symm.trans outputEq
          cases eq
          rfl
        subst payload
        exact (publication_failure_iff_read state.current.native event binding checks outputEq
          code .failure read).mpr rfl
  exact coverage.active.covered event who acting publicFailure

/-- The failed owner is excluded on every actual initialized raw phase history;
the input law, scheduler, observation rule and phase plan are unrestricted. -/
theorem phase_terminal_failedReveal_excluded_history
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (terminal : State L setup.program.terminalCtx)
    (decoded : decodeState? (terminalRefs setup.program)
      control.execution.application.current.native.config.store = some terminal) (who : Player)
    (failed : 0 < failedReveals setup.program who (publicOutcome setup.program terminal)) :
    who ∈ control.execution.application.current.excluded :=
  phase_terminal_failedReveal_excluded setup mode _
    (phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler trace)
    terminal decoded who failed

/-- On states with genuine physical failure coverage, the unchanged phase
utility is exactly the original recovery utility of the projected current state.
The initial private parameter and the ordinary terminal valuation are retained. -/
theorem phaseExclusionBase_eq_recoveryExclusionBase
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (graph setup)))
    (recoveryLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (control : (phaseApplication runtime leaks).Control)
    (coverage : control.execution.application.FailureCoverage) (who : Player) :
    phaseExclusionBase setup .sequential runtime leaks
        (fun terminal => utility (setup.parameterOutcome parameter terminal)) excludedPayoff
        (some control) who =
      recoveryExclusionBase (runtime := runtime) parameter utility excludedPayoff
        (some (PhaseRecoveryProjection.control runtime leaks recoveryLeaks control))
        who := by
  by_cases excluded : who ∈ control.execution.application.current.excluded
  · exact (phaseExclusionBase_of_excluded setup .sequential runtime leaks _ excludedPayoff
      control who excluded).trans
        (recoveryExclusionBase_of_excluded (runtime := runtime) parameter utility
          excludedPayoff _ who excluded).symm
  rw [recoveryExclusionBase_of_not_excluded (runtime := runtime) parameter utility
    excludedPayoff _ who excluded,
    exclusionBase_eq_readout, sourceReadout, serviceSourceReadout_eq_decode]
  simp only [phaseExclusionBase, excluded, ↓reduceIte]
  change (if control.execution.application.current.native.config.cut.Terminal then
      decodeState? (terminalRefs setup.program)
        control.execution.application.current.native.config.store else none).elim 0
      (fun terminal => utility (setup.parameterOutcome parameter terminal) who) =
    exclusionReadoutUtility setup parameter utility excludedPayoff
      (decodeState? (terminalRefs setup.program)
        control.execution.application.current.native.config.store) who
  cases decoded : decodeState? (terminalRefs setup.program)
      control.execution.application.current.native.config.store with
  | none => simp only [ite_self, Option.elim_none, exclusionReadoutUtility]
  | some terminal =>
      have complete := terminal_decode_complete setup.program .sequential
        control.execution.application.current.native.config (by rw [decoded]; rfl)
      have noFailure : failedReveals setup.program who (publicOutcome setup.program terminal) =
          0 := Nat.eq_zero_of_not_pos fun positive =>
        excluded (phase_terminal_failedReveal_excluded setup .sequential _ coverage terminal
          decoded who positive)
      rw [ite_eq_left complete]
      simp only [Option.elim_some, exclusionReadoutUtility]
      exact (exclusionTerminalUtility_of_not_failed setup parameter utility excludedPayoff
        noFailure).symm

end Vegas
