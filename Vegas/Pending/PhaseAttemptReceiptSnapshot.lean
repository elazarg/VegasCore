/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseBindingAcceptedReceipt
import Vegas.Pending.PhaseStoppedAttemptMetadata
import Vegas.Pending.PhaseAttemptCompletion

/-! # The original completed physical snapshot at a full-attempt exit -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

namespace PhaseRuntimeState

/-- Leaving the installed namespace requires completing that original
phase before selecting any retry or exhausted restoration branch. -/
theorem finished_of_normalize_attempt_ne (state : PhaseRuntimeState graph)
    (phase : RuntimePhase graph) (installed : phase ∈ state.phases.head?)
    (closed : state.normalize.attempt ≠ state.attempt) :
    phase.Finished (phase.drain state.current) := by
  classical
  obtain ⟨remaining, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp installed)
  by_contra unfinished
  apply closed
  simp only [normalize, phases, settle, ite_eq_right unfinished, attempt, List.head?_cons,
    Option.map_some, Option.getD_some]

end PhaseRuntimeState

/-- The actual recorded environment reply identifies the primitive native
result before normalization. Packet lookup and handling, or the native
environment draw, remain literal even when normalization restores a checkpoint. -/
def PhaseClosingEffect (before after : (app).Execution) (current : RecoveryState graph) : Prop :=
  (∃ (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
      (native : State graph),
    before.network.lookup id = some message ∧
      after ∈ (before.environmentStep app (.include id)).support ∧
      handle runtime before.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      current = before.application.current.inclusionResult message.payload.packet.call native) ∨
  (∃ (command : EnvironmentCommand graph) (native : State graph),
    after ∈ (before.environmentStep app (.application command)).support ∧
      native ∈ (environmentStep runtime before.application.current.native command).support ∧
      current = before.application.current.environmentResult command native)

/-- Every actual namespace-changing transition has its original completed
physical snapshot before normalization. Its accepted bindings carry actual
old-attempt true receipts. The snapshot is retained separately from both
the post-reset live store and a possible exhausted restoration. -/
theorem phase_closed_transition_receipt_snapshot (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (before after : (app).Control)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some before)) (joint : Player → Option (app).Action)
    (reached : some after ∈ ((app).transition (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler (some before) joint).support)
    (phase : RuntimePhase graph) (installed : phase ∈ before.execution.application.phases.head?)
    (closed : after.execution.application.attempt ≠ before.execution.application.attempt) :
    ∃ current : RecoveryState graph, after.actor = none ∧
      after.execution.application =
        ({ before.execution.application with
          current := current } : PhaseRuntimeState graph).normalize ∧
      phase.Finished (phase.drain current) ∧
      (phase.drain current).native.BindingInvariant ∧ (phase.drain current).FailureCoverage ∧
      (phase.drain current).excluded = after.execution.application.current.excluded ∧
      (∀ event candidate, before.execution.application.attempt.phase ≤ event.val →
        (phase.drain current).native.accepted (.inr event) = some candidate →
        PhaseService.BindingAccepted runtime leaks
          ⟨before.execution.application.attempt, event⟩ candidate.1 after.execution) ∧
      PhaseClosingEffect runtime leaks before.execution after.execution current ∧
      BindingStamp (fun who => (app).outputs (before.execution.recall who))
        before.execution.application.attempt (phase.drain current).native := by
  classical
  have binding :=
    (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler trace).active
  have coverage :=
    (phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler trace).active
  have stamped := phaseLiveBindingStamp_history runtime leaks plan inputs horizon scheduler trace
  have finish (current : RecoveryState graph) (idle : after.actor = none)
      (normalized : after.execution.application =
        ({ before.execution.application with
          current := current } : PhaseRuntimeState graph).normalize)
      (nativeBinding : current.native.BindingInvariant) (covered : current.FailureCoverage)
      (receipts : ∀ event candidate, before.execution.application.attempt.phase ≤ event.val →
        current.native.accepted (.inr event) = some candidate →
          PhaseService.BindingAccepted runtime leaks
            ⟨before.execution.application.attempt, event⟩ candidate.1 after.execution)
      (effect : PhaseClosingEffect runtime leaks before.execution after.execution current)
      (rawStamp : BindingStamp
        (fun who => (app).outputs (before.execution.recall who))
        before.execution.application.attempt current.native) :
      ∃ current : RecoveryState graph, after.actor = none ∧
        after.execution.application =
          ({ before.execution.application with
            current := current } : PhaseRuntimeState graph).normalize ∧
        phase.Finished (phase.drain current) ∧
        (phase.drain current).native.BindingInvariant ∧ (phase.drain current).FailureCoverage ∧
        (phase.drain current).excluded = after.execution.application.current.excluded ∧
        (∀ event candidate, before.execution.application.attempt.phase ≤ event.val →
          (phase.drain current).native.accepted (.inr event) = some candidate →
          PhaseService.BindingAccepted runtime leaks
            ⟨before.execution.application.attempt, event⟩ candidate.1 after.execution) ∧
        PhaseClosingEffect runtime leaks before.execution after.execution current ∧
        BindingStamp (fun who => (app).outputs (before.execution.recall who))
          before.execution.application.attempt (phase.drain current).native := by
    have finished := PhaseRuntimeState.finished_of_normalize_attempt_ne
      ({ before.execution.application with current := current } : PhaseRuntimeState graph)
        phase installed (by
          simpa only [← normalized, PhaseRuntimeState.attempt] using closed)
    have physical : after.execution.application.current.excluded = current.excluded := by
      rw [normalized]
      exact (PhaseRuntimeState.settle_physical _ _ _ _ _).1
    refine ⟨current, idle, normalized, finished, phase.drain_bindingInvariant current nativeBinding,
      covered.drain phase, (phase.drain_excluded current).trans physical.symm, ?_, effect,
      rawStamp.copy (phase.drain_tables current).1⟩
    intro event candidate lower accepted
    apply receipts event candidate lower
    rwa [(phase.drain_tables current).1] at accepted
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some owner =>
    cases (PMF.mem_support_pure_iff ..).mp reached
    apply (closed _).elim
    cases response : ((joint owner).getD ⟨none⟩).transmission <;>
      simp [ReactiveApplication.Execution.respond, response, phaseApplication,
        PhaseRuntimeState.submit, PhaseRuntimeState.attempt]
  | none =>
    cases remaining with
    | zero =>
      cases (PMF.mem_support_pure_iff ..).mp reached
      exact (closed rfl).elim
    | succ remaining =>
      obtain ⟨command, _selected, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨next, stepped, equal⟩ := PMF.support_map .. ▸ moved
      cases Option.some.inj equal
      cases command with
      | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at stepped
        cases (PMF.mem_support_pure_iff ..).mp stepped
        exact (closed rfl).elim
      | activate owner =>
        obtain ⟨updated, selected, rfl⟩ := PMF.support_map .. ▸ stepped
        obtain ⟨sample, _supported, rfl⟩ := PMF.support_map .. ▸ selected
        exact (closed rfl).elim
      | «include» id =>
        have physicalStep := stepped
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at stepped
        cases (PMF.mem_support_pure_iff ..).mp stepped
        cases found : execution.network.lookup id with
        | none =>
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found] at closed
          exact (closed rfl).elim
        | some message =>
          cases handled : execution.application.handle runtime message with
          | none =>
            simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
              found, show (app).handle execution.application message = none from handled,
              Option.getD_none] at closed
            exact (closed rfl).elim
          | some state =>
            obtain ⟨native, nativeHandled, normalized, receipted, rawStamp⟩ :=
              phase_inclusion_snapshot_bindingAccepted runtime leaks plan inputs horizon scheduler
                trace id message found state handled
            refine finish (execution.application.current.inclusionResult
              message.payload.packet.call native) rfl ?_ ?_ ?_ ?_ ?_ ?_
            · simpa only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending,
                found, show (app).handle execution.application message = some state from handled,
                Option.getD_some] using normalized
            · exact handle_bindingInvariant runtime execution.application.current.native native
                ⟨message.id, message.payload.packet.call⟩ binding nativeHandled
            · exact coverage.inclusionResult runtime _ native nativeHandled
            · exact receipted
            · exact Or.inl ⟨id, message, native, found, physicalStep, nativeHandled, rfl⟩
            · exact rawStamp
      | application operation =>
        have physicalStep := stepped
        obtain ⟨updated, selected, rfl⟩ := PMF.support_map .. ▸ stepped
        obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ selected
        change state ∈ (execution.application.environment runtime operation).support at supported
        unfold PhaseRuntimeState.environment at supported
        split at supported
        · obtain ⟨native, nativeMoved, rfl⟩ := PMF.support_map .. ▸ supported
          refine finish (execution.application.current.environmentResult operation native)
            rfl rfl ?_ ?_ ?_ ?_ ?_
          · exact environmentStep_bindingInvariant runtime execution.application.current.native
              native operation binding nativeMoved
          · exact coverage.environmentResult runtime operation native nativeMoved
          · intro event candidate lower accepted
            have old :
                execution.application.current.native.accepted (.inr event) = some candidate :=
              by
                change native.accepted (.inr event) = some candidate at accepted
                rwa [(environmentStep_tables runtime _ _ operation nativeMoved).1] at accepted
            exact phase_live_bindingAccepted runtime leaks plan inputs horizon scheduler trace
              event lower candidate old
          · exact Or.inr ⟨operation, native, physicalStep, nativeMoved, rfl⟩
          · exact stamped.copy (environmentStep_tables runtime _ _ operation nativeMoved).1
        · cases (PMF.mem_support_pure_iff ..).mp supported
          exact (closed rfl).elim


section Stopped

variable [Fintype Player]

/-- The first actual full-attempt exit retains the original completed physical
snapshot and all of its accepting receipts, before retry or exhausted restore.
No exclusion or terminal branch is discarded. -/
theorem phase_attempt_stopped_receipt_snapshot
    (menu : (app).ResponseMenu) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (delay bound : graph.EventId → Nat)
    (contract : PhaseService.AsyncContract runtime leaks
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler delay bound)
    (profile : ∀ who, (menu.information (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).BehavioralPolicy who)
    (start : (app).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some start))
    (phase : RuntimePhase graph) (installed : phase ∈ start.execution.application.phases.head?) :
    let stopped := fun history : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
        horizon scheduler).History => match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ start.execution.application.attempt
    ∀ final ∈ ((menu.information (inputs.map (PhaseRuntimeState.initial plan))
        horizon scheduler).runBehavioralUntil
      (menu.bounded (inputs.map (PhaseRuntimeState.initial plan))
        horizon scheduler).wellFoundedHistories profile stopped ⟨some start, trace⟩).support,
      ∃ ending : (app).Control, final.state = some ending ∧
        ending.execution.application.attempt ≠ start.execution.application.attempt ∧
        ending.actor = none ∧ ∃ snapshot : RecoveryState graph,
          phase.Finished snapshot ∧ snapshot.native.BindingInvariant ∧ snapshot.FailureCoverage ∧
          snapshot.excluded = ending.execution.application.current.excluded ∧
          (∀ event candidate, start.execution.application.attempt.phase ≤ event.val →
            snapshot.native.accepted (.inr event) = some candidate →
            PhaseService.BindingAccepted runtime leaks
              ⟨start.execution.application.attempt, event⟩ candidate.1 ending.execution) ∧
          ∃ (before : (app).Control) (prior : (menu.protocol
              (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
            (joint : Player → Option (app).Action)
            (legal : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
              horizon scheduler).Legal (some before) joint)
            (realized : some ending ∈ ((app).transition
              (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
                (some before) joint).support) (raw : RecoveryState graph),
            TracePrefix trace prior ∧
              TracePrefix (prior.extend joint legal realized) final.trace ∧
              before.execution.application.attempt = start.execution.application.attempt ∧
              phase ∈ before.execution.application.phases.head? ∧ snapshot = phase.drain raw ∧
              ending.execution.application =
                ({ before.execution.application with current := raw } :
                  PhaseRuntimeState graph).normalize ∧
              PhaseClosingEffect runtime leaks before.execution ending.execution raw := by
  classical
  intro stopped final supported
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let E := menu.protocol initial horizon scheduler
  let N := menu.information initial horizon scheduler
  obtain ⟨ending, stateEq, retained, changed, _completed, _retried, _failed⟩ :=
    phase_attempt_stopped_results runtime leaks menu plan inputs horizon scheduler delay bound
      contract profile start trace phase installed final supported
  rcases final with ⟨target, finish⟩
  change target = some ending at stateEq
  cases stateEq
  have longer : trace.length < finish.length := by
    have lower : trace.length ≤ finish.length := retained.length_le
    by_contra notLonger
    have lengths : trace.length = finish.length := by omega
    have same := retained.eq_of_length lengths
    have states := congrArg (fun history : E.History => history.state) same
    have controls : start = ending := Option.some.inj states
    exact changed (congrArg (fun control : (app).Control =>
      control.execution.application.attempt) controls.symm)
  obtain ⟨beforeState, prior, joint, legal, moved, fromStart, endEq⟩ :=
    TracePrefix.exists_last_transition (E := E) (initialTrace := trace)
      (last := some ending) (finish := finish) (show TracePrefix trace finish from retained) longer
  change finish = prior.extend joint legal moved at endEq
  subst finish
  have beforeFinal : TracePrefix prior (prior.extend joint legal moved) :=
    .extend .refl joint legal moved
  have lastPrefix : TracePrefix (prior.extend joint legal moved)
      (prior.extend joint legal moved) := .refl
  have shorter : prior.length < (prior.extend joint legal moved).length :=
    Nat.lt_succ_self _
  obtain ⟨before, rfl, _ordered, same, phases, _entry⟩ :=
    phase_attempt_stopped_prefix_metadata runtime leaks menu plan inputs horizon scheduler
      profile start trace ⟨some ending, prior.extend joint legal moved⟩ supported
        fromStart beforeFinal shorter
  have installedNow : phase ∈ before.execution.application.phases.head? := by
    simpa only [phases] using installed
  obtain ⟨raw, idle, normalized, finished, binding, covered, excluded, receipts, effect,
      _rawStamp⟩ :=
    phase_closed_transition_receipt_snapshot runtime leaks plan inputs horizon scheduler
      before ending (menu.toRawTrace initial horizon scheduler prior) joint moved phase
        installedNow (fun equal => changed (equal.trans same))
  refine ⟨ending, rfl, changed, idle, phase.drain raw, finished, binding, covered, excluded, ?_,
    before, prior, joint, legal, moved, raw, fromStart, lastPrefix, same, installedNow, rfl,
    normalized, effect⟩
  simpa only [same] using receipts


end Stopped

end Vegas.EventGraphRuntime
