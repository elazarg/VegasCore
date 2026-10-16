/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseExclusionRecord
import Vegas.Pending.EventValueSwap
import Vegas.Pending.PhaseRetryCompletion
import Interaction.ReactiveRecall
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryAtom

/-! # Genuine owner expiry inside an installed commitment attempt -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Any packet accepted while a commitment block is installed preserves every
owner's exclusion status, including after automatic phase settlement. -/
theorem handle_commitment_phase_excluded (runtime : EventGraphRuntime graph)
    (state next : PhaseRuntimeState graph) (phase : RuntimePhase graph)
    (installed : phase ∈ state.phases.head?) (commitment : phase.kind = .commitment)
    (message : Message Player (CommitAttemptPacket graph))
    (accepted : state.handle runtime message = some next) :
    next.current.excluded = state.current.excluded := by
  classical
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · rename_i permitted
    obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
    have allowed := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp permitted).1).2
    change (settle state.phases state.generation state.entry
      (state.current.inclusionResult message.payload.packet.call native)
      state.retired).current.excluded = state.current.excluded
    rw [(settle_physical _ _ _ _ _).1]
    cases call : message.payload.packet.call with
    | commitment event candidate => rfl
    | malformed raw =>
        simp only [call, EventGraphRuntime.handle] at handled
        cases handled
    | opening event candidate raw =>
        obtain ⟨actualPhase, actualInstalled, actualEvent, named, inside⟩ :=
          state.allows_event message.payload.packet.call allowed
        have phaseEq : actualPhase = phase := by
          exact Option.some.inj ((Option.mem_def.mp actualInstalled).symm.trans
            (Option.mem_def.mp installed))
        have eventEq : actualEvent = event := by
          exact Option.some.inj (by simpa only [call, Payload.event?] using named.symm)
        subst actualPhase
        subst actualEvent
        obtain ⟨owner, payload, binding⟩ := commitment ▸ phase.fields event
          ((phase.mem_events event).mp inside).1 ((phase.mem_events event).mp inside).2
        obtain ⟨_ready, _timely, _owner, _payload, _binding, _checks, output, _rest⟩ :=
          handle_opening_conditions runtime state.current.native native message.id event
            candidate raw (call ▸ handled)
        rw [binding] at output
        cases output
  · cases accepted

/-- A newly excluded owner under a physical environment command was the actor
of a genuinely ready expiry in this installed block. The original native draw
and pre-normalization completion witness are retained across rollback. -/
theorem environment_new_exclusion_request (runtime : EventGraphRuntime graph)
    (state next : PhaseRuntimeState graph) (phase : RuntimePhase graph)
    (installed : phase ∈ state.phases.head?) (command : EnvironmentCommand graph)
    (reached : next ∈ (state.environment runtime command).support)
    (owner : Player) (active : owner ∉ state.current.excluded)
    (excluded : owner ∈ next.current.excluded) :
    ∃ (event : graph.EventId) (native : State graph),
      command = .expire event ∧ event ∈ phase.events ∧
      state.SeedRequest owner ⟨state.attempt, event⟩ ∧
      native ∈ (environmentStep runtime state.current.native (.expire event)).support ∧
      event ∈ native.config.cut.completed ∧
      next = ({ state with current := state.current.environmentResult (.expire event) native } :
        PhaseRuntimeState graph).normalize := by
  classical
  unfold PhaseRuntimeState.environment at reached
  split at reached
  · rename_i permitted
    obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ reached
    change owner ∈ (settle state.phases state.generation state.entry
      (state.current.environmentResult command native) state.retired).current.excluded at excluded
    rw [(settle_physical _ _ _ _ _).1] at excluded
    cases command with
    | advanceClock => exact (active excluded).elim
    | executeSample event => exact (active excluded).elim
    | expire event =>
        change owner ∈ (if event ∉ state.current.native.config.cut.completed ∧
            event ∈ native.config.cut.completed then
          RecoveryState.excludeEvent state.current.excluded event else state.current.excluded)
          at excluded
        split at excluded
        · rename_i changed
          obtain ⟨_clock, effect⟩ := environmentStep_expire_config_activated runtime
            state.current.native native event moved
          rcases effect with ⟨sameConfig, _sameActivated⟩ | ⟨ready, _action, _step, _activated⟩
          · exact (changed.1 (sameConfig ▸ changed.2)).elim
          · have acting : graph.actor? event = some owner := by
              unfold RecoveryState.excludeEvent at excluded
              cases actor : graph.actor? event with
              | none =>
                  simp only [actor] at excluded
                  exact (active excluded).elim
              | some who =>
                  simp only [actor] at excluded
                  rcases Finset.mem_insert.mp excluded with same | old
                  · exact congrArg some same.symm
                  · exact (active old).elim
            have head : state.phases.head? = some phase := Option.mem_def.mp installed
            have inside : event ∈ phase.events := by
              simpa only [commandAllowed, head, Option.any_some, decide_eq_true_eq] using permitted
            exact ⟨event, native, rfl, inside, ⟨rfl, ⟨phase, installed, inside⟩, ready, acting,
              active⟩, moved, changed.2, rfl⟩
        · exact (active excluded).elim
  · cases (PMF.mem_support_pure_iff _ _).mp reached
    exact (active excluded).elim

end PhaseRuntimeState

/-- A commitment attempt can newly exclude an owner only at a genuine ready
request of that owner. Packet inclusion, preparation and bookkeeping cannot
create such an exclusion, even when another owner was already excluded. -/
theorem phaseApplication_commitment_exclusionRequest (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation (fun before after =>
      ∀ phase ∈ before.phases.head?, phase.kind = .commitment → ∀ owner,
        owner ∉ before.current.excluded → owner ∈ after.current.excluded →
          ∃ event ∈ phase.events, before.SeedRequest owner ⟨before.attempt, event⟩) where
  refl _ _ _ _ _ active excluded := (active excluded).elim
  submit _ _ _ _ _ _ _ active excluded := (active excluded).elim
  handle before message after accepted phase installed kind owner active excluded := by
    have same := PhaseRuntimeState.handle_commitment_phase_excluded runtime before after phase
      installed kind message accepted
    exact (active (same ▸ excluded)).elim
  environment before command after reached phase installed _kind owner active excluded := by
    obtain ⟨event, _native, _command, inside, request, _step, _completed, _normalized⟩ :=
      PhaseRuntimeState.environment_new_exclusion_request runtime before after phase installed
        command reached owner active excluded
    exact ⟨event, inside, request⟩

section Stopped

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable [Fintype Player]
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "E" => menu.protocol initial horizon scheduler
local notation "N" => menu.information initial horizon scheduler

/-- On the existing runner stopped at the first exit of an original attempt,
every newly excluded owner has an actual first exclusion transition at one
of its ready requests in that same block. Earlier exclusions of other owners
are retained, and no global clearance or delivery premise is needed. -/
theorem phase_attempt_stopped_exclusion_origin
    (profile : ∀ who, (N).BehavioralPolicy who)
    (start : (app).Control) (trace : (E).Trace (some start))
    (phase : RuntimePhase graph) (installed : phase ∈ start.execution.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (owner : Player) (active : owner ∉ start.execution.application.current.excluded) :
    let stopped := fun history : (E).History => match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ start.execution.application.attempt
    ∀ final ∈ ((N).runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
        ⟨some start, trace⟩).support,
      ∀ ending, final.state = some ending → owner ∈ ending.execution.application.current.excluded →
        ∃ (before after : (app).Control) (prior : (E).Trace (some before))
          (joint : Player → Option (app).Action) (legal : (E).Legal (some before) joint)
          (realized : some after ∈ ((app).transition initial horizon scheduler
            (some before) joint).support) (event : graph.EventId),
          TracePrefix trace prior ∧ TracePrefix (prior.extend joint legal realized) final.trace ∧
          before.execution.application.attempt = start.execution.application.attempt ∧
          phase ∈ before.execution.application.phases.head? ∧
          owner ∉ before.execution.application.current.excluded ∧
          owner ∈ after.execution.application.current.excluded ∧ event ∈ phase.events ∧
          before.execution.application.SeedRequest owner
            ⟨start.execution.application.attempt, event⟩ := by
  classical
  intro stopped final supported ending finalState excluded
  let Witness : {target : (app).ProtocolState} → (E).Trace target → Prop :=
    fun {_target} targetTrace =>
      ∃ (before after : (app).Control) (prior : (E).Trace (some before))
        (joint : Player → Option (app).Action) (legal : (E).Legal (some before) joint)
        (realized : some after ∈ ((app).transition initial horizon scheduler
          (some before) joint).support) (event : graph.EventId),
        TracePrefix trace prior ∧ TracePrefix (prior.extend joint legal realized) targetTrace ∧
        before.execution.application.attempt = start.execution.application.attempt ∧
        phase ∈ before.execution.application.phases.head? ∧
        owner ∉ before.execution.application.current.excluded ∧
        owner ∈ after.execution.application.current.excluded ∧ event ∈ phase.events ∧
        before.execution.application.SeedRequest owner
          ⟨start.execution.application.attempt, event⟩
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered plan draw
  have startOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized ((menu).toRawTrace initial horizon scheduler trace)
  have first := (N).runBehavioralUntil_support_first
    ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
      ⟨some start, trace⟩ final supported
  have along : ∀ {target} {targetTrace : (E).Trace target}, TracePrefix trace targetTrace →
      TracePrefix targetTrace final.trace →
        ∃ current : (app).Control, target = some current ∧ current.execution.application.Ordered ∧
          (current.execution.application.attempt = start.execution.application.attempt →
            current.execution.application.phases = start.execution.application.phases) ∧
          (owner ∈ current.execution.application.current.excluded → Witness targetTrace) := by
    intro target targetTrace kept
    induction kept with
    | refl =>
      intro _before
      exact ⟨start, rfl, startOrdered, fun _ => rfl, fun failed => (active failed).elim⟩
    | @extend source target earlier kept joint legal realized ih =>
      intro beforeFinal
      have earlierFinal := (TracePrefix.extend .refl joint legal realized).trans beforeFinal
      obtain ⟨middle, rfl, middleOrdered, phasesKept, previous⟩ := ih earlierFinal
      have moved : target ∈ ((app).transition initial horizon scheduler
          (some middle) joint).support := realized
      obtain ⟨next, rfl, _recall⟩ := (app).transition_recall_prefix initial horizon scheduler
        middle target joint moved
      have shorter : earlier.length < final.trace.length := by
        have upper := beforeFinal.length_le
        simp only [Trace.length] at upper
        omega
      have same : middle.execution.application.attempt = start.execution.application.attempt := by
        by_contra different
        exact first ⟨some middle, earlier⟩ kept earlierFinal shorter different
      have nextOrdered := (phaseApplication_seedOrder runtime leaks).transition initial horizon
        scheduler initialized (some middle) (some next) joint middleOrdered moved
      refine ⟨next, rfl, nextOrdered, ?_, ?_⟩
      · intro sameNext
        exact ((phaseApplication_sameAttempt_phases runtime leaks).transition initial horizon
          scheduler middle next joint moved middleOrdered (same.trans sameNext.symm)).trans
            (phasesKept same)
      · intro newExcluded
        by_cases old : owner ∈ middle.execution.application.current.excluded
        · obtain ⟨before, after, prior, actions, allowed, actual, event, fromStart, toMiddle,
            atAttempt, phaseInstalled, wasActive, nowExcluded, inside, request⟩ := previous old
          exact ⟨before, after, prior, actions, allowed, actual, event, fromStart,
            TracePrefix.extend toMiddle joint legal realized, atAttempt, phaseInstalled, wasActive,
            nowExcluded, inside, request⟩
        · have installedNow : phase ∈ middle.execution.application.phases.head? := by
            simpa only [phasesKept same] using installed
          obtain ⟨event, inside, request⟩ :=
            (phaseApplication_commitment_exclusionRequest runtime leaks).transition initial horizon
              scheduler middle next joint moved phase installedNow commitment owner old newExcluded
          exact ⟨middle, next, earlier, joint, legal, moved, event, kept, .refl, same,
            installedNow, old, newExcluded, inside, by simpa only [same] using request⟩
  have retained := (N).runBehavioralUntil_support_prefix
    ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
      ⟨some start, trace⟩ final supported
  obtain ⟨current, stateEq, _ordered, _phases, witness⟩ := along retained .refl
  have same := Option.some.inj (stateEq.symm.trans finalState)
  cases same
  exact witness excluded

end Stopped

end Vegas.EventGraphRuntime
