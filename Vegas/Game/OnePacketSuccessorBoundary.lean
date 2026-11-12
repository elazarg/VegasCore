module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketPrescribedSourceKernel
public import Vegas.Game.SourceServiceAsyncStep
public import Vegas.Pending.ReactiveCompletion
public import Vegas.Pending.ExclusionAcceptedOutput
public import Vegas.Game.OnePacketOwnSubmissions
public import Vegas.Game.SourceServiceCompletion
public import Vegas.Game.IntendedOpeningContinuation
public import Vegas.Game.SourceDebtObservation

@[expose] public section

/-! # Genuine clear successor boundaries after honest source steps -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- In the internally clear region a raw transition keeps the current prefix or
completes its one ready event, while retaining the prior bound on response views. -/
private theorem clear_transition_prefix {horizon rank : Nat}
    {scheduler : (application setup timeouts leaks).Scheduler}
    (before after : (application setup timeouts leaks).Control)
    (joint : Player → Option (application setup timeouts leaks).Action)
    (ordered : before.execution.application.config.cut.IsPrefix rank)
    (seen : ReadySeen setup leaks rank before.execution)
    (reached : some after ∈ ((application setup timeouts leaks).transition (initialLaw setup)
      horizon scheduler (some before) joint).support)
    (clear : after.execution.application.config.defaulted = ∅) :
    (after.execution.application.config = before.execution.application.config ∧
      ReadySeen setup leaks rank after.execution) ∨
    (after.actor = none ∧ after.execution.application.config.cut.IsPrefix (rank + 1) ∧
      ReadySeen setup leaks rank after.execution) := by
  let app := application setup timeouts leaks
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some owner =>
      cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
      refine Or.inl ⟨((reactive_respond_application timeouts) leaks execution owner _).1, ?_⟩
      intro observer entry member event readyView
      rcases app.respond_entry_origin execution owner observer ((joint owner).getD ⟨none⟩)
        entry member with old | ⟨same, fresh⟩
      · exact seen observer entry old event readyView
      · rw [fresh] at readyView
        change execution.application.publicView.EventReady event at readyView
        have ready := (execution.application.publicView_eventReady event).mp readyView
        have actual : execution.application.config.cut.IsPrefix event.val :=
          ⟨event.isLt.le, fun query =>
            setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready _ ready⟩
        exact (actual.unique ordered).le
  | none =>
      cases remaining with
      | zero =>
          cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
          exact Or.inl ⟨rfl, seen⟩
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ moved
          cases Option.some.inj same
          have unchangedRecall := app.environmentStep_recall execution next command supported
          have nextSeen : ReadySeen setup leaks rank next := by
            intro observer entry member event readyView
            rw [unchangedRecall] at member
            exact seen observer entry member event readyView
          rcases (reactive_environmentStep_config_eq_or_step timeouts) leaks execution next command
            supported clear with unchanged | ⟨event, ready, action, stepped⟩
          · exact Or.inl ⟨unchanged, nextSeen⟩
          · have idle : command.actor? app = none := by
              cases command with
              | activate owner =>
                  have sameConfig : next.application.config = execution.application.config := by
                    exact congrArg EventGraphRuntime.State.config
                      (activation_application setup leaks execution next owner supported)
                  exact (config_ne_of_step stepped sameConfig).elim
              | «include» _ => rfl
              | application _ => rfl
              | wait => rfl
            refine Or.inr ⟨idle, ?_, nextSeen⟩
            have actual : execution.application.config.cut.IsPrefix event.val :=
              ⟨event.isLt.le, fun query =>
                setup.eventGraph.sequentialize_mem_completed_iff_lt_of_ready _ ready⟩
            rw [execution.application.config.step_cut event ready action next.application.config
              stepped]
            exact ordered.complete_at event ready (actual.unique ordered)

section Successor

variable [Fintype Player] {bounds : MessageBounds (graph setup)}
  {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  (completes : ∀ control : (application setup timeouts leaks).Control,
    ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control) →
    control.execution.application.config.defaulted = ∅ →
    (application setup timeouts leaks).terminal (some control) →
    control.execution.application.config.cut.Terminal)

local notation "menu" => bounds.onePacketMenu timeouts leaks
local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup timeouts leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

include completes in
/-- A supported stopped endpoint with an intended source decoding is the next
clear scheduler boundary. The actual completion contract rules out exhaustion
while the current event remains pending. -/
theorem counted_stopped_boundary_of_intended
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup timeouts leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (final : (E).History)
    (supported : final ∈ ((N).runBehavioralUntil certificate players
      (fun stop => LateStopped setup timeouts leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) start).support)
    {point : ProtocolState setup.program}
    (decoded : nativeDecodedState setup timeouts leaks final.state = some point)
    (intended : ProtocolState.Intended setup.program point) :
    ∃ anchor : (application setup timeouts leaks).Execution,
      final.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ ∧
      anchor.application.config.defaulted = ∅ ∧
      event ∈ anchor.application.config.cut.completed ∧
      sourceServicePrefix? setup (rank + 1) anchor.application.config = some point ∧
      ReachedBoundary setup timeouts leaks horizon scheduler (rank + 1) anchor := by
  classical
  let stopped : (E).History → Prop := fun stop =>
    LateStopped setup timeouts leaks bounds horizon scheduler rank stop ∨ ¬ Clear stop.state
  let property : (E).History → Prop := fun history =>
    ∃ next : (application setup timeouts leaks).Control, history.state = some next ∧
      (next.execution.application.config.defaulted = ∅ →
        ((next.execution.application.config.cut.IsPrefix rank ∧
          ReadySeen setup leaks rank next.execution) ∨
        (next.actor = none ∧ next.execution.application.config.cut.IsPrefix (rank + 1) ∧
          ReadySeen setup leaks rank next.execution)))
  have atRank := (ready_iff_rank setup _ rank ordered event).mp ready
  have initialSeen : ReadySeen setup leaks rank control.execution :=
    readySeen_of_rawTrace timeouts leaks
      ((menu).toRawTrace (initialLaw setup) horizon scheduler (current ▸ start.trace)) ordered
  have preserved : ∀ history, ¬ stopped history → ¬ (E).terminal history.state →
      property history → ∀ next ∈ ((N).runBehavioralFrom players 1 history).support,
        property next := by
    intro history going running ⟨before, state, cases⟩ next member
    obtain ⟨⟨joint, _legal, realized⟩, _⟩ :=
      (N).mem_support_runBehavioralFrom_one players running member
    change next.state ∈ ((application setup timeouts leaks).transition (initialLaw setup) horizon
      scheduler history.state joint).support at realized
    rw [state] at realized
    obtain ⟨after, afterState, _recallPrefix⟩ :=
      (application setup timeouts leaks).transition_recall_prefix (initialLaw setup) horizon
        scheduler before next.state joint realized
    refine ⟨after, afterState, fun nextClear => ?_⟩
    have beforeClear := native_clear_before_transition timeouts leaks (initialLaw setup) horizon
      scheduler joint realized (by
        intro found foundState
        cases Option.some.inj (afterState.symm.trans foundState)
        exact nextClear) before rfl
    rcases cases beforeClear with ⟨beforeOrdered, beforeSeen⟩ | finished
    · rcases clear_transition_prefix (timeouts := timeouts) (leaks := leaks) before after joint
          beforeOrdered beforeSeen
          (by simpa only [afterState] using realized) nextClear with
        ⟨same, nextSeen⟩ | advanced
      · exact Or.inl ⟨by rw [same]; exact beforeOrdered, nextSeen⟩
      · exact Or.inr advanced
    · have completed : event ∈ before.execution.application.config.cut.completed :=
        (finished.2.1.2 event).mpr (by omega)
      exact (going (Or.inl ⟨before, state, event, completed, atRank⟩)).elim
  obtain ⟨last, lastState, cases⟩ := (N).runBehavioralUntil_support_history_closed certificate
    players stopped property preserved start
      ⟨control, current, fun _ => Or.inl ⟨ordered, initialSeen⟩⟩ final supported
  have rawTrace := (menu).toRawTrace (initialLaw setup) horizon scheduler
    (lastState ▸ final.trace)
  have lastDecoded : decodedPoint setup last.execution.application.config = some point := by
    simpa only [lastState, nativeDecodedState] using decoded
  have clear := defaulted_eq_empty_of_decodedIntended lastDecoded
    intended
  have finished : last.actor = none ∧
      last.execution.application.config.cut.IsPrefix (rank + 1) ∧
      ReadySeen setup leaks rank last.execution := by
    rcases cases clear with pending | finished
    · have ends := (N).mem_support_runBehavioralUntil certificate players stopped start final
        supported
      rcases ends with (halted | failure) | terminal
      · obtain ⟨other, otherState, query, completed, queryRank⟩ := halted
        rw [lastState, Option.some.injEq] at otherState
        subst otherState
        have := (pending.1.2 query).mp completed
        omega
      · exact (failure (by simpa only [lastState, ReactiveApplication.stateInvariant] using
          clear)).elim
      · rw [lastState] at terminal
        have complete := completes last (lastState ▸ final.trace) clear terminal
        have member : event ∈ last.execution.application.config.cut.completed := by
          rw [complete]
          exact Finset.mem_univ _
        have earlier := (pending.1.2 event).mp member
        have sameRank := (ready_iff_rank setup _ rank ordered event).mp ready
        omega
    · exact finished
  rcases last with ⟨remaining, actor, anchor⟩
  obtain ⟨idle, nextPrefix, seen⟩ := finished
  change actor = none at idle
  subst idle
  have accounted := (application setup timeouts leaks).raw_trace_horizon (initialLaw setup) horizon
    scheduler rawTrace
  change anchor.environmentRecall.length + remaining = horizon at accounted
  have boundaryState : final.state =
      some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ := by
    rw [lastState, show horizon - anchor.environmentRecall.length = remaining by omega]
  have nextDecoded : sourceServicePrefix? setup (rank + 1) anchor.application.config =
      some point := (decodedPoint_eq_of_isPrefix nextPrefix).symm.trans lastDecoded
  have untouched : ∀ later : (graph setup).EventId, rank + 1 ≤ later.val →
      Untouched setup leaks later anchor := fun later beyond observer entry member readyView => by
    have := seen observer entry member later readyView
    omega
  refine ⟨anchor, boundaryState, clear, ?_, nextDecoded,
    reachedBoundary_of_onePacket bounds final boundaryState (by omega)
      nextPrefix untouched point
      nextDecoded intended⟩
  exact (nextPrefix.2 event).mpr (by
    have := (ready_iff_rank setup _ rank ordered event).mp ready
    omega)

variable {delay bound : (graph setup).EventId → Nat}
  (opportunity : ∀ control : (application setup timeouts leaks).Control,
    ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control) →
    control.execution.application.config.defaulted = ∅ →
    OpportunityAt timeouts leaks control.execution delay)
  (inclusion : ∀ control : (application setup timeouts leaks).Control,
    ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control) →
    control.execution.application.config.defaulted = ∅ →
    ProtectedInclusionAt timeouts leaks control.execution bound)
  (timely : (AsyncTimely timeouts) delay bound)

include opportunity inclusion timely completes in
/-- Every supported honest first-callback completion is a genuine clear source
successor boundary, with the source behavioral successor and untouched later events. -/
theorem counted_firstActivation_honest_successorBoundary
    [∀ player, DecidableEq ((N).InfoState player)]
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (history : (E).History)
    {remaining : Nat} {who : Player} {execution : (application setup timeouts leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (clear : execution.application.config.defaulted = ∅)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup timeouts leaks who (some (execution.logs who,
      execution.observe (application setup timeouts leaks) who)) = some event)
    (never : ∀ entry ∈ execution.logs who, ¬ ActivatedAt setup timeouts leaks who event entry)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (info : (N).InfoState who) (observed : (N).infoOf who history.trace = info)
    (final : (E).History)
    (supported : final ∈ ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) players who
        ((players who).withLaw info
          (honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler source who
            info)))
      (fun stop => LateStopped setup timeouts leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) history).support) :
    ∃ (target : ProtocolState setup.program) (anchor : (application setup timeouts
      leaks).Execution),
      target ∈ (ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile source.strategy) point).support ∧
      ProtocolState.Intended setup.program target ∧
      final.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ ∧
      anchor.application.config.defaulted = ∅ ∧
      event ∈ anchor.application.config.cut.completed ∧
      sourceServicePrefix? setup (rank + 1) anchor.application.config = some target ∧
      ReachedBoundary setup timeouts leaks horizon scheduler (rank + 1) anchor := by
  classical
  have law := counted_firstActivation_honest_sourceLaw (timeouts := timeouts) opportunity
    inclusion timely completes covers capacity source certificate players history
    current clear event pending never ordered decoded intendedPoint info observed
  have decodedSupported : nativeDecodedState setup timeouts leaks final.state ∈
      ((ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile source.strategy) point).map some).support := by
    rw [← law, PMF.mem_support_map_iff]
    exact ⟨final, supported, rfl⟩
  rw [PMF.mem_support_map_iff] at decodedSupported
  obtain ⟨target, stepped, targetEq⟩ := decodedSupported
  have targetIntended := (setup.intendedOpening_step_closed source.strategy point target
    (decodedPoint_staticAt ((decodedPoint_eq_of_isPrefix ordered).trans decoded))
    intendedPoint stepped).2
  have ready := (execution.application.publicView_eventReady event).mp
    (pendingEvent_spec (timeouts := timeouts) pending).2.1
  obtain ⟨anchor, state, nextClear, completed, nextDecoded, reached⟩ :=
    counted_stopped_boundary_of_intended (timeouts := timeouts) completes certificate _ history
      current ordered event ready final supported targetEq.symm targetIntended
  exact ⟨target, anchor, stepped, targetIntended, state, nextClear, completed, nextDecoded, reached⟩

end Successor

end Vegas
