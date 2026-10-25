/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryPrescribedSourceKernel
import Vegas.Game.SourceFailureRecord
import Vegas.Pending.ExclusionAcceptedOutput
import Vegas.Game.AnchoredHonestLaw
import Vegas.Game.AnchoredOpeningClients
import Vegas.Game.IntendedOpeningContinuation

/-! # Genuine clear successor boundaries after honest source steps -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem native_sourceFailureRecord
    (profile : BehavioralProfile setup.program) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) : SourceFailureRecord profile control.execution.application.config := by
  let valid : (application setup leaks).ServiceInvariant scheduler
      (fun execution => SourceFailureRecord profile execution.application.config) :=
    { respond := fun execution who response holds => by
        rw [((runtime setup).reactive_respond_application leaks execution who response).1]
        exact holds
      environment := fun execution next command holds _chosen reached =>
        holds.step (environmentStep_configStep setup leaks execution next command reached) }
  exact valid.history (initialLaw setup) horizon (fun state supported => by
    obtain ⟨initial, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact SourceFailureRecord.initial setup profile initial) trace

/-- At a genuine native prefix, an intended source decoding rules out public
failure evidence. Hidden binding debt is handled through its actual stored
failure record, rather than through receipt flags alone. -/
theorem exclusionEvidence_of_decodedIntended {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    {point : ProtocolState setup.program}
    (decoded : decodedPoint setup control.execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) := by
  have binding := ((runtime setup).reactiveBindingInvariant leaks).history (initialLaw setup)
    horizon scheduler (fun state supported => by
      obtain ⟨inputs, _supported, rfl⟩ := PMF.support_map .. ▸ supported
      exact State.initial_bindingInvariant _) trace
  obtain ⟨rank, ⟨residual⟩, record⟩ :=
    native_sourceFailureRecord (failureProfile setup.program) horizon scheduler trace
  have decodedAt : sourceServicePrefix? setup rank control.execution.application.config =
      some point := (decodedPoint_eq_of_isPrefix residual.checkpoint.ordered).symm.trans decoded
  refine ⟨native_receiptsComplete_history (runtime setup) leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler trace,
    fun event lower => by omega, fun owner => ⟨?_, ?_⟩⟩
  · intro member
    exact (Finset.notMem_empty owner member).elim
  · rintro (inherited | ⟨event, _lower, acting, failed⟩)
    · exact inherited
    · have present := (control.execution.application.config.output_available event).mpr
        failed.completed
      obtain ⟨value, read⟩ := Option.isSome_iff_exists.mp present
      have stored : control.execution.application.config.store (.inr event) = some value := read
      have failing : StoreEventFailed control.execution.application.config.store event := by
        refine ⟨value, stored, ?_⟩
        by_contra good
        exact (OutputSucceeded.not_publicFailure ⟨value, stored, good⟩ binding) failed
      exact (ProtocolState.Intended.not_owesFailure owner setup.program point intended
        (record event failed.completed owner acting failing point decodedAt)).elim

section Successor

variable [Fintype Player] {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)

local notation "scheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

include initialized nativeLaw completes in
/-- A supported stopped endpoint with an intended source decoding is the next
clear scheduler boundary. The actual completion contract rules out exhaustion
while the current event remains pending. -/
theorem recovery_stopped_boundary_of_intended
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (final : (E).History)
    (supported : final ∈ ((N).runBehavioralUntil certificate players
      (fun stop => LateStopped setup leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) start).support)
    {point : ProtocolState setup.program}
    (decoded : nativeDecodedState setup leaks final.state = some point)
    (intended : ProtocolState.Intended setup.program point) :
    ∃ anchor : (application setup leaks).Execution,
      final.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ ∧
      ExclusionEvidence 0 ∅ (RecoveryState.mk anchor.application ∅) ∧
      event ∈ anchor.application.config.cut.completed ∧
      sourceServicePrefix? setup (rank + 1) anchor.application.config = some point ∧
      ReachedBoundary setup leaks horizon scheduler (rank + 1) anchor := by
  classical
  let stopped : (E).History → Prop := fun stop =>
    LateStopped setup leaks bounds horizon scheduler rank stop ∨ ¬ Clear stop.state
  let property : (E).History → Prop := fun history =>
    ∃ next : (application setup leaks).Control, history.state = some next ∧
      (PendingAt setup leaks rank next.execution ∨
        next.actor = none ∧ next.execution.application.config.cut.IsPrefix (rank + 1) ∧
          ReadySeen setup leaks rank next.execution)
  have initialPending : PendingAt setup leaks rank control.execution := by
    obtain ⟨found, foundOrdered, seen⟩ := pendingAt_history
      ((menu).toRawTrace (initialLaw setup) horizon scheduler (current ▸ start.trace))
    have same := isPrefix_unique foundOrdered ordered
    subst same
    exact ⟨ordered, seen⟩
  have preserved : ∀ history, ¬ stopped history → ¬ (E).terminal history.state →
      property history → ∀ next ∈ ((N).runBehavioralFrom players 1 history).support,
        property next := by
    intro history going running ⟨before, state, cases⟩ next member
    rcases cases with pending | finished
    · obtain ⟨joint, realized⟩ := onePacket_step_transition bounds players running member
      rw [state] at realized
      rcases before with ⟨remaining, actor, execution⟩
      exact pendingTransition pending joint realized
    · exact (going (Or.inl ⟨before, state, finished.2.1⟩)).elim
  obtain ⟨last, lastState, cases⟩ := (N).runBehavioralUntil_support_history_closed certificate
    players stopped property preserved start ⟨control, current, Or.inl initialPending⟩
    final supported
  have rawTrace := (menu).toRawTrace (initialLaw setup) horizon scheduler
    (lastState ▸ final.trace)
  have lastDecoded : decodedPoint setup last.execution.application.config = some point := by
    simpa only [lastState, nativeDecodedState] using decoded
  have clear := exclusionEvidence_of_decodedIntended rawTrace lastDecoded intended
  have finished : last.actor = none ∧
      last.execution.application.config.cut.IsPrefix (rank + 1) ∧
      ReadySeen setup leaks rank last.execution := by
    rcases cases with pending | finished
    · have ends := (N).mem_support_runBehavioralUntil certificate players stopped start final
        supported
      rcases ends with (halted | failure) | terminal
      · obtain ⟨other, otherState, nextPrefix⟩ := halted
        rw [lastState, Option.some.injEq] at otherState
        subst otherState
        have := isPrefix_unique pending.1 nextPrefix
        omega
      · exact (failure (by simpa only [lastState, ReactiveApplication.stateInvariant] using
          clear)).elim
      · rw [lastState] at terminal
        rw [← nativeLaw] at rawTrace
        have complete := Recovery.CompletesPlay.clear_native (runtime setup) leaks initialized
          completes last rawTrace clear terminal
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
  have accounted := (application setup leaks).raw_trace_horizon (initialLaw setup) horizon
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
    reachedBoundary_of_onePacket bounds final boundaryState (by omega) nextPrefix untouched point
      nextDecoded intended⟩
  exact (nextPrefix.2 event).mpr (by
    have := (ready_iff_rank setup _ rank ordered event).mp ready
    omega)

variable {delay bound : (graph setup).EventId → Nat}
  (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon recoveryScheduler delay)
  (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon recoveryScheduler
    bound)
  (timely : (runtime setup).AsyncTimely delay bound)

include initialized nativeLaw opportunity inclusion timely completes in
/-- Every supported honest first-callback completion is a genuine clear source
successor boundary, with the source behavioral successor and untouched later events. -/
theorem recovery_firstActivation_honest_successorBoundary
    [∀ player, DecidableEq ((N).InfoState player)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (history : (E).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk execution.application ∅))
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (info : (N).InfoState who) (observed : (N).infoOf who history.trace = info)
    (final : (E).History)
    (supported : final ∈ ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) players who
        ((players who).withLaw info
          (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler source who info)))
      (fun stop => LateStopped setup leaks bounds horizon scheduler rank stop ∨
        ¬ Clear stop.state) history).support) :
    ∃ (target : ProtocolState setup.program) (anchor : (application setup leaks).Execution),
      target ∈ (ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile source.strategy) point).support ∧
      ProtocolState.Intended setup.program target ∧
      final.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ ∧
      ExclusionEvidence 0 ∅ (RecoveryState.mk anchor.application ∅) ∧
      event ∈ anchor.application.config.cut.completed ∧
      sourceServicePrefix? setup (rank + 1) anchor.application.config = some target ∧
      ReachedBoundary setup leaks horizon scheduler (rank + 1) anchor := by
  classical
  have law := recovery_firstActivation_honest_sourceLaw initialized nativeLaw opportunity
    inclusion timely completes wellFormed covers capacity source certificate players history
    current clear event pending never ordered decoded intendedPoint info observed
  have decodedSupported : nativeDecodedState setup leaks final.state ∈
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
    (pendingEvent_spec pending).2.1
  obtain ⟨anchor, state, nextClear, completed, nextDecoded, reached⟩ :=
    recovery_stopped_boundary_of_intended initialized nativeLaw completes certificate _ history
      current ordered event ready final supported targetEq.symm targetIntended
  exact ⟨target, anchor, stepped, targetIntended, state, nextClear, completed, nextDecoded, reached⟩

end Successor

end Vegas
