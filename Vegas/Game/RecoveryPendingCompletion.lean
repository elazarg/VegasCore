/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoverySuccessorBoundary

import Vegas.Game.RecoveryCountedService

/-! # Completion of pending native events from counted terminal completeness -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

section CountedCompletion

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

/-- Counted clear terminal completeness settles the current pending source
event at its next scheduler boundary under every whole behavioral profile. -/
theorem pending_stop_completed
    (terminalCompletes : ∀ (final : (application setup leaks).Control),
      ((menu).protocol (initialLaw setup) horizon scheduler).Trace (some final) →
      ExclusionEvidence 0 ∅ (⟨final.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      (application setup leaks).terminal (some final) →
      final.execution.application.config.cut.Terminal)
    (stopAtPublicFailure : Bool)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event) :
    ∀ final ∈ ((N).runBehavioralUntil certificate players
      (fun stop => if stopAtPublicFailure then
        LateStopped setup leaks bounds horizon scheduler rank stop ∨ ¬ Clear stop.state
        else LateStopped setup leaks bounds horizon scheduler rank stop) start).support,
      ∃ anchor : (application setup leaks).Execution,
        final.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ ∧
        event ∈ anchor.application.config.cut.completed ∧
        anchor.application.config.cut.IsPrefix (rank + 1) ∧
        ReadySeen setup leaks rank anchor := by
  classical
  let stopped : (E).History → Prop := fun stop => if stopAtPublicFailure then
    LateStopped setup leaks bounds horizon scheduler rank stop ∨ ¬ Clear stop.state
    else LateStopped setup leaks bounds horizon scheduler rank stop
  let property : (E).History → Prop := fun history =>
    ∃ next : (application setup leaks).Control, history.state = some next ∧
      ((PendingAt setup leaks rank next.execution ∧
        next.execution.application.config = control.execution.application.config ∧
        ExclusionEvidence 0 ∅ (RecoveryState.mk next.execution.application ∅)) ∨
        (next.actor = none ∧ next.execution.application.config.cut.IsPrefix (rank + 1) ∧
          ReadySeen setup leaks rank next.execution))
  have pending : PendingAt setup leaks rank control.execution := by
    obtain ⟨found, foundOrdered, seen⟩ := pendingAt_history
      ((menu).toRawTrace (initialLaw setup) horizon scheduler (current ▸ start.trace))
    have same := isPrefix_unique foundOrdered ordered
    subst same
    exact ⟨ordered, seen⟩
  have preserved : ∀ history, ¬ stopped history → ¬ (E).terminal history.state →
      property history → ∀ next ∈ ((N).runBehavioralFrom players 1 history).support,
        property next := by
    intro history going running ⟨before, state, cases⟩ after member
    rcases cases with ⟨pending, equal, beforeClear⟩ | completed
    · obtain ⟨joint, realized⟩ := onePacket_step_transition bounds players running member
      rw [state] at realized
      obtain ⟨next, nextState, nextCases⟩ := pendingTransition pending joint realized
      rcases nextCases with pendingNext | completed
      · have sameConfig : next.execution.application.config =
            before.execution.application.config := by
          rcases transition_configStep (initialLaw setup) horizon scheduler before next joint
              (nextState ▸ realized) with same | ⟨completed, completedReady, action, sampled⟩
          · exact same
          · have nextPrefix := isPrefix_succ_of_mem_step pending.1 completedReady sampled
            have := isPrefix_unique pendingNext.1 nextPrefix
            omega
        have physical := (reactiveApplication_completionStep (runtime setup) leaks).transition
          (initialLaw setup) horizon scheduler before next joint (nextState ▸ realized)
        exact ⟨next, nextState, Or.inl ⟨pendingNext, sameConfig.trans equal,
          beforeClear.completionStep_sameConfig physical sameConfig⟩⟩
      · exact ⟨next, nextState, Or.inr completed⟩
    · apply False.elim
      apply going
      cases stopAtPublicFailure
      · exact ⟨before, state, completed.2.1⟩
      · exact Or.inl ⟨before, state, completed.2.1⟩
  have remains := (N).runBehavioralUntil_support_history_closed certificate players stopped property
    preserved start ⟨control, current, Or.inl ⟨pending, rfl, clear⟩⟩
  intro final supported
  obtain ⟨next, state, cases⟩ := remains final supported
  have completed : next.actor = none ∧ next.execution.application.config.cut.IsPrefix (rank + 1) ∧
      ReadySeen setup leaks rank next.execution := by
    rcases cases with ⟨pendingNext, equal, nextClear⟩ | completed
    · have ends := (N).mem_support_runBehavioralUntil certificate players stopped start final
        supported
      have endCases : LateStopped setup leaks bounds horizon scheduler rank final ∨
          ¬ Clear final.state ∨ (E).terminal final.state := by
        cases stopAtPublicFailure
        · exact ends.elim Or.inl (fun ended => Or.inr (Or.inr ended))
        · exact ends.elim
            (fun halted => halted.elim Or.inl (fun failed => Or.inr (Or.inl failed)))
            (fun ended => Or.inr (Or.inr ended))
      rcases endCases with halted | failed | ended
      · obtain ⟨other, otherState, prefixed⟩ := halted
        rw [state, Option.some.injEq] at otherState
        subst otherState
        have := isPrefix_unique pendingNext.1 prefixed
        omega
      · exact (failed (by
          simpa only [state, ReactiveApplication.stateInvariant] using nextClear)).elim
      · rw [state] at ended
        have terminal := terminalCompletes next (state ▸ final.trace) nextClear ended
        have member : event ∈ next.execution.application.config.cut.completed := by
          rw [terminal]
          exact Finset.mem_univ _
        rw [equal] at member
        exact (ready.1 member).elim
    · exact completed
  rcases next with ⟨remaining, actor, anchor⟩
  obtain ⟨idle, prefixed, seen⟩ := completed
  change actor = none at idle
  subst idle
  have trace := (menu).toRawTrace (initialLaw setup) horizon scheduler (state ▸ final.trace)
  have accounted := (application setup leaks).raw_trace_horizon (initialLaw setup) horizon scheduler
    trace
  change anchor.environmentRecall.length + remaining = horizon at accounted
  refine ⟨anchor, ?_, ?_, prefixed, seen⟩
  · rw [state, show horizon - anchor.environmentRecall.length = remaining by omega]
  · exact (prefixed.2 event).mpr (by
      have := (ready_iff_rank setup _ rank ordered event).mp ready
      omega)

end CountedCompletion

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
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
/-- From a clear sequential prefix, the current event completes at the next
scheduler boundary under every actual bounded response profile. Before that
event completes, no event can change the configuration or create public failure. -/
theorem recovery_pending_stop_completed
    (stopAtPublicFailure : Bool)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event) :
    ∀ final ∈ ((N).runBehavioralUntil certificate players
      (fun stop => if stopAtPublicFailure then
        LateStopped setup leaks bounds horizon scheduler rank stop ∨ ¬ Clear stop.state
        else LateStopped setup leaks bounds horizon scheduler rank stop) start).support,
      ∃ anchor : (application setup leaks).Execution,
        final.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ ∧
        event ∈ anchor.application.config.cut.completed ∧
        anchor.application.config.cut.IsPrefix (rank + 1) ∧
        ReadySeen setup leaks rank anchor := by
  apply pending_stop_completed ?_ stopAtPublicFailure
    certificate players start current ordered clear event ready
  exact Recovery.CompletesPlay.clear_counted_native bounds initialized nativeLaw completes


end Vegas
