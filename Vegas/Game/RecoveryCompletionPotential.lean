/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryEventPhaseLaw
import Vegas.Game.OnePacketLateBadMass

/-! # Completion potentials for actual current-event phases -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (recoveryApplication runtime leaks).Scheduler}
  (completes : Recovery.CompletesPlay runtime leaks initial horizon recoveryScheduler)

local notation "scheduler" => RecoveryProjection.nativeScheduler runtime leaks
  recoveryScheduler
local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))

omit initialized nativeLaw completes in
/-- The physical completion value is exactly the optional source-point
potential on the protected current-event phase, including every failure fallback. -/
theorem pending_completionValue_eq_potential
    (terminalCompletes : ∀ (final : (application setup runtime leaks).Control),
      ((menu).protocol (initialLaw setup) horizon scheduler).Trace (some final) →
      ExclusionEvidence 0 ∅ (⟨final.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      (application setup runtime leaks).terminal (some final) →
      final.execution.application.config.cut.Terminal)
    (certificate : (E).WellFoundedHistories) (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (profile : BehavioralProfile setup.program)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player)
    (fresh : (application setup runtime leaks).Control → Prop) (fallback : (E).History → ℝ) :
    let phase := (N).runBehavioralUntil certificate players (fun final =>
      LateStopped setup runtime leaks bounds horizon scheduler rank final ∨ ¬ Clear final.state)
        start
    expect phase (completionValue setup runtime leaks bounds horizon scheduler parameter utility
        excludedPayoff profile rank fresh who fallback) =
      expect phase (fun final =>
        (completionPoint setup runtime leaks bounds horizon scheduler rank fresh final).elim
          (fallback final) (sourcePointValue setup parameter utility excludedPayoff profile who)) :=
    by
  intro phase
  apply expect_congr_on_support
  intro final member
  obtain ⟨anchor, state, _completed, nextPrefix, _seen⟩ :=
    pending_stop_completed (runtime := runtime) terminalCompletes true certificate players start
      current ordered clear
      event ready
    final member
  exact completionValue_eq_elim setup runtime leaks bounds horizon scheduler parameter utility
    excludedPayoff profile rank fresh who fallback ⟨_, state, nextPrefix⟩

include initialized nativeLaw completes in
/-- The physical completion value is exactly the optional source-point
potential on the protected current-event phase, including every failure fallback. -/
theorem recovery_pending_completionValue_eq_potential
    (certificate : (E).WellFoundedHistories) (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (profile : BehavioralProfile setup.program)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player)
    (fresh : (application setup runtime leaks).Control → Prop) (fallback : (E).History → ℝ) :
    let phase := (N).runBehavioralUntil certificate players (fun final =>
      LateStopped setup runtime leaks bounds horizon scheduler rank final ∨ ¬ Clear final.state)
        start
    expect phase (completionValue setup runtime leaks bounds horizon scheduler parameter utility
        excludedPayoff profile rank fresh who fallback) =
      expect phase (fun final =>
        (completionPoint setup runtime leaks bounds horizon scheduler rank fresh final).elim
          (fallback final) (sourcePointValue setup parameter utility excludedPayoff profile who)) :=
    by
  exact pending_completionValue_eq_potential (runtime := runtime)
    (Recovery.CompletesPlay.clear_counted_native (runtime := runtime) bounds initialized nativeLaw
      completes)
    certificate players start current ordered clear event ready
    profile parameter utility excludedPayoff who fresh fallback

omit initialized nativeLaw completes in
open Classical in
/-- The exceptional mass in the continuation estimate is exactly the physical
successful-completion mass without an intended completion point. -/
theorem pending_badMass_eq_lateBadStop
    (terminalCompletes : ∀ (final : (application setup runtime leaks).Control),
      ((menu).protocol (initialLaw setup) horizon scheduler).Trace (some final) →
      ExclusionEvidence 0 ∅ (⟨final.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      (application setup runtime leaks).terminal (some final) →
      final.execution.application.config.cut.Terminal)
    (certificate : (E).WellFoundedHistories) (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (key : LateKey setup runtime leaks) (decided : decidedEvent (runtime := runtime) key = some
      event)
    (fresh : (application setup runtime leaks).Control → Prop) :
    let phase := (N).runBehavioralUntil certificate players (fun final =>
      LateStopped setup runtime leaks bounds horizon scheduler rank final ∨ ¬ Clear final.state)
        start
    (phase.toOuterMeasure {final |
      completionPoint setup runtime leaks bounds horizon scheduler rank fresh final = none ∧
        ¬ DecisionFailed (runtime := runtime) key final.state}).toReal =
      expect phase (lateBadStop setup runtime leaks bounds horizon scheduler rank fresh event) := by
  intro phase
  rw [← expect_indicator]
  apply expect_congr_on_support
  intro final member
  obtain ⟨anchor, state, completed, _nextPrefix, _seen⟩ :=
    pending_stop_completed (runtime := runtime) terminalCompletes true certificate players start
      current ordered clear
      event ready
    final member
  have failed : DecisionFailed (runtime := runtime) key final.state ↔
      StoreEventFailed anchor.application.config.store event := by
    simp only [state, DecisionFailed, decided, completed, true_and]
  have successful : (∃ next : (application setup runtime leaks).Control,
      final.state = some next ∧ event ∈ next.execution.application.config.cut.completed ∧
        ¬ StoreEventFailed next.execution.application.config.store event) ↔
      ¬ DecisionFailed (runtime := runtime) key final.state := by
    rw [failed]
    constructor
    · rintro ⟨next, same, _completed, works⟩
      rw [state, Option.some.injEq] at same
      cases same
      exact works
    · intro works
      exact ⟨_, state, completed, works⟩
  unfold lateBadStop
  simp only [Set.mem_ofPred_eq]
  have equivalence :
      (completionPoint setup runtime leaks bounds horizon scheduler rank fresh final = none ∧
        ¬ DecisionFailed (runtime := runtime) key final.state) ↔
      (∃ next : (application setup runtime leaks).Control,
        final.state = some next ∧ event ∈ next.execution.application.config.cut.completed ∧
          ¬ StoreEventFailed next.execution.application.config.store event) ∧
        completionPoint setup runtime leaks bounds horizon scheduler rank fresh final = none :=
    ⟨fun holds => ⟨successful.mpr holds.2, holds.1⟩,
      fun holds => ⟨holds.2, successful.mp holds.1⟩⟩
  by_cases first : completionPoint setup runtime leaks bounds horizon scheduler rank fresh final =
    none ∧
      ¬ DecisionFailed (runtime := runtime) key final.state
  · rw [ite_eq_left first, ite_eq_left (equivalence.mp first)]
  · rw [ite_eq_right first, ite_eq_right (fun second => first (equivalence.mpr second))]

include initialized nativeLaw completes in
open Classical in
/-- The exceptional mass in the continuation estimate is exactly the physical
successful-completion mass without an intended completion point. -/
theorem recovery_pending_badMass_eq_lateBadStop
    (certificate : (E).WellFoundedHistories) (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅))
    (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (key : LateKey setup runtime leaks) (decided : decidedEvent (runtime := runtime) key = some
      event)
    (fresh : (application setup runtime leaks).Control → Prop) :
    let phase := (N).runBehavioralUntil certificate players (fun final =>
      LateStopped setup runtime leaks bounds horizon scheduler rank final ∨ ¬ Clear final.state)
        start
    (phase.toOuterMeasure {final |
      completionPoint setup runtime leaks bounds horizon scheduler rank fresh final = none ∧
        ¬ DecisionFailed (runtime := runtime) key final.state}).toReal =
      expect phase (lateBadStop setup runtime leaks bounds horizon scheduler rank fresh event) := by
  exact pending_badMass_eq_lateBadStop (runtime := runtime)
    (Recovery.CompletesPlay.clear_counted_native (runtime := runtime) bounds initialized nativeLaw
      completes)
    certificate players start current ordered clear event ready key decided fresh

end Vegas
