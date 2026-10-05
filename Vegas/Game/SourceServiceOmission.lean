/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecisionSupport
import Vegas.Pending.ReactiveDecisionMiss

/-! # No public decision misses on retained full-source histories

Actual retained prefixes derive an empty public miss table. Both binding and
resolution owners submit a real decision before their block's ticks.
Its persistence under arbitrary continuations then rules it out at every
intermediate service command, and actual history support covers each legal
finite-game history, including off-path histories.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Arbitrary retained players complete the actual whole plan without public
missed decisions. Guarded publication failures are actual accepted decisions. -/
theorem sourceService_plan_no_miss
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network (rosterPlan setup rosters)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support) :
    final.application.missedEvents = ∅ := by
  have same : rosterPlanPrefix setup rosters (eventCount setup.program) =
      rosterPlan setup rosters := by
    unfold rosterPlanPrefix rosterPlan
    congr 1
    apply List.take_of_length_le
    simp only [List.length_finRange]
    exact Nat.le_refl _
  have supported := reached
  rw [← same] at supported
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, boundary⟩ :=
    initialized_sourceService_prefix_support setup leaks bounds values capacity rosters
      opportunities players lawful network (failureProfile setup.program)
      (eventCount setup.program) (Nat.le_refl _) final supported
  exact boundary.missed

/-- No initialized prefix of the real command plan can already contain
omission evidence: it would persist into a retained completed execution. -/
theorem sourceService_command_prefix_no_miss
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (count : Nat)
    (current : (application setup leaks).Execution)
    (reached : current ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network
        ((rosterPlan setup rosters).take count)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).support) :
    current.application.missedEvents = ∅ := by
  let app := application setup leaks
  let suffix := (rosterPlan setup rosters).drop count
  obtain ⟨final, continued⟩ :=
    ((runtime setup).runInteractionPlan leaks players network suffix current).support_nonempty
  have finalSupported : final ∈ ((initialLaw setup).bind fun state =>
      (runtime setup).runInteractionPlan leaks players network (rosterPlan setup rosters)
        (ReactiveApplication.Execution.initial app state)).support := by
    rw [← List.take_append_drop count (rosterPlan setup rosters)]
    simp only [runInteractionPlan_append, ← PMF.bind_bind, PMF.support_bind]
    apply Set.mem_iUnion₂.mpr
    exact ⟨current, PMF.support_bind .. ▸ reached, continued⟩
  have clear := sourceService_plan_no_miss setup leaks bounds values capacity rosters
    opportunities players lawful network final finalSupported
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro event missed
  have persistent := (runtime setup).runInteractionPlan_preserves leaks players network
    _ (ReactiveApplication.Invariant.policyInvariant app
      ((runtime setup).reactiveMissedDecisionInvariant leaks event) players)
      suffix current final missed continued
  rw [clear] at persistent
  exact Finset.notMem_empty event persistent

/-- The existing omission detector is false at every actual legal retained
history, regardless of the strategy whose support supplied that history. -/
theorem sourceService_history_no_miss
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) :
    control.execution.application.missedEvents = ∅ := by
  let menu := sourceServiceMenu setup leaks bounds rosters
  cases actor : control.actor with
  | some who =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          boundary, _, _, checkpoint, _, _, _, _, _, publicEq, _, _⟩ :=
        sourceService_decision_boundary setup leaks bounds values capacity rosters opportunities
          network (failureProfile setup.program) who control trace actor
      have same := congrArg PublicView.missedEvents publicEq
      exact same.trans checkpoint.missed
  | none =>
      have supported := menu.roundSupported_uniform (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) trace
      change control.execution.environmentRecall.length + control.remaining =
        (rosterPlan setup rosters).length ∧ _ at supported
      have within : control.execution.environmentRecall.length ≤
          (rosterPlan setup rosters).length := by omega
      have reached := supported.2
      rw [actor] at reached
      rw [roster_roundsFrom setup leaks rosters network menu.uniformResponses _ within] at reached
      exact sourceService_command_prefix_no_miss setup leaks bounds values capacity rosters
        opportunities menu.uniformResponses
        (fun who past view response member =>
          (menu.uniformResponses_support who past view response).mp member)
        network _ control.execution reached

end Vegas
