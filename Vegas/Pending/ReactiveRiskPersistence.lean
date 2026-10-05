/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRiskMenu
import Vegas.Pending.ReactiveDecisionMiss

/-! # Persistent service risk through actual execution steps

Public decision misses and both private recalled risk components persist through
environment commands and responses. Current opportunities are intentionally
excluded: they may change without an owner response. These backward clear
lemmas therefore apply to persistent risk alone.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (bound : graph.EventId → Nat)

theorem publicMiss_environment {execution next : (runtime.reactiveApplication leaks).Execution}
    {command : (runtime.reactiveApplication leaks).Command} (who : Player)
    (missed : execution.application.publicView.missedDecisionBy who = true)
    (moved : next ∈
      (execution.environmentStep (runtime.reactiveApplication leaks) command).support) :
    next.application.publicView.missedDecisionBy who = true := by
  obtain ⟨event, marked, owned⟩ := of_decide_eq_true missed
  apply PublicView.missedDecisionBy_of_event _ who event owned
  exact (runtime.reactiveMissedDecisionInvariant leaks event).environmentStep
    execution next command marked moved

theorem persistentServiceRisk_environment_mono (who : Player)
    {execution next : (runtime.reactiveApplication leaks).Execution}
    {command : (runtime.reactiveApplication leaks).Command}
    (risky : runtime.persistentServiceRisk leaks bound who (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who) = true)
    (moved : next ∈
      (execution.environmentStep (runtime.reactiveApplication leaks) command).support) :
    runtime.persistentServiceRisk leaks bound who (next.recall who)
      (next.observe (runtime.reactiveApplication leaks) who) = true := by
  rcases (runtime.persistentServiceRisk_iff leaks bound who _ _).mp risky with
    (publicMiss | recalled) | opportunity
  · exact runtime.persistentServiceRisk_of_public_miss leaks bound who _ _
      (runtime.publicMiss_environment leaks who publicMiss moved)
  · apply runtime.persistentServiceRisk_of_recalled leaks bound who _ _
    have recallEq := (runtime.reactiveApplication leaks).environmentStep_recall execution next
      command moved
    rw [recallEq]
    exact recalled
  · apply runtime.persistentServiceRisk_of_opportunityRecall leaks bound who _ _
    have recallEq := (runtime.reactiveApplication leaks).environmentStep_recall execution next
      command moved
    rw [recallEq]
    exact opportunity

theorem persistentServiceRisk_respond_mono
    (execution : (runtime.reactiveApplication leaks).Execution)
    (actor who : Player) (response : (runtime.reactiveApplication leaks).Action)
    (risky : runtime.persistentServiceRisk leaks bound who (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who) = true) :
    runtime.persistentServiceRisk leaks bound who
      ((execution.respond (runtime.reactiveApplication leaks) actor response).recall who)
      ((execution.respond (runtime.reactiveApplication leaks) actor response).observe
        (runtime.reactiveApplication leaks) who) = true := by
  rcases (runtime.persistentServiceRisk_iff leaks bound who _ _).mp risky with
    (publicMiss | recalled) | opportunity
  · apply runtime.persistentServiceRisk_of_public_miss leaks bound who _ _
    have publicEq := runtime.reactive_respond_application leaks execution actor response
    exact (congrArg (fun view : PublicView graph => view.missedDecisionBy who) publicEq.2).trans
      publicMiss
  · apply runtime.persistentServiceRisk_of_recalled leaks bound who _ _
    obtain ⟨entry, present, identity, event, named, owned, unprotected⟩ :=
      (runtime.recalledSubmissionRisk_iff leaks bound who _).mp recalled
    apply (runtime.recalledSubmissionRisk_iff leaks bound who _).mpr
    exact ⟨entry,
      (runtime.reactiveApplication leaks).respond_recall_mono execution actor who response present,
      identity, event, named, owned, unprotected⟩
  · apply runtime.persistentServiceRisk_of_opportunityRecall leaks bound who _ _
    exact runtime.recalledOpportunityRisk_respond_mono leaks bound execution actor who
      response opportunity

theorem persistentServiceRisk_clear_before_environment (who : Player)
    {execution next : (runtime.reactiveApplication leaks).Execution}
    {command : (runtime.reactiveApplication leaks).Command}
    (clear : runtime.persistentServiceRisk leaks bound who (next.recall who)
      (next.observe (runtime.reactiveApplication leaks) who) = false)
    (moved : next ∈
      (execution.environmentStep (runtime.reactiveApplication leaks) command).support) :
    runtime.persistentServiceRisk leaks bound who (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro risky
  have persists := runtime.persistentServiceRisk_environment_mono leaks bound who risky moved
  rw [clear] at persists
  cases persists

theorem persistentServiceRisk_clear_before_respond
    (execution : (runtime.reactiveApplication leaks).Execution) (actor who : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (clear : runtime.persistentServiceRisk leaks bound who
      ((execution.respond (runtime.reactiveApplication leaks) actor response).recall who)
      ((execution.respond (runtime.reactiveApplication leaks) actor response).observe
        (runtime.reactiveApplication leaks) who) = false) :
    runtime.persistentServiceRisk leaks bound who (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro risky
  have persists := runtime.persistentServiceRisk_respond_mono leaks bound execution actor who
    response risky
  rw [clear] at persists
  cases persists

end Vegas.EventGraphRuntime
