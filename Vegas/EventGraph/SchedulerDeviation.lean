/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.SchedulerReplayLaw
import Vegas.EventGraph.SchedulerErasure

/-! # Unilateral deviations under a pure public scheduler -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

private theorem policyPlan_choice_selected
    (scheduler : graph.DeterministicPublicScheduler)
    (profile : graph.BehavioralProfile) (config : graph.Config)
    (notTerminal : ¬ config.cut.Terminal)
    (choice : Σ selected : {event : graph.EventId // config.cut.Ready event},
      graph.Action selected.1)
    (member : choice ∈ (graph.policyPlan profile scheduler.toPublic
      config notTerminal).support) :
    (scheduler (graph.publicObserve config) config.cut.enabled
      (enabled_nonempty_of_not_terminal config notTerminal)).1 = choice.1.1 := by
  unfold policyPlan DeterministicPublicScheduler.toPublic at member
  simp only [FinDist.pure_bind] at member
  split at member <;> rename_i actor
  · rw [FinDist.support_map] at member
    obtain ⟨action, _, rfl⟩ := member
    rfl
  · simpa using congrArg (fun selected => selected.1.1)
      (FinDist.mem_support_pure.mp member).symm

private theorem policyPlan_update_replay_eq
    (scheduler : graph.DeterministicPublicScheduler)
    (sigma : graph.BehavioralProfile) (who : Player)
    (tau : graph.BehavioralPolicy who) (inputs : graph.Inputs)
    (config : graph.Config) (reachable : graph.SchedulerReachable scheduler inputs config)
    (notTerminal : ¬ config.cut.Terminal) :
    graph.policyPlan
        (Profile.update (sig := graph.gameSignature)
          (graph.normalizeProfile sigma) who tau) scheduler.toPublic
        config notTerminal =
      graph.policyPlan
        (Profile.update (sig := graph.gameSignature) (graph.normalizeProfile sigma) who
          (graph.replayPolicy scheduler who tau)) scheduler.toPublic
        config notTerminal := by
  unfold policyPlan DeterministicPublicScheduler.toPublic
  simp only [FinDist.pure_bind]
  split <;> rename_i ownerEq
  · rename_i owner
    by_cases same : owner = who
    · subst owner
      rw [Profile.update_same, Profile.update_same]
      congr 1
      apply congrArg (tau _ ownerEq)
      apply PlayerObservation.ext graph
      · exact (reachable.replayPrefix_eq_history notTerminal _ rfl who).symm
      · rfl
      · rfl
    · rw [Profile.update_of_ne _ _ same, Profile.update_of_ne _ _ same]
  · rfl

private theorem runPlan_update_replay_eq
    (scheduler : graph.DeterministicPublicScheduler)
    (sigma : graph.BehavioralProfile) (who : Player)
    (tau : graph.BehavioralPolicy who) (inputs : graph.Inputs) :
    ∀ fuel config,
      graph.SchedulerReachable scheduler inputs config →
      graph.runPlan
          (graph.policyPlan
            (Profile.update (sig := graph.gameSignature)
              (graph.normalizeProfile sigma) who tau)
            scheduler.toPublic) fuel config =
        graph.runPlan
          (graph.policyPlan
            (Profile.update (sig := graph.gameSignature)
              (graph.normalizeProfile sigma) who
              (graph.replayPolicy scheduler who tau)) scheduler.toPublic) fuel config := by
  intro fuel
  induction fuel with
  | zero => intro config reachable; rfl
  | succ fuel ih =>
      intro config reachable
      by_cases terminal : config.cut.Terminal
      · simp [runPlan, terminal]
      · rw [runPlan, runPlan, dif_neg terminal, dif_neg terminal,
          policyPlan_update_replay_eq scheduler sigma who tau inputs config reachable terminal]
        apply FinDist.bind_congr
        intro choice choiceMember
        apply FinDist.bind_congr
        intro next nextMember
        apply ih
        have selected := policyPlan_choice_selected scheduler
          (Profile.update (sig := graph.gameSignature) (graph.normalizeProfile sigma) who
            (graph.replayPolicy scheduler who tau)) config terminal choice choiceMember
        exact .step reachable terminal choice.1.1 selected choice.1.2 choice.2 next nextMember

/-- Under one pure scheduler, replacing the focal policy by its replay wrapper
preserves the complete configuration law. -/
theorem runPolicies_update_replay_eq
    (scheduler : graph.DeterministicPublicScheduler)
    (sigma : graph.BehavioralProfile) (who : Player)
    (tau : graph.BehavioralPolicy who) (inputs : graph.Inputs) :
    graph.runPolicies scheduler.toPublic
        (Profile.update (sig := graph.gameSignature)
          (graph.normalizeProfile sigma) who tau) inputs =
      graph.runPolicies scheduler.toPublic
        (Profile.update (sig := graph.gameSignature) (graph.normalizeProfile sigma) who
          (graph.replayPolicy scheduler who tau)) inputs := by
  apply runPlan_update_replay_eq scheduler sigma who tau inputs
  exact .initial

/-- A pure scheduler deviation is represented canonically by the replayed
focal policy; arbitrary completion-order dependence is removed without
changing the terminal typed-store law. -/
theorem BarrierOrdered.runPolicies_update_store_eq_canonical
    (ordered : graph.BarrierOrdered)
    (scheduler : graph.DeterministicPublicScheduler)
    (sigma : graph.BehavioralProfile) (who : Player)
    (tau : graph.BehavioralPolicy who) (inputs : graph.Inputs) :
    (graph.runPolicies scheduler.toPublic
      (Profile.update (sig := graph.gameSignature)
        (graph.normalizeProfile sigma) who tau) inputs).map Config.store =
      (graph.runPolicies graph.canonicalScheduler
        (Profile.update (sig := graph.gameSignature)
          (graph.normalizeProfile sigma) who
          (graph.replayPolicy scheduler who tau)) inputs).map Config.store := by
  let replayed := Profile.update (sig := graph.gameSignature)
    (graph.normalizeProfile sigma) who (graph.replayPolicy scheduler who tau)
  have sameScheduler := congrArg (fun law : FinDist graph.Config => law.map Config.store)
    (graph.runPolicies_update_replay_eq scheduler sigma who tau inputs)
  have erased := ordered.runPolicies_store_eq_canonical replayed scheduler.toPublic inputs
  have fixed : graph.normalizeProfile replayed = replayed := by
    simp only [replayed, normalizeProfile_update, normalizeProfile_idempotent,
      normalizePolicy_replayPolicy]
  rw [fixed] at erased
  exact sameScheduler.trans erased

end Vegas.EventGraph
