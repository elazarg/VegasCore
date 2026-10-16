/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCommitWordPolicy
import Interaction.ReactiveProfileMixture

/-! # Whole physical continuations with the same complete owned words -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
  (wellFormed : setup.WellFormed)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (prior : (owner : Player) → PMF (DecisionView owner Δ))

local notation "app" => phaseApplication runtime leaks
local notation "family" => phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed
  assessment block low generation slotWeight slotNonnegative slotBounded
local notation "realized" => fun owner => ReactiveApplication.Implementation.policy
  (ReactiveApplication.policyMixture (app) (prior owner) (family owner))
local notation "posterior" => fun execution : (app).Execution => independentProduct
  (fun owner => ReactiveApplication.Implementation.posterior
    (ReactiveApplication.policyMixture (app) (prior owner) (family owner))
    (ReactiveApplication.Execution.recall execution owner))

/-- Every owner keeps the same complete latent word throughout the entire
original scheduler continuation. The conclusion retains the full physical
execution jointly with that word profile, including later phases and retries. -/
theorem phaseCommitWordPolicy_runRounds_joint
    (scheduler : (app).Scheduler) (count : Nat) (execution : (app).Execution) :
    (posterior execution).bind (fun words =>
      ((app).runRounds scheduler (fun owner => family owner (words owner)) count execution).map
        (fun final => (final, words))) =
      ((app).runRounds scheduler realized count execution).bind
        (fun final => (posterior final).map (Prod.mk final)) := by
  exact (app).runRounds_policyMixtures_posterior_joint scheduler prior family count execution

/-- At the current callback, sample the same original word profile before
responding and retain it through every later callback. Waiting is followed by
the entire actual continuation, with no resampling or source-value premise. -/
theorem phaseCommitWordPolicy_callback_joint
    (scheduler : (app).Scheduler) (count : Nat) (execution : (app).Execution) (who : Player) :
    (posterior execution).bind (fun words =>
      (family who (words who) (execution.recall who) (execution.observe (app) who)).bind
        (fun response => ((app).runRounds scheduler (fun owner => family owner (words owner))
          count (execution.respond (app) who response)).map (fun final => (final, words)))) =
      (realized who (execution.recall who) (execution.observe (app) who)).bind
        (fun response => ((app).runRounds scheduler realized count
          (execution.respond (app) who response)).bind
            (fun final => (posterior final).map (Prod.mk final))) := by
  let implementations := fun owner => (app).policyMixture (prior owner) (family owner)
  let next := fun current (words : (owner : Player) → DecisionView owner Δ) =>
    ((app).runRounds scheduler (fun owner => family owner (words owner)) count current).map
      (fun final => (final, words))
  have responseLaw := ReactiveApplication.response_disintegrate_profile implementations
    execution who next
  simp only [implementations, ReactiveApplication.policyMixture, PMF.bind_map,
    Function.comp_def, Function.update_eq_self] at responseLaw
  calc
    _ = (realized who (execution.recall who) (execution.observe (app) who)).bind
        (fun response => (posterior (execution.respond (app) who response)).bind
          (next (execution.respond (app) who response))) := responseLaw
    _ = _ := by
      apply bind_congr_on_support
      intro response _supported
      exact phaseCommitWordPolicy_runRounds_joint setup mode runtime leaks bounds wellFormed
        assessment block low generation slotWeight slotNonnegative slotBounded prior scheduler
        count (execution.respond (app) who response)

/-- The saved-entry law may correlate hidden source data with every owner's
word prior. The exact original entry tag is retained with the full callback
continuation and word profile; only the owner product is conditional on entry. -/
theorem phaseCommitWordPolicy_callback_entry_joint {Entry : Type}
    (entryLaw : PMF Entry)
    (entryPrior : Entry → (owner : Player) → PMF (DecisionView owner Δ))
    (scheduler : (app).Scheduler) (count : Nat)
    (execution : Entry → (app).Execution) (who : Player) :
    let realizedAt := fun entry owner => ReactiveApplication.Implementation.policy
      ((app).policyMixture (entryPrior entry owner) (family owner))
    let posteriorAt := fun entry (current : (app).Execution) => independentProduct
      (fun owner => ReactiveApplication.Implementation.posterior
        ((app).policyMixture (entryPrior entry owner) (family owner)) (current.recall owner))
    (entryLaw.bind fun entry => (posteriorAt entry (execution entry)).bind fun words =>
      ((family who (words who) ((execution entry).recall who)
        ((execution entry).observe (app) who)).bind fun response =>
          ((app).runRounds scheduler (fun owner => family owner (words owner)) count
            ((execution entry).respond (app) who response)).map (fun final => (final, words))).map
              (Prod.mk entry)) =
      (entryLaw.bind fun entry => PMF.map (Prod.mk entry)
        (PMF.bind (realizedAt entry who ((execution entry).recall who)
          ((execution entry).observe (app) who)) (fun response =>
            PMF.bind ((app).runRounds scheduler (realizedAt entry) count
              ((execution entry).respond (app) who response))
                (fun final => (posteriorAt entry final).map (Prod.mk final))))) := by
  intro realizedAt posteriorAt
  apply bind_congr_on_support
  intro entry _supported
  rw [← PMF.map_bind]
  exact congrArg (PMF.map (Prod.mk entry))
    (phaseCommitWordPolicy_callback_joint setup mode runtime leaks bounds wellFormed assessment
      block low generation slotWeight slotNonnegative slotBounded (entryPrior entry)
      scheduler count (execution entry) who)

/-- A supported final physical execution and its possible owned words replay
under those SAME members from the current execution. Thus both the complete
scheduler transcript and each owner's original word draw are retained. -/
theorem phaseCommitWordPolicy_runRounds_replay
    (scheduler : (app).Scheduler) (count : Nat) (execution final : (app).Execution)
    (reached : final ∈ ((app).runRounds scheduler realized count execution).support)
    (words : (owner : Player) → DecisionView owner Δ)
    (possible : ∀ owner, words owner ∈
      (((app).policyMixture (prior owner) (family owner)).posterior (final.recall owner)).support) :
    (∀ owner, words owner ∈
      (((app).policyMixture (prior owner) (family owner)).posterior
        (execution.recall owner)).support) ∧
      final ∈ ((app).runRounds scheduler (fun owner => family owner (words owner))
        count execution).support := by
  have joint : (final, words) ∈ (((app).runRounds scheduler realized count execution).bind
      (fun last => (posterior last).map (Prod.mk last))).support := by
    apply (PMF.mem_support_bind_iff _ _ _).mpr
    refine ⟨final, reached, ?_⟩
    apply (PMF.mem_support_map_iff _ _ _).mpr
    exact ⟨words, (independentProduct_support_iff _ _).mpr possible, rfl⟩
  rw [← phaseCommitWordPolicy_runRounds_joint setup mode runtime leaks bounds wellFormed
    assessment block low generation slotWeight slotNonnegative slotBounded prior scheduler count
    execution] at joint
  obtain ⟨sampled, present, replayed⟩ := (PMF.mem_support_bind_iff _ _ _).mp joint
  obtain ⟨last, supported, equality⟩ := (PMF.mem_support_map_iff _ _ _).mp replayed
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equality
  exact ⟨(independentProduct_support_iff _ _).mp present, supported⟩

end Vegas
