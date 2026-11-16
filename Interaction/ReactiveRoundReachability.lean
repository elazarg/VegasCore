module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveRounds
public import Interaction.ReactiveRecall
public import Interaction.ReactiveResponseMenu
public import GameTheoryExtensions.Math.Probability.Uniform

@[expose] public section

/-! # Legal histories occur in the round evaluator

A response family with support on every menu action witnesses every legal
history. At a pending activation the witness stops after the environment step;
at scheduler control it stops after a complete round. Thus round-based service
proofs also apply at off-path decision histories, without assuming those
histories have positive probability in an equilibrium assessment.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu)

end ResponseMenu

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

open GameTheory.Protocol GameTheory.Math.Probability

/-- Initialization followed by a specified number of complete scheduler rounds. -/
def roundsFrom (initial : PMF app.State) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) : PMF app.Execution :=
  initial.bind fun state => app.runRounds scheduler players count (Execution.initial app state)

theorem roundsFrom_succ (initial : PMF app.State) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) :
    app.roundsFrom initial scheduler players (count + 1) =
      (app.roundsFrom initial scheduler players count).bind (app.round scheduler players) := by
  unfold roundsFrom
  simp only [app.runRounds_add scheduler players count 1, PMF.bind_bind]
  congr 1
  funext state
  apply bind_congr_on_support _
  intro execution _
  simp only [runRounds, PMF.bind_pure]
end Interaction.ReactiveApplication

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

private theorem round_recall_subset
    (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (before after : app.Execution) (reached : after ∈ (app.round scheduler players before).support)
    (who : Principal) : before.logs who ⊆ after.logs who := by
  obtain ⟨command, _, dispatched⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  obtain ⟨middle, moved, resumed⟩ := (PMF.mem_support_bind_iff _ _ _).mp dispatched
  have recalled := app.environmentStep_recall before middle command moved
  cases actor : command.actor? app with
  | none =>
      change after ∈ (app.resume players (command.actor? app) middle).support at resumed
      rw [actor, resume, PMF.mem_support_pure_iff] at resumed
      subst after
      rw [recalled]
  | some owner =>
      change after ∈ (app.resume players (command.actor? app) middle).support at resumed
      rw [actor] at resumed
      obtain ⟨response, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp resumed
      rw [← recalled]
      exact app.respond_recall_mono middle owner who response

private theorem runRounds_recall_subset
    (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (count : Nat) (before after : app.Execution)
    (reached : after ∈ (app.runRounds scheduler players count before).support)
    (who : Principal) : before.logs who ⊆ after.logs who := by
  induction count generalizing before with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact List.Subset.refl _
  | succ count ih =>
      obtain ⟨middle, moved, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      intro entry member
      exact ih middle rest
        (round_recall_subset app scheduler players before middle moved who member)

private theorem round_support_of_recorded_policy_eq
    (scheduler : app.Scheduler) (old new : Principal → app.Policy)
    (before after : app.Execution) (reached : after ∈ (app.round scheduler old before).support)
    (agree : ∀ who (entry : app.PlayerEntry), entry ∈ after.logs who → ∀ past,
      old who past entry.beforeView = new who past entry.beforeView) :
    after ∈ (app.round scheduler new before).support := by
  obtain ⟨command, selected, dispatched⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  obtain ⟨middle, moved, resumed⟩ := (PMF.mem_support_bind_iff _ _ _).mp dispatched
  refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨command, selected, ?_⟩
  refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨middle, moved, ?_⟩
  change after ∈ (app.resume old (command.actor? app) middle).support at resumed
  cases actor : command.actor? app with
  | none => simpa only [actor, resume] using resumed
  | some who =>
      rw [actor] at resumed
      obtain ⟨response, chosen, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp resumed
      have recorded : ∃ entry ∈ (middle.respond app who response).logs who,
          entry.beforeView = middle.observe app who := by
        rcases response with ⟨transmission⟩
        cases transmission <;>
          simp only [Execution.respond, ite_true, List.mem_append, List.mem_singleton] <;>
          exact ⟨_, Or.inr rfl, rfl⟩
      obtain ⟨entry, member, view⟩ := recorded
      have equal := agree who entry member (middle.logs who)
      rw [view] at equal
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨response, equal ▸ chosen, rfl⟩

/-- Agreement at recorded response views preserves the support of complete rounds. -/
theorem runRounds_support_of_recorded_policy_eq
    (scheduler : app.Scheduler) (old new : Principal → app.Policy)
    (count : Nat) (before after : app.Execution)
    (reached : after ∈ (app.runRounds scheduler old count before).support)
    (agree : ∀ who (entry : app.PlayerEntry), entry ∈ after.logs who → ∀ past,
      old who past entry.beforeView = new who past entry.beforeView) :
    after ∈ (app.runRounds scheduler new count before).support := by
  induction count generalizing before with
  | zero => exact reached
  | succ count ih =>
      obtain ⟨middle, moved, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
      have middleAgree : ∀ who (entry : app.PlayerEntry), entry ∈ middle.logs who → ∀ past,
          old who past entry.beforeView = new who past entry.beforeView := by
        intro who entry member past
        exact agree who entry (runRounds_recall_subset app scheduler old count middle after rest
          who member) past
      refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨middle,
        round_support_of_recorded_policy_eq app scheduler old new before middle moved middleAgree,
        ih middle rest⟩

/-- Agreement at recorded response views preserves initialized execution support. -/
theorem roundsFrom_support_of_recorded_policy_eq
    (initial : PMF app.State) (scheduler : app.Scheduler) (old new : Principal → app.Policy)
    (count : Nat) (after : app.Execution)
    (reached : after ∈ (app.roundsFrom initial scheduler old count).support)
    (agree : ∀ who (entry : app.PlayerEntry), entry ∈ after.logs who → ∀ past,
      old who past entry.beforeView = new who past entry.beforeView) :
    after ∈ (app.roundsFrom initial scheduler new count).support := by
  obtain ⟨state, selected, moved⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨state, selected,
    runRounds_support_of_recorded_policy_eq app scheduler old new count _ after moved agree⟩

end Interaction.ReactiveApplication
