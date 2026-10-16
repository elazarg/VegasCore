/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMixtureRounds
import Interaction.ReactiveImplementationProfile
import GameTheory.Math.Probability.Product

/-! # Complete scheduler runs with private policy mixtures for every owner

Each private member is selected from its actual own-recall posterior. The
existing scheduler runner realizes the whole profile, retaining an arbitrary
outer entry mixture and its tag when supplied.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} {Memory : Principal → Type} [Fintype Principal] [DecidableEq Principal]
  (app : ReactiveApplication Principal)

/-- Simultaneously realizing all private policy mixtures preserves the whole
actual scheduler run. Independence is conditional on the given execution;
each owner uses its posterior on its own complete recall. -/
theorem runRounds_policyMixtures (scheduler : app.Scheduler)
    (initial : (owner : Principal) → PMF (Memory owner))
    (members : (owner : Principal) → Memory owner → app.Policy)
    (count : Nat) (execution : app.Execution) :
    (independentProduct (fun who =>
      (app.policyMixture (initial who) (members who)).posterior (execution.recall who))).bind
        (fun memories => app.runRounds scheduler (fun who => members who (memories who))
          count execution) =
      app.runRounds scheduler
        (fun who => (app.policyMixture (initial who) (members who)).policy) count execution := by
  classical
  let realized := fun who => (app.policyMixture (initial who) (members who)).policy
  let laws := fun who =>
    (app.policyMixture (initial who) (members who)).posterior (execution.recall who)
  let profile := fun (active : Finset Principal)
    (memories : (owner : Principal) → Memory owner) who =>
    if who ∈ active then members who (memories who) else realized who
  have peel (active : Finset Principal) (who : Principal) (absent : who ∉ active) :
      (independentProduct laws).bind (fun memories =>
        app.runRounds scheduler (profile (insert who active) memories) count execution) =
      (independentProduct laws).bind (fun memories =>
        app.runRounds scheduler (profile active memories) count execution) := by
    let split := Equiv.piSplitAt who Memory
    rw [independentProduct_splitAt laws who]
    simp only [PMF.bind_bind, PMF.bind_map]
    conv_lhs => rw [PMF.bind_comm]
    conv_rhs => rw [PMF.bind_comm]
    apply bind_congr_on_support
    intro rest _
    let baseline := fun owner => if other : owner = who then realized owner else
      if owner ∈ active then members owner (rest ⟨owner, other⟩) else realized owner
    have before (memory : Memory who) :
        profile (insert who active) (split.symm (memory, rest)) =
          Function.update baseline who (members who memory) := by
      funext owner
      by_cases same : owner = who
      · subst owner
        simp [profile, split, Equiv.piSplitAt]
      · simp [profile, baseline, same, split, Equiv.piSplitAt]
    have after (memory : Memory who) :
        profile active (split.symm (memory, rest)) = baseline := by
      funext owner
      by_cases same : owner = who
      · subst owner
        simp [profile, baseline, absent]
      · simp [profile, baseline, same, split, Equiv.piSplitAt]
    change (laws who).bind (fun memory => app.runRounds scheduler
        (profile (insert who active) (split.symm (memory, rest))) count execution) =
      (laws who).bind (fun memory => app.runRounds scheduler
        (profile active (split.symm (memory, rest))) count execution)
    simp_rw [before, after]
    rw [PMF.bind_const]
    have updated : Function.update baseline who (realized who) = baseline := by
      funext owner
      by_cases same : owner = who
      · subst owner
        simp [baseline]
      · simp [same]
    have single := app.runRounds_policyMixture scheduler (initial who) (members who) who
      baseline count execution
    change (laws who).bind (fun memory => app.runRounds scheduler
      (Function.update baseline who (members who memory)) count execution) =
        app.runRounds scheduler (Function.update baseline who (realized who)) count execution
      at single
    rwa [updated] at single
  have remove (active : Finset Principal) :
      (independentProduct laws).bind (fun memories =>
        app.runRounds scheduler (profile active memories) count execution) =
      app.runRounds scheduler realized count execution := by
    induction active using Finset.induction_on with
    | empty => simp only [profile, Finset.notMem_empty, ite_false, PMF.bind_const]
    | @insert who active absent ih => exact (peel active who absent).trans ih
  simpa only [profile, Finset.mem_univ, ite_true] using remove Finset.univ

/-- The complete run retains the private member profile jointly with its
actual execution. Conditioning each member on the final own recall gives
that same joint law, rather than merely its external execution marginal. -/
theorem runRounds_policyMixtures_posterior_joint (scheduler : app.Scheduler)
    (initial : (owner : Principal) → PMF (Memory owner))
    (members : (owner : Principal) → Memory owner → app.Policy)
    (count : Nat) (execution : app.Execution) :
    (independentProduct (fun who =>
      (app.policyMixture (initial who) (members who)).posterior (execution.recall who))).bind
        (fun memories =>
          (app.runRounds scheduler (fun who => members who (memories who)) count execution).map
            (fun final => (final, memories))) =
      (app.runRounds scheduler
        (fun who => (app.policyMixture (initial who) (members who)).policy) count execution).bind
          (fun final => (independentProduct (fun who =>
            (app.policyMixture (initial who) (members who)).posterior (final.recall who))).map
              (Prod.mk final)) := by
  let implementations := fun who => app.policyMixture (initial who) (members who)
  let posterior := fun current : app.Execution => independentProduct (fun who =>
    (implementations who).posterior (current.recall who))
  let profile := fun (memories : (owner : Principal) → Memory owner) who =>
    members who (memories who)
  let realized := fun who => (implementations who).policy
  change (posterior execution).bind (fun memories =>
    (app.runRounds scheduler (profile memories) count execution).map
      (fun final => (final, memories))) =
    (app.runRounds scheduler realized count execution).bind fun final =>
      (posterior final).map (Prod.mk final)
  induction count generalizing execution with
  | zero =>
      simp only [runRounds, PMF.pure_map, PMF.pure_bind]
      rfl
  | succ count ih =>
      let next := fun current memories =>
        (app.runRounds scheduler (profile memories) count current).map
          (fun final => (final, memories))
      have step : (posterior execution).bind (fun memories =>
          (app.round scheduler (profile memories) execution).bind
            (fun current => next current memories)) =
          (app.round scheduler realized execution).bind fun current =>
            (posterior current).bind (next current) := by
        have dispatched := round_disintegrate_profile implementations execution scheduler next
        simp only [implementations, policyMixture, PMF.bind_map, Function.comp_def,
          Function.update_eq_self] at dispatched
        refine Eq.trans ?_ dispatched
        apply bind_congr_on_support
        intro memories _
        simp only [round, dispatch, PMF.bind_bind]
        apply bind_congr_on_support
        intro command _
        apply bind_congr_on_support
        intro current _
        cases command.actor? app with
        | none => simp only [resume, PMF.pure_bind]
        | some who => simp only [resume, invoke, profile, PMF.bind_map, Function.comp_def]
      simp only [runRounds, PMF.map_bind, PMF.bind_bind]
      change (posterior execution).bind (fun memories =>
        (app.round scheduler (profile memories) execution).bind
          (fun current => next current memories)) = _
      rw [step]
      apply bind_congr_on_support
      intro current _
      exact ih current

/-- Keeping an arbitrary original entry beside every complete run preserves
the same joint law. The owner products are conditional on that entry; no
independence between entries or their hidden source data is asserted. -/
theorem runRounds_policyMixtures_entry_joint {Entry : Type}
    (entryLaw : PMF Entry) (scheduler : app.Scheduler)
    (initial : Entry → (owner : Principal) → PMF (Memory owner))
    (members : Entry → (owner : Principal) → Memory owner → app.Policy)
    (count : Nat) (execution : Entry → app.Execution) :
    (entryLaw.bind fun entry =>
      (independentProduct (fun who =>
        (app.policyMixture (initial entry who) (members entry who)).posterior
          ((execution entry).recall who))).bind fun memories =>
        (app.runRounds scheduler (fun who => members entry who (memories who)) count
          (execution entry)).map (Prod.mk entry)) =
      entryLaw.bind fun entry =>
        (app.runRounds scheduler
          (fun who => (app.policyMixture (initial entry who) (members entry who)).policy)
            count (execution entry)).map (Prod.mk entry) := by
  apply bind_congr_on_support
  intro entry _
  rw [← PMF.map_bind]
  exact congrArg (PMF.map (Prod.mk entry))
    (app.runRounds_policyMixtures scheduler (initial entry) (members entry) count (execution entry))

end Interaction.ReactiveApplication
