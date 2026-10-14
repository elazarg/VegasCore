/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveSchedulerImplementation
import GameTheory.Math.Probability.ProductConditioning
import GameTheory.Math.Probability.ConditionalObservation

/-! # Fresh seed coordinates before their first scheduler read

The false coordinate is the selected local seed. The true coordinate groups
the remainder, including the other event seeds. A fixed-seed scheduler that
has not read the local coordinate at any recorded command leaves it independent
of the remainder in its actual private-memory posterior.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

private theorem posterior_tag {Seed Output : Type} (law : PMF Seed) (choose : Seed → Output)
    (output : Output) :
    (fiberPosterior (law.map fun seed => (choose seed, seed)) Prod.fst output).map Prod.snd =
      fiberPosterior law choose output := by
  classical
  by_cases present : output ∈ (law.map choose).support
  · have transfer := fiberPosterior_bind_of_observation law
      (fun seed => PMF.pure (choose seed, seed)) choose Prod.fst
      (fun seed _ result supported => by
        cases (PMF.mem_support_pure_iff _ _).mp supported
        rfl) output present
    change fiberPosterior (law.map fun seed => (choose seed, seed)) Prod.fst output = _ at transfer
    rw [transfer, PMF.map_bind]
    simpa only [PMF.pure_map] using PMF.bind_pure (fiberPosterior law choose output)
  · have notPresent : output ∉
        ((law.map fun seed => (choose seed, seed)).map Prod.fst).support := by
      simpa only [PMF.map_comp, Function.comp_def] using present
    rw [fiberPosterior_of_not_mem_support _ _ notPresent,
      fiberPosterior_of_not_mem_support _ _ present, PMF.map_comp]
    change law.map id = law
    exact PMF.map_id _

private theorem independent_posterior_unread {A : Bool → Type} {Output : Type}
    (laws : (side : Bool) → PMF (A side)) (choose : ((side : Bool) → A side) → Output)
    (output : Output)
    (unread : ∀ values value, choose (Function.update values false value) = choose values) :
    ∃ updated : (side : Bool) → PMF (A side),
      fiberPosterior (independentProduct laws) choose output = independentProduct updated ∧
        updated false = laws false := by
  classical
  by_cases present : output ∈ ((independentProduct laws).map choose).support
  · obtain ⟨reference, supported⟩ := (independentProduct laws).support_nonempty
    let embed (value : A true) : (side : Bool) → A side
      | false => reference false
      | true => value
    let restriction : (side : Bool) → Set (A side)
      | false => Set.univ
      | true => {value | choose (embed value) = output}
    have choiceEq (values : (side : Bool) → A side) : choose (embed (values true)) =
        choose values := by
      have same : embed (values true) = Function.update values false (reference false) := by
        funext side
        cases side <;> simp [embed]
      rw [same]
      exact unread values (reference false)
    have rectangle : {values | choose values = output} = Set.pi Set.univ restriction := by
      ext values
      simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
      constructor
      · intro same side
        cases side with
        | false => trivial
        | true =>
            change choose (embed (values true)) = output
            rw [choiceEq values]
            exact same
      · intro listed
        have found := listed true
        change choose (embed (values true)) = output at found
        rwa [choiceEq values] at found
    have meets := exists_mem_fiber_of_mem_support_map present
    have coordinates (side : Bool) : ∃ value ∈ restriction side, value ∈ (laws side).support := by
      obtain ⟨values, matching, supported⟩ := meets
      have listed : values ∈ Set.pi Set.univ restriction := by rwa [← rectangle]
      exact ⟨values side, listed side (Set.mem_univ _),
        (independentProduct_support_iff laws values).mp supported side⟩
    refine ⟨fun side => (laws side).filter (restriction side) (coordinates side), ?_, ?_⟩
    · rw [fiberPosterior_eq_filter _ _ meets]
      simpa only [← rectangle] using filter_independentProduct laws restriction coordinates
    · exact filter_of_support_subset _ Set.univ (coordinates false) (Set.subset_univ _)
  · exact ⟨laws, fiberPosterior_of_not_mem_support _ _ present, rfl⟩

variable {Principal : Type} (app : ReactiveApplication Principal)

/-- If every command in actual scheduler recall ignores one fixed seed
coordinate, that coordinate retains its law and is independent of the remainder.
The other coordinate groups all other event seeds and all remainder randomness. -/
theorem schedulerMixture_posterior_unread {A : Bool → Type}
    (laws : (side : Bool) → PMF (A side))
    (choose : ((side : Bool) → A side) → List app.EnvironmentEntry →
      app.EnvironmentView → app.Command)
    (past : List app.EnvironmentEntry)
    (unread : ∀ (before : List app.EnvironmentEntry) (entry : app.EnvironmentEntry),
      before ++ [entry] <+: past → ∀ values value,
        choose (Function.update values false value) before entry.beforeView =
          choose values before entry.beforeView) :
    ∃ updated : (side : Bool) → PMF (A side),
      (app.schedulerMixture (independentProduct laws)
        (fun values before view => PMF.pure (choose values before view))).posterior past =
          independentProduct updated ∧ updated false = laws false := by
  induction past using List.reverseRecOn with
  | nil => exact ⟨laws, rfl, rfl⟩
  | append_singleton past entry ih =>
      obtain ⟨current, currentEq, localEq⟩ := ih fun before earlier member =>
        unread before earlier (member.trans (List.prefix_append _ _))
      rw [SchedulerImplementation.posterior_snoc, currentEq]
      simp only [schedulerMixture, PMF.pure_map]
      change ∃ updated,
        (fiberPosterior
          ((independentProduct current).map
            fun values => (choose values past entry.beforeView, values))
          Prod.fst entry.command).map Prod.snd = independentProduct updated ∧
            updated false = laws false
      rw [posterior_tag]
      obtain ⟨updated, posteriorEq, unchanged⟩ := independent_posterior_unread current
        (fun values => choose values past entry.beforeView) entry.command
        (unread past entry (List.prefix_refl _))
      exact ⟨updated, posteriorEq, unchanged.trans localEq⟩

/-- The marginal of a seed never read at any recorded scheduler command is
its original fixed law, even though the remainder posterior may have changed. -/
theorem schedulerMixture_posterior_unread_marginal {A : Bool → Type}
    (laws : (side : Bool) → PMF (A side))
    (choose : ((side : Bool) → A side) → List app.EnvironmentEntry →
      app.EnvironmentView → app.Command)
    (past : List app.EnvironmentEntry)
    (unread : ∀ (before : List app.EnvironmentEntry) (entry : app.EnvironmentEntry),
      before ++ [entry] <+: past → ∀ values value,
        choose (Function.update values false value) before entry.beforeView =
          choose values before entry.beforeView) :
    ((app.schedulerMixture (independentProduct laws)
      (fun values before view => PMF.pure (choose values before view))).posterior past).map
        (fun values => values false) = laws false := by
  obtain ⟨updated, posteriorEq, unchanged⟩ :=
    app.schedulerMixture_posterior_unread laws choose past unread
  rw [posteriorEq, independentProduct_map_eval, unchanged]

variable [DecidableEq Principal]

/-- Before a local seed is first read, the complete actual execution law is
independent of it. The condition concerns only primitive command choices at
recorded prefixes of supported realized executions. -/
theorem schedulerMixture_unread_execution {A : Bool → Type}
    (laws : (side : Bool) → PMF (A side))
    (choose : ((side : Bool) → A side) → List app.EnvironmentEntry →
      app.EnvironmentView → app.Command)
    (players : Principal → app.Policy) (count : Nat) (state : app.State)
    (unread : ∀ next ∈ (app.runRounds (app.schedulerMixture (independentProduct laws)
        (fun values before view => PMF.pure (choose values before view))).scheduler players count
          (Execution.initial app state)).support,
      ∀ (before : List app.EnvironmentEntry) (entry : app.EnvironmentEntry),
        before ++ [entry] <+: next.environmentRecall → ∀ values value,
          choose (Function.update values false value) before entry.beforeView =
            choose values before entry.beforeView) :
    ((independentProduct laws).bind fun values =>
      (app.runRounds (fun before view => PMF.pure (choose values before view)) players count
        (Execution.initial app state)).map fun next => (next, values false)) =
      (app.runRounds (app.schedulerMixture (independentProduct laws)
        (fun values before view => PMF.pure (choose values before view))).scheduler players count
          (Execution.initial app state)).bind fun next => (laws false).map (Prod.mk next) := by
  have joint := congrArg (fun law => law.map fun pair => (pair.1, pair.2 false))
    (app.schedulerMixture_joint (independentProduct laws)
      (fun values before view => PMF.pure (choose values before view)) players count state)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at joint
  refine joint.trans ?_
  apply bind_congr_on_support _
  intro next supported
  have marginal := app.schedulerMixture_posterior_unread_marginal laws choose
    next.environmentRecall (unread next supported)
  simpa only [PMF.map_comp, Function.comp_def] using
    congrArg (fun law : PMF (A false) => law.map (Prod.mk next)) marginal

end Interaction.ReactiveApplication
