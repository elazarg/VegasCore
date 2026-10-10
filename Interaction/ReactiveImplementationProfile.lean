/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveImplementation
import GameTheory.Math.Probability.Product

/-! # Joint private memory at actual reactive responses -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal Memory : Type} [Fintype Principal] [DecidableEq Principal]
  {app : ReactiveApplication Principal}

/-- One actual response disintegrates the whole independent private-memory
profile into the actual behavioral response and its conditioned profile.
The continuation can inspect every player's private memory. -/
theorem response_disintegrate_profile
    (implementations : Principal → app.Implementation Memory)
    (execution : app.Execution) (who : Principal)
    {Result : Type} (next : app.Execution → (Principal → Memory) → PMF Result) :
    (independentProduct (fun owner =>
      (implementations owner).posterior (execution.recall owner))).bind
        (fun memories =>
          ((implementations who).respond (memories who)
            (execution.recall who, execution.observe app who)).bind fun response =>
              next (execution.respond app who response.1)
                (Function.update memories who response.2)) =
      ((implementations who).policy (execution.recall who)
        (execution.observe app who)).bind fun action =>
          (independentProduct (fun owner => (implementations owner).posterior
            ((execution.respond app who action).recall owner))).bind
              (next (execution.respond app who action)) := by
  let split := Equiv.piSplitAt who (fun _ : Principal => Memory)
  have atWho (memory : Memory) (rest : {owner // owner ≠ who} → Memory) :
      split.symm (memory, rest) who = memory := by simp [split, Equiv.piSplitAt]
  have replace (memory replacement : Memory) (rest : {owner // owner ≠ who} → Memory) :
      Function.update (split.symm (memory, rest)) who replacement =
        split.symm (replacement, rest) := by
    funext owner
    by_cases equal : owner = who
    · subst owner
      simp [split, Equiv.piSplitAt]
    · simp [split, Equiv.piSplitAt, equal]
  let others := independentProduct (fun owner : {owner // owner ≠ who} =>
    (implementations owner).posterior (execution.recall owner))
  have posteriorAfter (action : app.Action) :
      independentProduct (fun owner => (implementations owner).posterior
          ((execution.respond app who action).recall owner)) =
        ((implementations who).posterior ((execution.respond app who action).recall who)).bind
          (fun memory => others.map (fun rest => split.symm (memory, rest))) := by
    rw [independentProduct_splitAt _ who]
    congr 1
    funext memory
    congr 1
    apply congrArg independentProduct
    funext owner
    rw [app.respond_recall_other execution who owner owner.property action]
  rw [independentProduct_splitAt _ who]
  simp only [posteriorAfter, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  conv_lhs => rw [PMF.bind_comm]
  conv_rhs =>
    arg 2
    ext action
    rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  apply bind_congr_on_support
  intro rest _
  have law := (implementations who).response_disintegrate execution who
    (fun current memory => next current (split.symm (memory, rest)))
  change (((implementations who).posterior (execution.recall who)).bind fun memory =>
    ((implementations who).respond (split.symm (memory, rest) who)
      (execution.recall who, execution.observe app who)).bind fun response =>
        next (execution.respond app who response.1)
          (Function.update (split.symm (memory, rest)) who response.2)) = _
  simp only [atWho, replace]
  exact law

/-- An actual environment command updates no private recall. Conditioning all
implementation memories before or after that command gives the same joint law. -/
theorem environmentStep_disintegrate_profile
    (implementations : Principal → app.Implementation Memory)
    (execution : app.Execution) (command : app.Command)
    {Result : Type} (next : app.Execution → (Principal → Memory) → PMF Result) :
    (independentProduct (fun owner =>
      (implementations owner).posterior (execution.recall owner))).bind
        (fun memories => (execution.environmentStep app command).bind
          (fun current => next current memories)) =
      (execution.environmentStep app command).bind fun current =>
        (independentProduct (fun owner =>
          (implementations owner).posterior (current.recall owner))).bind (next current) := by
  rw [PMF.bind_comm]
  apply bind_congr_on_support
  intro current reached
  have same : (fun owner => (implementations owner).posterior (execution.recall owner)) =
      (fun owner => (implementations owner).posterior (current.recall owner)) := by
    funext owner
    rw [app.environmentStep_recall execution current command reached]
  rw [same]

/-- The full private-memory profile disintegrates at an actual activation.
Only the activated owner's memory changes, while all other memories survive. -/
theorem resume_disintegrate_profile
    (implementations : Principal → app.Implementation Memory)
    (execution : app.Execution) (actor : Option Principal)
    {Result : Type} (next : app.Execution → (Principal → Memory) → PMF Result) :
    (independentProduct (fun owner =>
      (implementations owner).posterior (execution.recall owner))).bind
        (fun memories => match actor with
          | none => next execution memories
          | some who => ((implementations who).respond (memories who)
              (execution.recall who, execution.observe app who)).bind fun response =>
                next (execution.respond app who response.1)
                  (Function.update memories who response.2)) =
      (app.resume (fun owner => (implementations owner).policy) actor execution).bind
        (fun current => (independentProduct (fun owner =>
          (implementations owner).posterior (current.recall owner))).bind (next current)) := by
  cases actor with
  | none => simp only [resume, PMF.pure_bind]
  | some who =>
      simpa only [resume, invoke, PMF.bind_map, Function.comp_def] using
        response_disintegrate_profile implementations execution who next

end Interaction.ReactiveApplication
