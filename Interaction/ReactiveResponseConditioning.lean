/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveImplementationProfile

/-! # Whole private-memory conditioning with the actual raw response retained -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}

/-- Disintegration retains the actual raw action as well as the updated private
memory. A following history kernel can therefore retain the precise signed
response, including preparation and evidence aliases. -/
theorem Implementation.response_action_disintegrate {Memory Result : Type}
    (implementation : app.Implementation Memory) (execution : app.Execution) (who : Principal)
    (next : app.Action → Memory → PMF Result) :
    (implementation.posterior (execution.recall who)).bind (fun memory =>
      (implementation.respond memory (execution.recall who, execution.observe app who)).bind
        fun response => next response.1 response.2) =
      (implementation.policy (execution.recall who) (execution.observe app who)).bind
        (fun action =>
          (implementation.posterior ((execution.respond app who action).recall who)).bind
            (next action)) := by
  let law := (implementation.posterior (execution.recall who)).bind fun memory =>
    implementation.respond memory (execution.recall who, execution.observe app who)
  rw [← PMF.bind_bind]
  change law.bind (fun response => next response.1 response.2) = _
  conv_lhs => arg 1; rw [eq_bind_fst_fiberPosterior_snd law]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, Implementation.policy_eq,
    Implementation.posterior_respond, law]

variable {Memory : Principal → Type} [Fintype Principal]

/-- The actual response and the complete owner-memory profile are retained in
one disintegration. Only the responding owner's posterior is updated; all
other owners and any outer entry tag stay in the continuation. -/
theorem response_action_disintegrate_profile
    (implementations : (owner : Principal) → app.Implementation (Memory owner))
    (execution : app.Execution) (who : Principal)
    {Result : Type} (next : app.Action → ((owner : Principal) → Memory owner) → PMF Result) :
    (independentProduct (fun owner =>
      (implementations owner).posterior (execution.recall owner))).bind
        (fun memories =>
          ((implementations who).respond (memories who)
            (execution.recall who, execution.observe app who)).bind fun response =>
              next response.1
                (Function.update memories who response.2)) =
      ((implementations who).policy (execution.recall who)
        (execution.observe app who)).bind fun action =>
          (independentProduct (fun owner => (implementations owner).posterior
            ((execution.respond app who action).recall owner))).bind
              (next action) := by
  let split := Equiv.piSplitAt who Memory
  have atWho (memory : Memory who) (rest : (owner : {owner // owner ≠ who}) → Memory owner.val) :
      split.symm (memory, rest) who = memory := by simp [split, Equiv.piSplitAt]
  have replace (memory replacement : Memory who)
      (rest : (owner : {owner // owner ≠ who}) → Memory owner.val) :
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
  have law := (implementations who).response_action_disintegrate execution who
    (fun current memory => next current (split.symm (memory, rest)))
  change (((implementations who).posterior (execution.recall who)).bind fun memory =>
    ((implementations who).respond (split.symm (memory, rest) who)
      (execution.recall who, execution.observe app who)).bind fun response =>
        next response.1
          (Function.update (split.symm (memory, rest)) who response.2)) = _
  simp only [atWho, replace]
  exact law

end Interaction.ReactiveApplication
