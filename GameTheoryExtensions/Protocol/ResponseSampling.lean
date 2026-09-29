/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Conditioning
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform
import GameTheoryExtensions.Math.Probability.Support

/-! # Sequential sampling of correlated responses

Any finitely supported law of fixed-length action lists can be sampled one
action at a time, using just the already chosen prefix. Conditioning retains
arbitrary correlations. No cost or extra observation is introduced.
-/

noncomputable section

namespace GameTheory.Protocol.ResponseSampling

open GameTheory.Math.Probability

variable {Action : Type*} [Inhabited Action]

def next (law : PMF (List Action)) : List Action → PMF Action
  | [] => law.map (List.headD · default)
  | action :: past =>
      next ((fiberConditional law (List.headD · default) action).map List.tail) past

def run (policy : List Action → PMF Action) : Nat → PMF (List Action)
  | 0 => PMF.pure []
  | count + 1 => (policy []).bind fun action =>
      (run (fun past => policy (action :: past)) count).map (action :: ·)

private theorem conditioned_support {α β : Type*} (law : PMF α) (f : α → β) (b : β) :
    (fiberConditional law f b).support ⊆ law.support := by
  classical
  unfold fiberConditional
  split
  · exact fun _ member => ((PMF.mem_support_filter_iff _).mp member).2
  · exact Set.Subset.refl _

private theorem conditioned_fibre {α β : Type*} (law : PMF α) (f : α → β) (b : β)
    (supported : b ∈ (law.map f).support) :
    ∀ a ∈ (fiberConditional law f b).support, f a = b := by
  classical
  obtain ⟨witness, member, rfl⟩ := PMF.support_map .. ▸ supported
  have meets : ∃ a ∈ f ⁻¹' {f witness}, a ∈ law.support := ⟨witness, rfl, member⟩
  rw [fiberConditional, dite_eq_left meets]
  exact fun _ reached => ((PMF.mem_support_filter_iff _).mp reached).1

/-- Every response law has an implementation using only past chosen actions.
The policy is defined on all prefixes, including those with zero probability. -/
theorem run_next (law : PMF (List Action)) (count : Nat)
    (lengths : ∀ actions ∈ law.support, actions.length = count) :
    run (next law) count = law := by
  induction count generalizing law with
  | zero =>
      change PMF.pure [] = law
      calc
        _ = law.map (fun _ => []) := (PMF.map_const _ _).symm
        _ = law.map id := map_congr_on_support _ fun actions member => by
          have length := lengths actions member
          cases actions <;> simp_all
        _ = law := PMF.map_id _
  | succ count ih =>
      rw [run]
      change ((law.map (List.headD · default)).bind fun action =>
        (run (next ((fiberConditional law (List.headD · default) action).map List.tail))
          count).map (action :: ·)) = law
      conv_rhs => rw [eq_bind_fiberConditional law (List.headD · default)]
      apply bind_congr_on_support _
      intro action supported
      have remaining : ∀ rest ∈
          ((fiberConditional law (List.headD · default) action).map List.tail).support,
          rest.length = count := by
        intro rest member
        obtain ⟨actions, conditioned, rfl⟩ := PMF.support_map .. ▸ member
        have length := lengths actions (conditioned_support law _ action conditioned)
        simp only [List.length_tail]
        omega
      rw [ih _ remaining, PMF.map_comp]
      calc
        _ = (fiberConditional law (List.headD · default) action).map id := by
          apply map_congr_on_support _
          intro actions member
          have head := conditioned_fibre law (List.headD · default) action supported actions member
          have length := lengths actions (conditioned_support law _ action member)
          cases actions with
          | nil => simp only [List.length_nil] at length; omega
          | cons first rest =>
              change action :: rest = first :: rest
              exact congrArg (· :: rest) head.symm
        _ = _ := PMF.map_id _

end GameTheory.Protocol.ResponseSampling
