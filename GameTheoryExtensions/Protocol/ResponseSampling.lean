/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.FinDist

/-! # Sequential sampling of correlated responses

Any finitely supported law of fixed-length action lists can be sampled one
action at a time, using just the already chosen prefix. Conditioning retains
arbitrary correlations. No cost or extra observation is introduced.
-/

noncomputable section

namespace GameTheory.Protocol.ResponseSampling

open GameTheory.Math.Probability

variable {Action : Type*} [Inhabited Action]

def next (law : FinDist (List Action)) : List Action → FinDist Action
  | [] => law.map (List.headD · default)
  | action :: past =>
      next ((law.condOnFibre (List.headD · default) action).map List.tail) past

def run (policy : List Action → FinDist Action) : Nat → FinDist (List Action)
  | 0 => FinDist.pure []
  | count + 1 => (policy []).bind fun action =>
      (run (fun past => policy (action :: past)) count).map (action :: ·)

private theorem conditioned_support {α β : Type*} (law : FinDist α) (f : α → β) (b : β) :
    (law.condOnFibre f b).support ⊆ law.support := by
  classical
  unfold FinDist.condOnFibre
  split
  · exact fun _ member => (FinDist.support_condOn _ _ _ member).2
  · exact Set.Subset.refl _

private theorem conditioned_fibre {α β : Type*} (law : FinDist α) (f : α → β) (b : β)
    (supported : b ∈ (law.map f).support) :
    ∀ a ∈ (law.condOnFibre f b).support, f a = b := by
  classical
  obtain ⟨witness, member, rfl⟩ := FinDist.support_map .. ▸ supported
  have meets : ∃ a ∈ f ⁻¹' {f witness}, a ∈ law.support := ⟨witness, rfl, member⟩
  rw [FinDist.condOnFibre, dite_eq_left meets]
  exact fun _ reached => (FinDist.support_condOn _ _ _ reached).1

/-- Every response law has an implementation using only past chosen actions.
The policy is defined on all prefixes, including those with zero probability. -/
theorem run_next (law : FinDist (List Action)) (count : Nat)
    (lengths : ∀ actions ∈ law.support, actions.length = count) :
    run (next law) count = law := by
  induction count generalizing law with
  | zero =>
      change FinDist.pure [] = law
      calc
        _ = law.map (fun _ => []) := (FinDist.map_const _ _).symm
        _ = law.map id := FinDist.map_congr_of_eq_on_support fun actions member => by
          have length := lengths actions member
          cases actions <;> simp_all
        _ = law := FinDist.map_id _
  | succ count ih =>
      rw [run]
      change ((law.map (List.headD · default)).bind fun action =>
        (run (next ((law.condOnFibre (List.headD · default) action).map List.tail))
          count).map (action :: ·)) = law
      conv_rhs => rw [FinDist.eq_bind_condOnFibre law (List.headD · default)]
      apply FinDist.bind_congr
      intro action supported
      have remaining : ∀ rest ∈
          ((law.condOnFibre (List.headD · default) action).map List.tail).support,
          rest.length = count := by
        intro rest member
        obtain ⟨actions, conditioned, rfl⟩ := FinDist.support_map .. ▸ member
        have length := lengths actions (conditioned_support law _ action conditioned)
        simp only [List.length_tail]
        omega
      rw [ih _ remaining, FinDist.map_comp]
      calc
        _ = (law.condOnFibre (List.headD · default) action).map id := by
          apply FinDist.map_congr_of_eq_on_support
          intro actions member
          have head := conditioned_fibre law (List.headD · default) action supported actions member
          have length := lengths actions (conditioned_support law _ action member)
          cases actions with
          | nil => simp only [List.length_nil] at length; omega
          | cons first rest =>
              change action :: rest = first :: rest
              exact congrArg (· :: rest) head.symm
        _ = _ := FinDist.map_id _

end GameTheory.Protocol.ResponseSampling
