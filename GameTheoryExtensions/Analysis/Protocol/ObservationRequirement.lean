/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.ContinuationDecision
import GameTheoryExtensions.Protocol.Knowledge

/-! # Information that a rational continuation must retain

An observation abstraction may merge actual decision information sites only
when the retained response law can maximize all of their posterior rewards.
This constraint uses the game's one fixed utility and the assessment's actual
beliefs. It applies to arbitrary further coarsenings of an observation.

The factorization premise concerns the executed response law, not an action's
syntactic name. A state-aware macro may have one name and execute different
responses in different states. Such a macro does not satisfy the premise and
is not excluded. Conversely, under the premise the result needs no model of
the abstraction's syntax, compiler, or internal state representation.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel.ContinuationDecision

open GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} {M : InformationModel E}
  {utility : Player → E.History → ℝ} {fuel : Nat}
  {State Action Index Observation Coarse : Type*}

/-- Knowledge fixes the posterior reward for every assessment, including
off-path assessments with otherwise unrestricted compatible-history beliefs. -/
theorem expectedReward_of_known
    (decision : M.ContinuationDecision utility fuel State Action)
    (read : E.History → State)
    (reads : ∀ history, decision.state history = read history.1)
    (state : State)
    (known : M.Knows decision.player decision.site.1 (fun history => read history = state))
    (assessment : M.BehavioralAssessment) (action : Action) :
    decision.expectedReward assessment action = decision.reward state action := by
  have posterior : decision.posterior assessment = FinDist.pure state := by
    unfold posterior
    rw [show decision.state = (fun history => read history.1) from funext reads]
    exact known.belief_map_eq_pure read state _
  simp only [expectedReward, posterior, FinDist.expect_pure]

/-- Every observation fiber of actual decisions has a common maximizing
action if the assessment is rational and its executed response depends only
on that observation. Randomization cannot evade this intersection condition.
No finiteness of the index or action carrier is needed. -/
theorem observation_fiber_has_common_maximizer
    (decisions : Index → M.ContinuationDecision utility fuel State Action)
    (observe : Index → Observation)
    (respond : Observation → FinDist Action)
    (assessment : M.BehavioralAssessment)
    (factors : ∀ index, (decisions index).response assessment.strategy = respond (observe index))
    (rational : assessment.IsSequentiallyRationalWithin utility fuel) (index : Index) :
    ∃ action, ∀ other, observe other = observe index → ∀ alternative,
      (decisions other).expectedReward assessment alternative ≤
        (decisions other).expectedReward assessment action := by
  obtain ⟨action, supported⟩ := (respond (observe index)).support_nonempty
  refine ⟨action, fun other same alternative => ?_⟩
  apply (decisions other).rational_support_maximal assessment rational action _ alternative
  rwa [factors other, same]

/-- An information distinction is necessary whenever the two actual
continuations have disjoint posterior maximizers for the fixed utility. -/
theorem observation_separates_incompatible
    (decisions : Index → M.ContinuationDecision utility fuel State Action)
    (observe : Index → Observation)
    (respond : Observation → FinDist Action)
    (assessment : M.BehavioralAssessment)
    (factors : ∀ index, (decisions index).response assessment.strategy = respond (observe index))
    (rational : assessment.IsSequentiallyRationalWithin utility fuel)
    (first second : Index)
    (incompatible : ¬ ∃ action,
      (∀ alternative, (decisions first).expectedReward assessment alternative ≤
        (decisions first).expectedReward assessment action) ∧
      (∀ alternative, (decisions second).expectedReward assessment alternative ≤
        (decisions second).expectedReward assessment action)) :
    observe first ≠ observe second := by
  intro same
  obtain ⟨action, maximal⟩ := observation_fiber_has_common_maximizer
    decisions observe respond assessment factors rational first
  exact incompatible ⟨action, maximal first rfl, maximal second same.symm⟩

/-- Once a further coarsening merges incompatible decisions, no response
factoring through the coarsened observation can be sequentially rational.
This quantifies over arbitrary observation alphabets and decoders. -/
theorem not_rational_of_coarsening_collision
    (decisions : Index → M.ContinuationDecision utility fuel State Action)
    (observe : Index → Observation) (coarsen : Observation → Coarse)
    (respond : Coarse → FinDist Action)
    (assessment : M.BehavioralAssessment)
    (factors : ∀ index, (decisions index).response assessment.strategy =
      respond (coarsen (observe index)))
    (first second : Index) (merged : coarsen (observe first) = coarsen (observe second))
    (incompatible : ¬ ∃ action,
      (∀ alternative, (decisions first).expectedReward assessment alternative ≤
        (decisions first).expectedReward assessment action) ∧
      (∀ alternative, (decisions second).expectedReward assessment alternative ≤
        (decisions second).expectedReward assessment action)) :
    ¬ assessment.IsSequentiallyRationalWithin utility fuel := by
  intro rational
  exact observation_separates_incompatible decisions (coarsen ∘ observe) respond
    assessment factors rational first second incompatible merged

end GameTheory.Protocol.InformationModel.ContinuationDecision
