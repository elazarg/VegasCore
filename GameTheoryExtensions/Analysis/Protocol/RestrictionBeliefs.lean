/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.RestrictionExecution
import GameTheoryExtensions.Analysis.Protocol.FixedDepthBayes
import GameTheoryExtensions.Math.Probability.ConditionalDomination
import GameTheoryExtensions.Math.Probability.Convergence
import GameTheoryExtensions.Math.Probability.Support

/-! # Beliefs preserved by a structural action restriction

The local execution embedding gives a corresponding information event. If
target approximants dominate the embedded source laws by sufficiently near-unit
factors, their Bayes beliefs converge to the prescribed source beliefs. The
event can have zero probability in the limiting equilibrium.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability Filter

variable {Player : Type} [Fintype Player] {E T : ExecutionProtocol Player}
  {M : InformationModel E} {N : InformationModel T}

private theorem information_event_meets (assessment : M.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (who : Player) (site : M.InformationSite who)
    (depth : Nat) (clock : InformationSite.CommonDepth M site depth) :
    ∃ history ∈ {history : E.History | M.infoOf who history.trace = site.1},
      history ∈ (M.runBehavioral assessment.strategy depth).support := by
  let witness := site.2.choose
  refine ⟨witness.1, witness.2, ?_⟩
  have supported := mixed.history_supported witness.1.trace
  rwa [clock witness] at supported

private theorem bayes_belief_eq (assessment : M.BehavioralAssessment)
    (who : Player) (site : M.InformationSite who)
    (antichain : site.IsHistoryAntichain)
    (positive : 0 < M.informationMass assessment.strategy who site)
    (bayes : BehavioralAssessment.IsBayesConsistentAt M assessment who site antichain positive) :
    assessment.belief who site = M.bayesBelief assessment.strategy who site antichain positive := by
  ext history
  rw [M.bayesBelief_apply]
  exact bayes history

namespace ActionRestriction

variable (restriction : M.ActionRestriction N)

omit [Fintype Player] in
/-- Embedded source histories reflect the entire retained information event,
including histories not reached by a particular source strategy. -/
theorem information_event_preimage (who : Player) (site : M.InformationSite who) :
    restriction.history ⁻¹'
        {history | N.infoOf who history.trace = (restriction.site who site).1} =
      {history | M.infoOf who history.trace = site.1} := by
  ext history
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, restriction.observed,
    site_val, Function.Embedding.apply_eq_iff_eq]

variable [Finite T.History]

/-- Bayes beliefs on retained sites follow from the actual execution-law bound,
not from an assumed belief translation. One sequence covers every history. -/
theorem retained_beliefs_converge
    (sourceSequence : ℕ → M.BehavioralAssessment)
    (targetSequence : ℕ → N.BehavioralAssessment)
    (sourceAntichain : M.DecisionInformationAntichain)
    (targetAntichain : N.DecisionInformationAntichain)
    (sourceMixed : ∀ n, (sourceSequence n).IsFullyMixed)
    (targetMixed : ∀ n, (targetSequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent M
      (sourceSequence n) sourceAntichain)
    (targetBayes : ∀ n, BehavioralAssessment.IsBayesConsistent N
      (targetSequence n) targetAntichain)
    (who : Player) (site : M.InformationSite who) (depth : Nat)
    (clock : InformationSite.CommonDepth N (restriction.site who site) depth)
    (factor : ℕ → ℝ) (positive : ∀ n, 0 < factor n)
    (atMostOne : ∀ n, factor n ≤ 1)
    (lower : ∀ n history,
      factor n * (((M.runBehavioral (sourceSequence n).strategy depth).map
        restriction.history) history).toReal ≤
          ((N.runBehavioral (targetSequence n).strategy depth) history).toReal)
    (negligible : Tendsto (fun n => (1 - factor n) /
      (factor n * (M.informationMass (sourceSequence n).strategy who site).toReal)) atTop
        (nhds 0))
    (limit : PMF (M.InformationHistory who site.1))
    (converges : PMFConvergesPointwise (fun n => (sourceSequence n).belief who site) limit) :
    PMFConvergesPointwise
      (fun n => (targetSequence n).belief who (restriction.site who site))
      (limit.map (restriction.informationHistory who site)) := by
  classical
  let sourceEvent : Set E.History := {history | M.infoOf who history.trace = site.1}
  let targetEvent : Set T.History :=
    {history | N.infoOf who history.trace = (restriction.site who site).1}
  have sourceClock := restriction.source_commonDepth who site depth clock
  have sourceMeet (n : Nat) := information_event_meets (sourceSequence n)
    (sourceMixed n) who site depth sourceClock
  have targetMeet (n : Nat) := information_event_meets (targetSequence n)
    (targetMixed n) who (restriction.site who site) depth clock
  have preimage : restriction.history ⁻¹' targetEvent = sourceEvent :=
    restriction.information_event_preimage who site
  have encodedMeet (n : Nat) : ∃ history ∈ targetEvent,
      history ∈ ((M.runBehavioral (sourceSequence n).strategy depth).map
        restriction.history).support := by
    obtain ⟨history, observed, supported⟩ := sourceMeet n
    refine ⟨restriction.history history, ?_, ?_⟩
    · change history ∈ restriction.history ⁻¹' targetEvent
      rwa [preimage]
    · rw [PMF.support_map]
      exact ⟨history, supported, rfl⟩
  have sourceConditioned (n : Nat) :
      (((M.runBehavioral (sourceSequence n).strategy depth).map restriction.history).filter
        targetEvent (encodedMeet n)) =
      ((sourceSequence n).belief who site).map
        (fun history => restriction.history history.1) := by
    rw [← map_filter_embedding
      (M.runBehavioral (sourceSequence n).strategy depth) restriction.history
      sourceEvent targetEvent (fun history => by
        change history ∈ restriction.history ⁻¹' targetEvent ↔ history ∈ sourceEvent
        rw [preimage]) (sourceMeet n) (encodedMeet n)]
    rw [← M.bayesBelief_map_eq_filter (sourceSequence n).strategy who site depth
      sourceClock (sourceAntichain who site) (M.informationMass_pos_of_fullSupport _ (sourceMixed
          n) who site)
      (sourceMeet n),
      ← bayes_belief_eq (sourceSequence n) who site (sourceAntichain who site)
        (M.informationMass_pos_of_fullSupport _ (sourceMixed n) who site)
        (sourceBayes n who site (M.informationMass_pos_of_fullSupport _ (sourceMixed n) who site)),
            PMF.map_comp]
    rfl
  have targetConditioned (n : Nat) :
      (N.runBehavioral (targetSequence n).strategy depth).filter targetEvent (targetMeet n) =
        ((targetSequence n).belief who (restriction.site who site)).map Subtype.val := by
    rw [← N.bayesBelief_map_eq_filter (targetSequence n).strategy who
      (restriction.site who site) depth clock (targetAntichain who (restriction.site who site))
      (N.informationMass_pos_of_fullSupport _ (targetMixed n) who (restriction.site who site))
          (targetMeet n),
      ← bayes_belief_eq (targetSequence n) who (restriction.site who site)
        (targetAntichain who (restriction.site who site))
        (N.informationMass_pos_of_fullSupport _ (targetMixed n) who (restriction.site who site))
        (targetBayes n who (restriction.site who site)
          (N.informationMass_pos_of_fullSupport _ (targetMixed n) who (restriction.site who site)))]
  have mass (n : Nat) :
      (((M.runBehavioral (sourceSequence n).strategy depth).map
        restriction.history).toOuterMeasure targetEvent).toReal =
        (M.informationMass (sourceSequence n).strategy who site).toReal := by
    rw [PMF.toOuterMeasure_map_apply, preimage,
      M.informationMass_eq_fixedDepth_toOuterMeasure (sourceSequence n).strategy who site
        depth sourceClock]
  have conditioned := conditional_domination_converges
    (fun n => (M.runBehavioral (sourceSequence n).strategy depth).map restriction.history)
    (fun n => N.runBehavioral (targetSequence n).strategy depth) targetEvent encodedMeet targetMeet
    factor positive atMostOne lower (by simpa only [mass] using negligible)
    (limit.map (fun history => restriction.history history.1)) (by
      simpa only [sourceConditioned] using
        converges.map (fun history => restriction.history history.1))
  rw [show (fun history : M.InformationHistory who site.1 =>
      restriction.history history.1) =
      Subtype.val ∘ restriction.informationHistory who site by rfl,
    ← PMF.map_comp] at conditioned
  intro history
  have point := conditioned history.1
  simpa only [targetConditioned, pmf_map_apply_of_injective _ Subtype.val_injective]
    using point

end ActionRestriction

end GameTheory.Protocol.InformationModel
