/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeGame
import Vegas.Examples.LateOpeningRuntimeEarlyBobRationality
import Vegas.Examples.LateOpeningRuntimeLabelBeliefs
import Interaction.ReactiveEquilibriumExistence
import GameTheoryExtensions.Analysis.Protocol.PrescribedCompletion
import GameTheory.Analysis.Protocol.BeliefTransport

/-! # Sequential-equilibrium existence in the actual late-opening runtime

The complete bounded raw menu, initialized prior, partial pending observations
and public lottery builder define a finite decision-recall game. It has a
sequential equilibrium for every finite lottery weight and every audit payoff.
Existence does not imply preservation of a specified source equilibrium law.
Against a fixed full Bob policy, coherent completion makes Alice rational
at all legal sites while retaining Bob's decision laws. Bob's optimality and
the selected initialized terminal law remain separate obligations.
A separate completion fixes Alice to full-menu uniform play and makes Bob
rational at every legal fiber, with uniform private-label beliefs even
at information sites with zero initialized reach.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeEquilibrium

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeGame

/-- The actual partially public runtime has a sequential equilibrium, with
all bounded raw deviations available. No payoff-sign, collateral-margin or
authentic-audit hypothesis is needed for finite-game existence. -/
theorem exists_sequential_equilibrium (weight : ℝ) (nonnegative : 0 ≤ weight)
    (reward forfeit : ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ) :
    ∃ assessment : (model weight nonnegative).BehavioralAssessment,
      assessment.IsSequentialEquilibrium
        (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain
        (rawMenu.bounded initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
        (fun who history => payoff reward forfeit sample deposit history.state who) :=
  rawMenu.exists_sequentialEquilibrium initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
    (fun who history => payoff reward forfeit sample deposit history.state who)


/-- Against any fixed full native Bob policy, Alice has a coherent rational
completion on all legal information fibers. Bob's decision laws are retained.
The assessment obeys Bayes' rule wherever initialized play has positive mass;
neither Bob's rationality nor a prescribed terminal law is claimed. -/
theorem exists_consistent_alice_completion (weight : ℝ) (nonnegative : 0 ≤ weight)
    (reward forfeit : ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ)
    (policy : (model weight nonnegative).BehavioralPolicy bob) :
    ∃ assessment : (model weight nonnegative).BehavioralAssessment,
      assessment.IsSequentiallyConsistent
        (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain ∧
      InformationModel.BehavioralAssessment.IsBayesConsistent (model weight nonnegative)
        assessment (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain ∧
      (∀ site : (model weight nonnegative).InformationSite bob,
        assessment.strategy bob site.1 = policy site.1) ∧
      ∀ site : (model weight nonnegative).InformationSite alice,
        assessment.IsSequentiallyRationalAt site
          (assessment.continuationContext
            (rawMenu.bounded initial LateOpeningRuntimeService.horizon
              (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories site
            (fun history => payoff reward forfeit sample deposit history.state alice)) := by
  classical
  let prescribed : ∀ who, (model weight nonnegative).BehavioralPolicy who := fun who =>
    if same : who = bob then same.symm ▸ policy
    else rawMenu.uniformPolicy initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who
  obtain ⟨assessment, consistent, kept, rational⟩ :=
    (model weight nonnegative).exists_consistent_player_completion
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative))
      (fun who info => Classical.choice (inferInstance :
        Nonempty ((model weight nonnegative).Choice who info)))
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => payoff reward forfeit sample deposit history.state who)
      {alice} prescribed
  refine ⟨assessment, consistent, consistent.isBayesConsistent _, ?_, ?_⟩
  · intro site
    simpa [prescribed] using kept bob site (by decide)
  · exact rational alice (by simp)

/-- With Alice uniform on the actual full raw menu, Bob has a coherent whole-policy
rational completion. Its genuine Bayes approximation retains Alice exactly and
its limiting private-label posterior is uniform at every legal Bob fiber. -/
theorem exists_uniform_alice_bob_completion (weight : ℝ) (nonnegative : 0 ≤ weight)
    (reward forfeit : ℝ)
    (sample : List (SettledEvidence setup .sequential) →
      PMF (List (SettledEvidence setup .sequential))) (deposit : Player → ℝ) :
    ∃ (sequence : ℕ → (model weight nonnegative).BehavioralAssessment)
        (assessment : (model weight nonnegative).BehavioralAssessment),
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
        (model weight nonnegative) (sequence n)
        (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain) ∧
      InformationModel.BehavioralAssessmentConvergesPointwise sequence assessment ∧
      (∀ n (site : (model weight nonnegative).InformationSite alice),
        (sequence n).strategy alice site.1 =
          rawMenu.uniformPolicy initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) alice site.1) ∧
      assessment.IsSequentiallyConsistent
        (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain ∧
      InformationModel.BehavioralAssessment.IsBayesConsistent (model weight nonnegative)
        assessment (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain ∧
      (∀ site : (model weight nonnegative).InformationSite alice,
        assessment.strategy alice site.1 =
          rawMenu.uniformPolicy initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) alice site.1) ∧
      (∀ site : (model weight nonnegative).InformationSite bob,
        assessment.IsSequentiallyRationalAt site
          (assessment.continuationContext
            (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
            site (fun history => payoff reward forfeit sample deposit history.state bob))) ∧
      ∀ site : (model weight nonnegative).InformationSite bob,
        (assessment.belief bob site).map (fun history =>
          LateOpeningRuntimeLabelBeliefs.historyLabel LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) history.1) =
          PMF.uniformOfFintype (Fin 3) := by
  classical
  obtain ⟨sequence, assessment, mixed, bayes, converges, keptSequence,
      consistent, kept, rational⟩ :=
    (model weight nonnegative).exists_consistent_full_support_player_completion
      (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative))
      (fun who info => Classical.choice (inferInstance :
        Nonempty ((model weight nonnegative).Choice who info)))
      (rawMenu.bounded initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
      (fun who history => payoff reward forfeit sample deposit history.state who)
      {bob} (rawMenu.uniformPolicy initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative))
      (fun who site _ => rawMenu.uniform_fullyMixed initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) who site)
  have uniformSequence (n : ℕ) : ((sequence n).strategy alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) alice) := by
    funext site
    exact keptSequence n alice site (by decide)
  refine ⟨sequence, assessment, mixed, bayes, converges, ?_, consistent,
    consistent.isBayesConsistent _, ?_, rational bob (by simp), ?_⟩
  · intro n site
    exact keptSequence n alice site (by decide)
  · intro site
    exact kept alice site (by decide)
  · exact LateOpeningRuntimeLabelBeliefs.label_belief_uniform_of_uniform_sequence
      LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      sequence assessment mixed bayes converges
      uniformSequence

/-- Under full traffic audit, a coherent label-uniform Bob reference is silent
at every actual unresolved first callback. Alice is fixed uniformly, with no
claim that she is optimal or that this is the selected initialized law. -/
theorem exists_uniform_bob_reference (weight : ℝ) (nonnegative : 0 ≤ weight)
    (reward forfeit : ℝ) (deposit : Player → ℝ)
    (forfeitNonnegative : 0 ≤ forfeit) (collateral : 1 < deposit bob) :
    ∃ assessment : (model weight nonnegative).BehavioralAssessment,
      assessment.IsSequentiallyConsistent
        (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain ∧
      InformationModel.BehavioralAssessment.IsBayesConsistent (model weight nonnegative)
        assessment (rawMenu.decisionRecall initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative)).decisionInformationAntichain ∧
      (∀ site : (model weight nonnegative).InformationSite alice,
        assessment.strategy alice site.1 =
          rawMenu.uniformPolicy initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) alice site.1) ∧
      (∀ site : (model weight nonnegative).InformationSite bob,
        assessment.IsSequentiallyRationalAt site
          (assessment.continuationContext
            (rawMenu.bounded initial LateOpeningRuntimeService.horizon
              (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
            site (fun history => payoff reward forfeit (fun actual => PMF.pure actual)
              deposit history.state bob))) ∧
      (∀ site : (model weight nonnegative).InformationSite bob,
        (assessment.belief bob site).map (fun history =>
          LateOpeningRuntimeLabelBeliefs.historyLabel LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) history.1) =
          PMF.uniformOfFintype (Fin 3)) ∧
      ∀ (site : (model weight nonnegative).InformationSite bob)
          (representative : (model weight nonnegative).InformationHistory bob site.1)
          (decision : LateOpeningRuntimeEarlyBobInformation.DecisionHistory weight nonnegative),
        representative.1.state = some ⟨21, some bob, decision.execution⟩ →
          LateOpeningRuntimeEarlyBobDecision.responseLaw weight nonnegative site
            (assessment.strategy bob site.1) = PMF.pure ⟨none⟩ := by
  obtain ⟨sequence, assessment, _, _, _, _, consistent, bayes, uniform, rational, labels⟩ :=
    exists_uniform_alice_bob_completion weight nonnegative reward forfeit
      (fun actual => PMF.pure actual) deposit
  refine ⟨assessment, consistent, bayes, uniform, rational, labels, ?_⟩
  intro site representative decision current
  apply LateOpeningRuntimeEarlyBobRationality.rational_early_response_law weight nonnegative
    site representative decision current reward forfeit deposit forfeitNonnegative collateral
    assessment
  have localRational := rational site
  rw [assessment.continuationContext_eq_truncated_of_bounded
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).wellFoundedHistories
    (rawMenu.bounded initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative))] at localRational
  exact localRational

end Vegas.Examples.LateOpeningRuntimeEquilibrium
