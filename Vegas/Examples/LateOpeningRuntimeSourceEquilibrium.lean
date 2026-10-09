/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeSourceOptimality
import Vegas.Examples.LateOpeningRuntimeSourceContinuation
import Vegas.Examples.LateOpeningRuntimeSourcePreservation

/-! # The selected equilibrium outcome of the actual source program

The source publishes Alice's initialized bit, privately binds Bob's answer,
and publishes that answer. This module relates its sequential rationality to
the unique safe answer, retaining the initialized state jointly with payoffs.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeSource

open SourceProgram GameTheory GameTheory.Math.Probability GameTheory.Protocol

theorem bobAnswerLaw_update
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (alternative : setup.intendedModel.BehavioralPolicy bob) (bit : Bool) :
    bobAnswerLaw (Profile.update (sig := setup.intendedModel.behavioralSignature)
      profile bob alternative) bit =
        (alternative (bobBindingSite bit).1).map (bobChoiceEquiv bit).symm := by
  simp only [bobAnswerLaw, Profile.update_same]

theorem bobAnswerLaw_fallback
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) (bit : Bool) :
    bobAnswerLaw (Profile.update (sig := setup.intendedModel.behavioralSignature)
      profile bob (fun info => PMF.pure (intendedFallback bob info))) bit = PMF.pure safe := by
  rw [bobAnswerLaw_update, PMF.pure_map]
  change PMF.pure ((bobChoiceEquiv bit).symm (bobChoiceEquiv bit safe)) = _
  rw [Equiv.symm_apply_apply]

theorem bobBinding_context_integrable
    (assessment : setup.intendedModel.BehavioralAssessment) (reward : ℝ) (bit : Bool)
    (alternative : setup.intendedModel.BehavioralPolicy bob) :
    (assessment.continuationContext setup.intended_bounded.wellFoundedHistories
      (bobBindingSite bit) (intendedPayoff reward bob)).IntegrableAt alternative := by
  let : Finite setup.intendedProtocol.History :=
    setup.intended_finite_history finiteBindingTypes
  exact payoffIntegrable_of_finite _ _

theorem parameterOutcome_finalState (bit : Bool) (label : Fin 3) (answer : Answer) :
    setup.parameterOutcome parameter (finalState bit label true answer true) =
      ((bit, label), publicOutcome program (finalState bit label true answer true)) := by
  unfold Setup.parameterOutcome
  change (parameter (sourceInitial bit label), _) = _
  rw [parameter_sourceInitial]
  rfl

def safeTerminalLaw (reward : ℝ) :=
  prior.map (fun initial =>
    (some (finalState initial.1 initial.2 true safe true),
      fun who : Player => if who = alice then reward / 2 else (2 / 5 : ℝ)))

theorem safe_terminal_payoff (reward : ℝ) (bit : Bool) (label : Fin 3) :
    (fun who : Player =>
      grossUtility reward (setup.parameterOutcome parameter
        (finalState bit label true safe true)) who) =
      (fun who : Player => if who = alice then reward / 2 else (2 / 5 : ℝ)) := by
  rw [parameterOutcome_finalState]
  funext who
  fin_cases who
  · exact (intended_gross reward bit label).1
  · exact (intended_gross reward bit label).2

theorem intendedTerminalLaw_of_safe_readout
    (reward : ℝ) (profile : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (law : (setup.intendedModel.runBehavioralTerminalFrom
      setup.intended_bounded.wellFoundedHistories profile setup.intendedProtocol.initHistory).map
        (fun final => setup.protocolReadout final.state) =
      prior.map (fun initial => some (finalState initial.1 initial.2 true safe true))) :
    intendedTerminalLaw reward profile = safeTerminalLaw reward := by
  let joint (terminal : Option (State simpleExpr program.terminalCtx)) :=
    (terminal, fun who : Player => terminal.elim 0 (fun store =>
      grossUtility reward (setup.parameterOutcome parameter store) who))
  have mapped := congrArg (PMF.map joint) law
  rw [PMF.map_comp, PMF.map_comp] at mapped
  refine mapped.trans ?_
  apply map_congr_on_support
  intro initial _
  dsimp only [Function.comp_apply, joint, Option.elim_some]
  rw [safe_terminal_payoff]

theorem bobContinuation_payoff
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (reward : ℝ) (bit : Bool) (label : Fin 3) :
    expect (setup.intendedModel.runBehavioralTerminalFrom
      setup.intended_bounded.wellFoundedHistories profile (openedHistory bit label))
      (intendedPayoff reward bob) =
    expect (bobAnswerLaw profile bit) (fun answer =>
      grossUtility reward ((bit, label),
        publicOutcome program (finalState bit label true answer true)) bob) := by
  let utility (terminal : Option (State simpleExpr program.terminalCtx)) :=
    terminal.elim 0 (fun store =>
      grossUtility reward (setup.parameterOutcome parameter store) bob)
  change expect _ (fun final : setup.intendedProtocol.History =>
    utility (setup.protocolReadout final.state)) = _
  have mapped := expect_map
    (fun final : setup.intendedProtocol.History => setup.protocolReadout final.state)
    (setup.intendedModel.runBehavioralTerminalFrom
      setup.intended_bounded.wellFoundedHistories profile (openedHistory bit label)) utility
  refine mapped.symm.trans ?_
  rw [bobContinuation_readout, expect_map]
  apply expect_congr_on_support
  intro answer _
  change grossUtility reward (setup.parameterOutcome parameter
    (finalState bit label true answer true)) bob = _
  exact congrArg (fun outcome => grossUtility reward outcome bob)
    (parameterOutcome_finalState bit label answer)

/-- Every whole Bob continuation policy has exactly the uniform-label
decision value. Both source publications are mandatory in this game. -/
theorem bobBinding_context_value
    {assessment : setup.intendedModel.BehavioralAssessment}
    (consistent : assessment.IsSequentiallyConsistent
      intended_decisionRecall.decisionInformationAntichain)
    (reward : ℝ) (bit : Bool) (alternative : setup.intendedModel.BehavioralPolicy bob) :
    (assessment.continuationContext setup.intended_bounded.wellFoundedHistories
      (bobBindingSite bit) (intendedPayoff reward bob)).value alternative =
    expect (bobAnswerLaw (Profile.update (sig := setup.intendedModel.behavioralSignature)
      assessment.strategy bob alternative) bit) (bobUniformAnswerValue reward bit) := by
  let : Finite setup.intendedProtocol.History :=
    setup.intended_finite_history finiteBindingTypes
  rw [InformationModel.BehavioralAssessment.continuationContext_value, expect_bind_of_finite,
    consistent_bobBinding_uniform consistent bit, expect_map]
  change (expect (PMF.uniformOfFintype (Fin 3)) (fun label =>
    expect (setup.intendedModel.runBehavioralTerminalFrom
      setup.intended_bounded.wellFoundedHistories
      (Profile.update (sig := setup.intendedModel.behavioralSignature)
        assessment.strategy bob alternative) (openedHistory bit label))
      (intendedPayoff reward bob))) = _
  simp_rw [bobContinuation_payoff]
  exact expect_comm_of_support_finite _ _ (Set.toFinite _) (Set.toFinite _) _

/-- Every actual intended source sequential equilibrium binds the safe
answer. This identifies its outcome rather than selecting an unspecified
equilibrium from the finite existence theorem. -/
theorem intended_equilibrium_bobAnswerLaw
    {assessment : setup.intendedModel.BehavioralAssessment} {reward : ℝ}
    (equilibrium : assessment.IsSequentialEquilibrium
      intended_decisionRecall.decisionInformationAntichain
      setup.intended_bounded.wellFoundedHistories (intendedPayoff reward)) (bit : Bool) :
    bobAnswerLaw assessment.strategy bit = PMF.pure safe := by
  let alternative : setup.intendedModel.BehavioralPolicy bob :=
    fun info => PMF.pure (intendedFallback bob info)
  have optimal := (Context.isLocallyOptimal_iff_of_integrable
    (bobBinding_context_integrable assessment reward bit (assessment.strategy bob))
    (fun policy _ => bobBinding_context_integrable assessment reward bit policy)).mp
      (equilibrium.1 bob (bobBindingSite bit)) alternative (Set.mem_univ _)
  rw [bobBinding_context_value equilibrium.2, bobBinding_context_value equilibrium.2,
    Profile.update_eq_self] at optimal
  change expect (bobAnswerLaw (Profile.update (sig := setup.intendedModel.behavioralSignature)
    assessment.strategy bob (fun info => PMF.pure (intendedFallback bob info))) bit)
      (bobUniformAnswerValue reward bit) ≤ _ at optimal
  rw [bobAnswerLaw_fallback, expect_pure, bobUniformAnswerValue_safe] at optimal
  exact bob_answer_law_eq_pure_safe_of_value_ge reward bit _ optimal

theorem intended_safe_readout_of_bobAnswerLaw
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (safeAnswer : ∀ bit, bobAnswerLaw profile bit = PMF.pure safe) :
    (setup.intendedModel.runBehavioralTerminalFrom
      setup.intended_bounded.wellFoundedHistories profile setup.intendedProtocol.initHistory).map
        (fun final => setup.protocolReadout final.state) =
      prior.map (fun initial => some (finalState initial.1 initial.2 true safe true)) := by
  rw [intendedTerminal_readout]
  simp_rw [safeAnswer, PMF.pure_map]
  exact PMF.bind_pure_comp _ _

theorem intended_equilibrium_terminal_law
    {assessment : setup.intendedModel.BehavioralAssessment} {reward : ℝ}
    (equilibrium : assessment.IsSequentialEquilibrium
      intended_decisionRecall.decisionInformationAntichain
      setup.intended_bounded.wellFoundedHistories (intendedPayoff reward)) :
    intendedTerminalLaw reward assessment.strategy = safeTerminalLaw reward :=
  intendedTerminalLaw_of_safe_readout reward assessment.strategy
    (intended_safe_readout_of_bobAnswerLaw assessment.strategy
      (intended_equilibrium_bobAnswerLaw equilibrium))

/-- The concrete initialized source has a sequential equilibrium with the
exact safe terminal-store and payoff law. -/
theorem exists_intended_equilibrium_with_safe_law (reward : ℝ) :
    ∃ assessment : setup.intendedModel.BehavioralAssessment,
      assessment.IsSequentialEquilibrium intended_decisionRecall.decisionInformationAntichain
        setup.intended_bounded.wellFoundedHistories (intendedPayoff reward) ∧
      intendedTerminalLaw reward assessment.strategy = safeTerminalLaw reward := by
  obtain ⟨assessment, equilibrium⟩ := exists_intended_sequential_equilibrium reward
  exact ⟨assessment, equilibrium, intended_equilibrium_terminal_law equilibrium⟩

/-- The same selected initialized outcome extends to the actual source
withholding game under the stated finite forfeit bounds. -/
theorem exists_withholding_equilibrium_with_safe_law {reward forfeit : ℝ}
    (nonnegative : 0 ≤ reward) (coversAlice : reward ≤ forfeit) (coversBob : 1 ≤ forfeit) :
    ∃ assessment : withholdingModel.BehavioralAssessment,
      assessment.IsSequentialEquilibrium (setup.decision_antichain _)
        withholding_bounded.wellFoundedHistories (withholdingPayoff reward forfeit) ∧
      withholdingTerminalLaw reward forfeit assessment.strategy = safeTerminalLaw reward := by
  obtain ⟨intended, equilibrium, law⟩ := exists_intended_equilibrium_with_safe_law reward
  obtain ⟨assessment, preserved, _, sameLaw⟩ :=
    intended_equilibrium_preserved_under_withholding nonnegative coversAlice coversBob
      intended equilibrium
  exact ⟨assessment, preserved, sameLaw.trans law⟩

end Vegas.Examples.LateOpeningRuntimeSource
