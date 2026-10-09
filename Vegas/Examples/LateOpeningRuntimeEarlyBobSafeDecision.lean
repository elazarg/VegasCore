/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeEarlyBobDecision
import Vegas.Examples.LateOpeningRuntimeEarlyBobSafeMenu

/-! # The actual assessment value of quiet followed by Safe

The complete finite-menu deviation executes the checked physical Safe policy
against the incumbent opponent policy. Its native continuation utility is
nonnegative at every hidden history of the early unresolved Bob information
class. The comparison uses the assessment's existing whole-policy context.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeEarlyBobSafeDecision

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeEarlyBobInformation
  LateOpeningRuntimeEarlyBobDecision LateOpeningRuntimeEarlyBobSafeMenu
  LateOpeningRuntimeBobSafeContinuation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def safePlayers
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    Player → app.Policy :=
  Function.update (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy) bob safePolicy

theorem safePlayers_admissible
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (who : Player) :
    rawMenu.Admissible initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who
      (safePlayers weight nonnegative assessment who) := by
  by_cases same : who = bob
  · subst who
    simpa only [safePlayers, Function.update_self] using safePolicy_admissible weight nonnegative
  · intro control _trace _active response supported
    simp only [safePlayers, Function.update_of_ne same] at supported
    exact rawMenu.decode_embedPolicy_covered initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who (assessment.strategy who)
      _ _ response supported

theorem safeProfile_as_restriction
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    Profile.update (sig := (LateOpeningRuntimeNash.model weight nonnegative).behavioralSignature)
      assessment.strategy bob (safeFinitePolicy weight nonnegative) =
    fun who => rawMenu.restrictPolicy initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who
      (safePlayers weight nonnegative assessment who) := by
  classical
  funext who
  by_cases same : who = bob
  · subst who
    simp only [Profile.update_same, safePlayers, Function.update_self, safeFinitePolicy]
  · rw [Profile.update_of_ne _ _ same]
    simp only [safePlayers, Function.update_of_ne same,
      ReactiveApplication.ResponseMenu.decodeProfile]
    exact (rawMenu.restrict_decode_embedPolicy initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative) who (assessment.strategy who)).symm

variable
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨21, some bob, decision.execution⟩)

def safeFinalLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    PMF app.Execution :=
  (assessment.belief bob site).bind fun history =>
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (safePlayers weight nonnegative assessment) 21
      ((decisionOfInformation weight nonnegative site representative decision current
        history).execution.respond app bob ⟨none⟩)

theorem safe_current_continuation_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioralFrom
      (Profile.update (sig := (LateOpeningRuntimeNash.model weight nonnegative).behavioralSignature)
        assessment.strategy bob (safeFinitePolicy weight nonnegative))
      (2 * LateOpeningRuntimeService.horizon + 1) history.1).map History.state =
    (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      (safePlayers weight nonnegative assessment) 21
      ((decisionOfInformation weight nonnegative site representative decision current
        history).execution.respond app bob ⟨none⟩)).map app.finished := by
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  have valid := decisionOfInformation_spec weight nonnegative site representative decision current
    history
  rw [safeProfile_as_restriction weight nonnegative]
  rw [rawMenu.run_restrict_eq_finish initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative)
    (safePlayers weight nonnegative assessment)
    (safePlayers_admissible weight nonnegative assessment)
    _ history.1 (by rw [valid.1]; change 43 ≤ 53; decide), valid.1]
  unfold ReactiveApplication.finish ReactiveApplication.resume
  have quiet : safePolicy (recovered.execution.recall bob)
      (recovered.execution.observe app bob) = PMF.pure ⟨none⟩ := by
    apply safePolicy_silent
    change recovered.execution.application.clock ≠ 3
    rw [recovered.clock weight nonnegative]
    decide
  unfold ReactiveApplication.invoke
  change (((safePlayers weight nonnegative assessment bob (recovered.execution.recall bob)
    (recovered.execution.observe app bob)).map (fun response =>
      recovered.execution.respond app bob response)).bind
        (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (safePlayers weight nonnegative assessment) 21)).map app.finished = _
  simp only [safePlayers, Function.update_self, quiet, PMF.pure_map, PMF.pure_bind]
  rfl

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

theorem safe_context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (safeFinitePolicy weight nonnegative)).map History.state =
    (safeFinalLaw weight nonnegative site representative decision current assessment).map
      app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, safeFinalLaw, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  exact safe_current_continuation_law weight nonnegative site representative decision current
    assessment history

theorem safe_context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (context weight nonnegative site reward forfeit deposit assessment).value
      (safeFinitePolicy weight nonnegative) =
    expect (safeFinalLaw weight nonnegative site representative decision current assessment)
      (utility reward forfeit deposit) := by
  have mapped := expect_map History.state
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      (safeFinitePolicy weight nonnegative))
    (fun state => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit state bob)
  rw [safe_context_outcome_law weight nonnegative site representative decision current,
    expect_map] at mapped
  exact mapped.symm

include representative decision current in
theorem safe_context_nonnegative
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    0 ≤ (context weight nonnegative site reward forfeit deposit assessment).value
      (safeFinitePolicy weight nonnegative) := by
  rw [safe_context_value weight nonnegative site representative decision current]
  apply expect_nonneg
  intro final reached
  obtain ⟨history, _, sampled⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  exact safe_continuation_nonnegative weight nonnegative
    (safePlayers weight nonnegative assessment) (by simp only [safePlayers, Function.update_self])
    recovered.execution final recovered.trace recovered.emptyRecall recovered.unresolved
    reward forfeit deposit (fun actual => PMF.pure actual)
    (by
      intro actual observed supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact List.Subset.refl _) sampled

end Vegas.Examples.LateOpeningRuntimeEarlyBobSafeDecision
