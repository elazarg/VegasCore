/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFirstPacket
import Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality
import Interaction.ReactiveLocalContinuation

/-! # An actual first late Alice response followed by the incumbent policy

A local law replacement at this actual native information site draws one
response and retains the entire incumbent continuation. Genuine raw opening
aliases and silence are kept; the repair replaces only nongenuine emitted
envelopes with silence. No later response policy is changed.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceFirstResponse

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeAliceFirstDecision LateOpeningRuntimeAliceContinuation

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    alice site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨22, some alice, decision.execution⟩)

include current in
theorem site_information : site.1 =
    some (decision.execution.recall alice, decision.execution.observe app alice) := by
  rw [← representative.2]
  change (rawMenu.signals _ _ _).infoOf alice representative.1.trace = _
  rw [rawMenu.info, current]
  rfl

def responseLaw
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1)) :
    PMF app.Action := law.map (fun choice => choice.1.getD ⟨none⟩)

def finalLaw (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1)) :
    PMF app.Execution :=
  (assessment.belief alice site).bind fun history =>
    (responseLaw weight nonnegative site law).bind fun response =>
      LateOpeningRuntimeAliceFirstPacket.responseLaw weight nonnegative
        (decisionOfInformation weight nonnegative site representative decision current history)
        response (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
          (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)

open Classical in
theorem current_local_law_finish
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1)) :
    ((LateOpeningRuntimeNash.model weight nonnegative).runBehavioralFrom
      (Profile.update (sig := (LateOpeningRuntimeNash.model weight nonnegative).behavioralSignature)
        assessment.strategy alice ((assessment.strategy alice).withLaw site.1 law))
      (2 * LateOpeningRuntimeService.horizon + 1) history.1).map History.state =
      (responseLaw weight nonnegative site law).bind fun response =>
        (LateOpeningRuntimeAliceFirstPacket.responseLaw weight nonnegative
          (decisionOfInformation weight nonnegative site representative decision current history)
          response (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)).map
              app.finished := by
  classical
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  have facts := decisionOfInformation_spec weight nonnegative site representative decision current
    history
  have native := rawMenu.run_local_law_finish_of_information initial
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      assessment.strategy history.1 alice 22 recovered.execution facts.1 site.1 history.2 law
        (2 * LateOpeningRuntimeService.horizon)
          (by rw [facts.1]; change 45 ≤ 53; decide)
  unfold ReactiveApplication.finish ReactiveApplication.resume at native
  simp only [PMF.pure_bind] at native
  exact native

variable (reward forfeit : ℝ) (deposit : Player → ℝ)

def context (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :=
  assessment.truncatedContinuationContext site
    (fun history => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit history.state alice) (2 * LateOpeningRuntimeService.horizon + 1)

open Classical in
theorem context_outcome_law
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1)) :
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      ((assessment.strategy alice).withLaw site.1 law)).map History.state =
    (finalLaw weight nonnegative site representative decision current assessment law).map
      app.finished := by
  dsimp only [context, InformationModel.BehavioralAssessment.truncatedContinuationContext,
    InformationModel.BehavioralAssessment.continuationContextWith,
    GameTheory.Protocol.Context.ofBelief, InformationModel.truncatedRunner]
  rw [PMF.map_bind, finalLaw, PMF.map_bind]
  apply bind_congr_on_support
  intro history _
  rw [current_local_law_finish weight nonnegative site representative decision current]
  rw [PMF.map_bind]

open Classical in
theorem context_value
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1)) :
    (context weight nonnegative site reward forfeit deposit assessment).value
        ((assessment.strategy alice).withLaw site.1 law) =
      expect (finalLaw weight nonnegative site representative decision current assessment law)
        (aliceUtility reward forfeit deposit) := by
  have projected := expect_map History.state
    ((context weight nonnegative site reward forfeit deposit assessment).outcome
      ((assessment.strategy alice).withLaw site.1 law))
    (fun state => LateOpeningRuntimeNash.payoff reward forfeit (fun actual => PMF.pure actual)
      deposit state alice)
  rw [context_outcome_law weight nonnegative site representative decision current,
    expect_map] at projected
  exact projected.symm

theorem context_integrable
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (depositNonnegative : 0 ≤ deposit alice)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (alternative : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy alice) :
    Context.IntegrableAt
      (context weight nonnegative site reward forfeit deposit assessment) alternative :=
  payoffIntegrable_of_bounded _ _ fun history =>
    LateOpeningRuntimeAliceRationality.payoff_bounded reward forfeit deposit
      rewardNonnegative forfeitNonnegative depositNonnegative history.state

def quietChoice : (LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1 := by
  classical
  refine ⟨some ⟨none⟩, ?_⟩
  rw [site_information weight nonnegative site representative decision current]
  refine ⟨⟨none⟩, ?_, rfl⟩
  exact bounds.silent_available LateOpeningRuntimeService.runtime leaks alice _ _

/-- Silence or the complete genuine envelope, with every private alias kept. -/
def PermittedResponse (response : app.Action) : Prop :=
  match response.transmission with
  | none => True
  | some submission => EmitsOpening weight nonnegative decision submission

def repairResponse (response : app.Action) : app.Action := by
  classical
  exact if PermittedResponse weight nonnegative decision response then response else ⟨none⟩

def repairChoice (choice : (LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1) :
    (LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1 := by
  classical
  exact if PermittedResponse weight nonnegative decision (choice.1.getD ⟨none⟩) then choice
    else quietChoice weight nonnegative site representative decision current

theorem repairChoice_response
    (choice : (LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1) :
    (repairChoice weight nonnegative site representative decision current choice).1.getD ⟨none⟩ =
      repairResponse weight nonnegative decision (choice.1.getD ⟨none⟩) := by
  classical
  unfold repairChoice repairResponse
  split <;> rfl

def repairedPolicy
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy alice := by
  classical
  exact (assessment.strategy alice).withLaw site.1
    ((assessment.strategy alice site.1).map
      (repairChoice weight nonnegative site representative decision current))

theorem repaired_responseLaw
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment) :
    responseLaw weight nonnegative site
        ((assessment.strategy alice site.1).map
          (repairChoice weight nonnegative site representative decision current)) =
      (responseLaw weight nonnegative site (assessment.strategy alice site.1)).map
        (repairResponse weight nonnegative decision) := by
  unfold responseLaw
  rw [PMF.map_comp, PMF.map_comp]
  congr 1
  funext choice
  exact repairChoice_response weight nonnegative site representative decision current choice

theorem permitted_of_information
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1)
    (response : app.Action) :
    PermittedResponse weight nonnegative
      (decisionOfInformation weight nonnegative site representative decision current history)
      response ↔ PermittedResponse weight nonnegative decision response := by
  let recovered :=
    decisionOfInformation weight nonnegative site representative decision current history
  have facts := decisionOfInformation_spec weight nonnegative site representative decision current
    history
  have own := app.history_inputRecall initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) decision.trace
  have other := app.history_inputRecall initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) recovered.trace
  change decision.execution.InputRecall app at own
  change recovered.execution.InputRecall app at other
  have known := LateOpeningRuntimeService.runtime.known_eq_of_input_eq leaks
    decision.execution recovered.execution alice own other facts.2.1 facts.2.2.1
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission =>
      have packet := LateOpeningRuntimeService.runtime.response_packet_eq_of_input_eq leaks
        decision.execution recovered.execution alice submission facts.2.2.1 known
      change (_ = (LateOpeningRuntimeLatePrefix.openingMessage recovered.bit).payload) ↔
        (_ = (LateOpeningRuntimeLatePrefix.openingMessage decision.bit).payload)
      change app.packet (app.submit decision.execution.application alice submission) alice
        (decision.execution.network.known alice) submission =
          app.packet (app.submit recovered.execution.application alice submission) alice
            (recovered.execution.network.known alice) submission at packet
      rw [← packet, ← facts.2.2.2]

end Vegas.Examples.LateOpeningRuntimeAliceFirstResponse
