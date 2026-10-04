/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceWithholdingCommittedBound
import Vegas.Game.AsyncServiceCounterfactualBeliefs
import Vegas.Game.SourceServiceInitialReadout

/-! # The actual native conditional bound for a first LOW guess

The initial Boolean parameter is read from each real native hidden history.
Committing a withholding packet and allowing every later native response gives
at most the actual conditional LOW-type probability. The denominator contains
the genuine foreign response and nature likelihoods, including their waiting
and free-menu paths. No source posterior or fork path masses are supplied.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)
  (menu : (application service.setup service.leaks).ResponseMenu)

local notation "app" => application service.setup service.leaks
local notation "model" => ReactiveApplication.ResponseMenu.information menu
  (initialLaw service.setup) service.horizon service.scheduler

/-- The same exogenous Boolean read from the immutable actual inputs.
The optional branches are unreachable at a legal acting history. -/
def initialGuessParameter (parameter : State L service.setup.context → Bool)
    (history : (menu.protocol (initialLaw service.setup) service.horizon
      service.scheduler).History) : Bool :=
  history.state.elim false fun control =>
    (sourceInitialReadout service.setup control.execution.application.config).elim false parameter

omit [Fintype Player] in
/-- An actual information history recovers its genuine supported initial draw;
the parameter in the payoff is not a newly selected source witness. -/
theorem initialGuessParameter_history
    (parameter : State L service.setup.context → Bool) (who : Player)
    (site : (model).InformationSite who) (history : (model).InformationHistory who site.1) :
    ∃ control initial,
      history.1.state = some control ∧ initial ∈ service.setup.initialLaw.support ∧
      sourceInitialReadout service.setup control.execution.application.config = some initial ∧
      service.initialGuessParameter menu parameter history.1 = parameter initial := by
  have active := InformationModel.InformationSite.active (model) site history
  cases current : history.1.state with
  | none => rw [current] at active; cases active
  | some control =>
      obtain ⟨initial, supported, read⟩ := sourceInitialReadout_history service.setup service.leaks
        service.horizon service.scheduler control
        (current ▸ menu.toRawTrace (initialLaw service.setup) service.horizon
          service.scheduler history.1.trace)
      exact ⟨control, initial, rfl, supported, read, by
        simp only [initialGuessParameter, current, read, Option.elim_some]⟩

open Classical in
/-- A genuine available LOW response, followed by any whole native policy,
is bounded by the actual LOW-type counterfactual mass at its information site. -/
theorem bayes_withhold_guess_committed_le
    (parameter : State L service.setup.context → Bool)
    (profile : ∀ who, (model).BehavioralPolicy who) (who : Player)
    (site : (model).InformationSite who)
    (positive : 0 < (model).informationMass profile who site)
    (choice : (model).Choice who site.1)
    (material : (app).Submission) (selected : choice.1 = some ⟨some material⟩)
    (event : (graph service.setup).EventId) (payload : L.Ty)
    (outputEq : (graph service.setup).outputLayout event = .publication payload)
    (withheld : material.call.packet = .withhold event)
    (backend : EvidenceReportService (SettledEvidence service.setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (deposit : Player → ℝ) (nonnegative : 0 ≤ deposit who)
    (sufficient : 1 ≤ observationRate who * deliveryRate who * deposit who) :
    let belief := (model).bayesBelief profile who site
      (menu.decisionInformationAntichain (initialLaw service.setup) service.horizon
        service.scheduler who site) positive
    let updated := Profile.update (sig := (model).behavioralSignature) profile who
      ((profile who).commit site.1 choice)
    expect belief (fun history =>
      expect ((model).runBehavioralTerminalFrom
        (menu.bounded (initialLaw service.setup) service.horizon
          service.scheduler).wellFoundedHistories updated history.1)
        (fun final => TerminalAudit.utility
          (fun state _ => sourcePublicationGuessValue service.setup service.leaks event payload
            outputEq (service.initialGuessParameter menu parameter history.1) state)
          ((runtime service.setup).serviceAuditObservation service.leaks)
          (sourceServiceAudit service.setup service.leaks backend.sample)
          deposit final.state who)) ≤
      service.counterfactualInformationMass menu profile who site
        {history | service.initialGuessParameter menu parameter history.1 = false} /
      service.counterfactualInformationMass menu profile who site Set.univ := by
  intro belief updated
  let value := fun history : (model).InformationHistory who site.1 =>
    expect ((model).runBehavioralTerminalFrom
      (menu.bounded (initialLaw service.setup) service.horizon
        service.scheduler).wellFoundedHistories updated history.1)
      (fun final => TerminalAudit.utility
        (fun state _ => sourcePublicationGuessValue service.setup service.leaks event payload
          outputEq (service.initialGuessParameter menu parameter history.1) state)
        ((runtime service.setup).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks backend.sample) deposit final.state who)
  let low : Set ((model).InformationHistory who site.1) :=
    {history | service.initialGuessParameter menu parameter history.1 = false}
  have bound (history : (model).InformationHistory who site.1) :
      value history ≤ low.indicator (fun _ => (1 : ℝ)) history := by
    have active := InformationModel.InformationSite.active (model) site history
    cases current : history.1.state with
    | none => rw [current] at active; cases active
    | some control =>
        rcases control with ⟨remaining, actor, execution⟩
        have acting : actor = some who := by
          rw [current] at active
          change actor = some who at active
          exact active
        subst actor
        have actual := sourceService_withhold_guess_committed_le service.setup service.leaks
          menu service.horizon service.scheduler service.completes profile history.1 who remaining
          execution current site.1 choice history.2 material selected event payload outputEq
          withheld backend observationRate deliveryRate delivery_nonnegative coverage
          (service.initialGuessParameter menu parameter history.1) deposit nonnegative sufficient
        dsimp only [value]
        refine actual.trans_eq ?_
        cases high : service.initialGuessParameter menu parameter history.1 <;> simp [low, high]
  calc
    _ ≤ expect belief (low.indicator (fun _ => (1 : ℝ))) :=
      expect_mono (fun history _supported => bound history)
        (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    _ = (belief.toOuterMeasure low).toReal := expect_indicator belief low
    _ = _ := service.bayesBelief_event_counterfactual menu profile who site positive low

end Vegas.AsyncServiceSpec
