/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceEffectiveImmediateComparator
import Vegas.Game.SourceServiceAuditableCollection
import Vegas.Game.SourceServiceRecordedCollection
import Vegas.Game.AsyncServiceDeposit
import Vegas.Game.SourceServiceFreeRationality
import GameTheoryExtensions.Analysis.Protocol.TerminalAuditContinuation

/-! # Charged continuation comparisons at compatible effective information

A classified packet or repeated response has an actual terminal collection
bound under arbitrary effective continuation policies, at any native input.
One shared immediate comparator has zero owner collection at the same compatible information.
The fixed deposit covers the entire effective-history payoff range, giving
an expected net-utility comparison for every belief on that information fiber.

This compares against the clean whole-policy alternative. It does not prove
that a prescribed current source response dominates, or assert equilibrium.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "runtime" => runtime service.setup
local notation "menu" => service.bounds.menu (runtime) service.leaks
local notation "model" => ReactiveApplication.ResponseMenu.information
  (service.bounds.menu (Vegas.runtime service.setup) service.leaks)
  (initialLaw service.setup) service.horizon service.scheduler


local instance history_nonempty : Nonempty (((menu).protocol (initialLaw service.setup)
    service.horizon service.scheduler).History) :=
  ⟨((menu).protocol (initialLaw service.setup) service.horizon service.scheduler).initHistory⟩

open Classical in
private theorem charged_collection_at_information
    (backend : EvidenceReportService (SettledEvidence service.setup))
    (baseline : ∀ player, (model).BehavioralPolicy player) (who : Player)
    (site : (model).InformationSite who)
    (choice : (model).Choice who site.1)
    (classified : auditableServiceChoice service.setup service.leaks (menu) service.horizon
      service.scheduler who site.1 choice ∨
        recordedServiceChoice service.setup service.leaks (menu) service.horizon
          service.scheduler who site.1 choice)
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (history : (model).InformationHistory who site.1) :
    observationRate who * deliveryRate who ≤
      expect ((model).runBehavioralTerminalFrom
        ((menu).bounded (initialLaw service.setup) service.horizon
          service.scheduler).wellFoundedHistories
        (Profile.update (sig := (model).behavioralSignature) baseline who
          ((baseline who).commit site.1 choice)) history.1)
        (fun final => TerminalAudit.charge ((runtime).serviceAuditObservation service.leaks)
          (sourceServiceAudit service.setup service.leaks backend.sample) final.state who) := by
  have active := InformationModel.InformationSite.active _ site history
  cases current : history.1.state with
  | none =>
      rw [current] at active
      cases active
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      rw [current] at active
      change actor = some who at active
      subst actor
      rcases classified with packet | recorded
      · exact auditableServiceChoice_collection_committed service.setup service.leaks (menu)
          service.horizon service.scheduler service.completes backend baseline history.1 who
          remaining execution current site.1 choice history.2 packet observationRate deliveryRate
          delivery_nonnegative coverage
      · exact recordedServiceChoice_collection_committed (menu) service.horizon service.scheduler
          service.completes backend baseline history.1 who remaining execution current site.1
          choice history.2 recorded observationRate deliveryRate delivery_nonnegative coverage

open Classical in
/-- Actual collection of a classified pure response bounds its entire net
continuation value by the finite base-payoff minimum. No clean comparator or
prescribed source law is needed for this bound. -/
theorem charged_expected_utility_le_lower
    (base : (app).ProtocolState → Player → ℝ)
    (backend : EvidenceReportService (SettledEvidence service.setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (who : Player) (positive : 0 < observationRate who * deliveryRate who)
    (baseline : ∀ player, (model).BehavioralPolicy player)
    (site : (model).InformationSite who)
    (choice : (model).Choice who site.1)
    (classified : auditableServiceChoice service.setup service.leaks (menu) service.horizon
      service.scheduler who site.1 choice ∨
        recordedServiceChoice service.setup service.leaks (menu) service.horizon
          service.scheduler who site.1 choice)
    (belief : PMF ((model).InformationHistory who site.1)) :
    let certificate := ((menu).bounded (initialLaw service.setup) service.horizon
      service.scheduler).wellFoundedHistories
    let probability := fun player => observationRate player * deliveryRate player
    let deposit := service.auditDeposit base probability
    let observe := (runtime).serviceAuditObservation service.leaks
    let audit := sourceServiceAudit service.setup service.leaks backend.sample
    let payoff := TerminalAudit.utility base observe audit deposit
    expect belief (fun history => expect ((model).runBehavioralTerminalFrom certificate
      (Profile.update (sig := (model).behavioralSignature) baseline who
        ((baseline who).commit site.1 choice)) history.1) (fun final => payoff final.state who)) ≤
      FinitePayoffBounds.lower (fun final : ((menu).protocol (initialLaw service.setup)
        service.horizon service.scheduler).History => base final.state who) := by
  intro certificate probability deposit observe audit payoff
  let extremum := fun history : ((menu).protocol (initialLaw service.setup) service.horizon
    service.scheduler).History => base history.state who
  have nonnegative : 0 ≤ deposit who := asyncAuditDeposit_nonnegative service.setup service.leaks
    service.bounds service.horizon service.scheduler base probability who positive
  have sufficient : FinitePayoffBounds.upper extremum - probability who * deposit who ≤
      FinitePayoffBounds.lower extremum := by
    change FinitePayoffBounds.upper extremum - probability who *
      ((FinitePayoffBounds.upper extremum - FinitePayoffBounds.lower extremum) / probability who) ≤
        FinitePayoffBounds.lower extremum
    rw [mul_div_cancel₀ _ positive.ne']
    exact le_of_eq (by ring)
  rw [← expect_constant belief (FinitePayoffBounds.lower extremum)]
  apply expect_mono _ (payoffIntegrable_of_finite _ _) (payoffIntegrable_constant _ _)
  intro history _
  let deviating := (model).runBehavioralTerminalFrom certificate
    (Profile.update (sig := (model).behavioralSignature) baseline who
      ((baseline who).commit site.1 choice)) history.1
  have collected : probability who ≤ expect deviating
      (fun final => TerminalAudit.charge observe audit final.state who) :=
    service.charged_collection_at_information backend baseline who site choice
      classified observationRate deliveryRate delivery_nonnegative coverage history
  have upperBound : expect deviating extremum ≤ FinitePayoffBounds.upper extremum :=
    expect_le_const deviating extremum (payoffIntegrable_of_finite _ _)
      (FinitePayoffBounds.upper extremum)
      (fun final _ => FinitePayoffBounds.le_upper extremum final)
  have audited : expect deviating (fun final => payoff final.state who) =
      expect deviating extremum - expect deviating
        (fun final => TerminalAudit.charge observe audit final.state who) * deposit who :=
    TerminalAudit.expect_utility deviating (fun final => base final.state)
      (fun final => observe final.state) audit deposit who (payoffIntegrable_of_finite _ _)
  rw [audited]
  exact (sub_le_sub upperBound (mul_le_mul_of_nonneg_right collected nonnegative)).trans sufficient

open Classical in
/-- Every charged local choice is bounded by the same clean whole-policy
comparator under any belief at compatible effective information. The future
baseline is arbitrary and need not extend a risk-menu policy. -/
theorem charged_expected_utility_le_immediate
    (base : (app).ProtocolState → Player → ℝ)
    (backend : EvidenceReportService (SettledEvidence service.setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (reference : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (reference who).Admitted service.setup.program (CommitmentInterface.values _))
    (positive : 0 < observationRate who * deliveryRate who)
    (baseline : ∀ player, (model).BehavioralPolicy player)
    (site : (model).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (choice : (model).Choice who site.1)
    (classified : auditableServiceChoice service.setup service.leaks (menu) service.horizon
      service.scheduler who site.1 choice ∨
        recordedServiceChoice service.setup service.leaks (menu) service.horizon
          service.scheduler who site.1 choice)
    (belief : PMF ((model).InformationHistory who site.1)) :
    let certificate := ((menu).bounded (initialLaw service.setup) service.horizon
      service.scheduler).wellFoundedHistories
    let probability := fun player => observationRate player * deliveryRate player
    let deposit := service.auditDeposit base probability
    let observe := (runtime).serviceAuditObservation service.leaks
    let audit := sourceServiceAudit service.setup service.leaks backend.sample
    let payoff := TerminalAudit.utility base observe audit deposit
    expect belief (fun history => expect ((model).runBehavioralTerminalFrom certificate
      (Profile.update (sig := (model).behavioralSignature) baseline who
        ((baseline who).commit site.1 choice)) history.1) (fun final => payoff final.state who)) ≤
    expect belief (fun history => expect ((model).runBehavioralTerminalFrom certificate
      (Profile.update (sig := (model).behavioralSignature) baseline who
        (service.effectiveImmediateComparator reference who)) history.1)
          (fun final => payoff final.state who)) := by
  intro certificate probability deposit observe audit payoff
  have charged := service.charged_expected_utility_le_lower base backend observationRate
    deliveryRate
    delivery_nonnegative coverage who positive baseline site choice classified belief
  exact charged.trans (service.effectiveImmediateComparator_expected_utility_lower base
    backend.sample backend.sample_authentic deposit reference who permitted certificate baseline
      site compatible belief)

open Classical in
/-- Actual compatible pins and free-site comparisons turn the clean
comparator bound into a no-gain comparison against the same assessment,
allowing an arbitrary whole focal continuation after the classified choice.
The backend's collection coverage remains an explicit operational hypothesis. -/
theorem charged_expected_utility_le_assessment
    (base : (app).ProtocolState → Player → ℝ)
    (backend : EvidenceReportService (SettledEvidence service.setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ player, 0 ≤ deliveryRate player)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (reference : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (reference who).Admitted service.setup.program (CommitmentInterface.values _))
    (positive : 0 < observationRate who * deliveryRate who)
    (assessment : (model).BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      ((menu).decisionInformationAntichain (initialLaw service.setup) service.horizon
        service.scheduler))
    (prescribed : ∀ current : (model).InformationSite who,
      service.sourceCompatibleInfo who current.1 →
        assessment.strategy who current.1 =
          service.effectiveImmediateComparator reference who current.1)
    (site : (model).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (choice : (model).Choice who site.1)
    (classified : auditableServiceChoice service.setup service.leaks (menu) service.horizon
      service.scheduler who site.1 choice ∨
        recordedServiceChoice service.setup service.leaks (menu) service.horizon
          service.scheduler who site.1 choice)
    (alternative : (model).BehavioralPolicy who) :
    let certificate := ((menu).bounded (initialLaw service.setup) service.horizon
      service.scheduler).wellFoundedHistories
    let probability := fun player => observationRate player * deliveryRate player
    let deposit := service.auditDeposit base probability
    let observe := (runtime).serviceAuditObservation service.leaks
    let audit := sourceServiceAudit service.setup service.leaks backend.sample
    let payoff := fun player (final : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History) => TerminalAudit.utility base observe audit deposit final.state
        player
    (∀ player (current : (model).InformationSite player),
      ¬ service.sourceCompatibleInfo player current.1 →
      ∀ law : PMF ((model).Choice player current.1),
        (assessment.continuationContext certificate current (payoff player)).value
          ((assessment.strategy player).withLaw current.1 law) ≤
        (assessment.continuationContext certificate current (payoff player)).value
          (assessment.strategy player)) →
    (assessment.continuationContext certificate site (payoff who)).value
        (alternative.commit site.1 choice) ≤
      (assessment.continuationContext certificate site (payoff who)).value
        (assessment.strategy who) := by
  intro certificate probability deposit observe audit payoff freeOptimal
  have comparator := service.sourceCompatibleInfo_agree_continuation_le (menu) assessment
    consistent certificate payoff freeOptimal who site
      (service.effectiveImmediateComparator reference who)
      (fun current compatible => (prescribed current compatible).symm)
  have charged := service.charged_expected_utility_le_immediate base backend observationRate
    deliveryRate delivery_nonnegative coverage reference who permitted positive
      (Profile.update (sig := (model).behavioralSignature) assessment.strategy who alternative)
      site compatible choice classified (assessment.belief who site)
  simp only [Profile.update_same, Profile.update_idem] at charged
  have committedTower := assessment.continuationContextWith_value_tower
    ((model).runBehavioralTerminalFrom certificate) site (payoff who)
    (alternative.commit site.1 choice) (payoffIntegrable_of_finite _ _)
  have comparatorTower := assessment.continuationContextWith_value_tower
    ((model).runBehavioralTerminalFrom certificate) site (payoff who)
    (service.effectiveImmediateComparator reference who) (payoffIntegrable_of_finite _ _)
  exact (committedTower.trans_le (charged.trans_eq comparatorTower.symm)).trans comparator

end Vegas.AsyncServiceSpec
