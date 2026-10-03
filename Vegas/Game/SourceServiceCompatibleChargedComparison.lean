/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceEffectiveImmediateComparator
import Vegas.Game.SourceServiceCompatibleCollection
import Vegas.Game.AsyncServiceDeposit
import GameTheoryExtensions.Analysis.Protocol.TerminalAuditContinuation

/-! # Charged continuation comparisons at compatible effective information

A classified packet or repeated response has an actual terminal collection
bound under arbitrary effective continuation policies. One shared immediate
comparator has zero owner collection at the same compatible information.
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
    (compatible : service.sourceCompatibleInfo who site.1)
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
      exact service.sourceCompatibleInfo_charged_collection_committed (menu) backend baseline
        history.1 who remaining execution current site.1 compatible choice history.2 classified
        observationRate deliveryRate delivery_nonnegative coverage

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
  have clean := service.effectiveImmediateComparator_charge_zero_at_information reference who
    permitted certificate baseline site compatible backend.sample backend.sample_authentic
  apply expect_mono _ (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  intro history _
  let deviating := (model).runBehavioralTerminalFrom certificate
    (Profile.update (sig := (model).behavioralSignature) baseline who
      ((baseline who).commit site.1 choice)) history.1
  let comparator := (model).runBehavioralTerminalFrom certificate
    (Profile.update (sig := (model).behavioralSignature) baseline who
      (service.effectiveImmediateComparator reference who)) history.1
  have collected : probability who ≤ expect deviating
      (fun final => TerminalAudit.charge observe audit final.state who) :=
    service.charged_collection_at_information backend baseline who site compatible choice
      classified observationRate deliveryRate delivery_nonnegative coverage history
  have upperBound : expect deviating extremum ≤ FinitePayoffBounds.upper extremum :=
    expect_le_const deviating extremum (payoffIntegrable_of_finite _ _)
      (FinitePayoffBounds.upper extremum)
      (fun final _ => FinitePayoffBounds.le_upper extremum final)
  have lowerBound : FinitePayoffBounds.lower extremum ≤
      expect comparator (fun final => payoff final.state who) := by
    rw [← expect_constant comparator (FinitePayoffBounds.lower extremum)]
    apply expect_mono _ (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
    intro final supported
    have zero := clean history final supported
    change FinitePayoffBounds.lower extremum ≤
      base final.state who - TerminalAudit.charge observe audit final.state who * deposit who
    rw [zero, zero_mul, sub_zero]
    exact FinitePayoffBounds.lower_le extremum final
  have audited : expect deviating (fun final => payoff final.state who) =
      expect deviating extremum - expect deviating
        (fun final => TerminalAudit.charge observe audit final.state who) * deposit who :=
    TerminalAudit.expect_utility deviating (fun final => base final.state)
      (fun final => observe final.state) audit deposit who (payoffIntegrable_of_finite _ _)
  rw [audited]
  exact ((sub_le_sub upperBound (mul_le_mul_of_nonneg_right collected nonnegative)).trans
    sufficient).trans lowerBound

end Vegas.AsyncServiceSpec
