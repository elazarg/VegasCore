/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceImmediateComparator
import Vegas.Game.AsyncServiceDeposit
import Vegas.Game.SourceServiceDoomedCollection
import Vegas.Pending.ReactiveSignedEvidence
import Interaction.ReactiveFiniteAssessment
import GameTheoryExtensions.Analysis.Protocol.LocalizedEnforcement

/-! # The risk-menu restriction of the complete effective runtime

Both games have the actual application, scheduler, observations and horizon.
The restriction preserves complete histories and their actual audited net
payoffs, including nonzero audit charges on retained histories. An excluded effective
choice can occur only at a clear local information site. There the fixed
immediate comparator supplies a clean whole-policy continuation.

Every excluded response at a clear site transmits and is not a conformant
first submission, so committing it dooms its author and the final record
forbids some packet of that author. The asynchronous deposit uses extrema over
this complete effective history space. Authentic coverage of packets forbidden
by the final record remains a separate runtime obligation. The result extends
an audited risk-menu equilibrium; embedding a source-language equilibrium is
separate.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (service : AsyncServiceSpec Player L)

/-- The actual nested-menu action restriction changes no application state,
observation, response or scheduler step. -/
def riskRestriction :
    ((service.bounds.riskMenu (serviceRuntime service.setup service.mode service.deadline)
      service.leaks service.bound).information
      (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).ActionRestriction
      ((service.bounds.menu (serviceRuntime service.setup service.mode service.deadline)
        service.leaks).information
        (serviceInitialLaw service.setup service.mode) service.horizon service.scheduler) :=
  ReactiveApplication.ResponseMenu.IncludedIn.actionRestriction
    (service.bounds.riskMenu_in_effective (serviceRuntime service.setup service.mode
      service.deadline) service.leaks service.bound)
    (serviceInitialLaw service.setup service.mode) service.horizon service.scheduler

/-- An excluded choice has the same concrete recall and view throughout its
information site, and that local view has clear full service risk. Risky sites
already admit every bounded effective response. -/
theorem riskRestriction_extra_clear
    (who : Player)
    (site : ((service.bounds.riskMenu (serviceRuntime service.setup service.mode service.deadline)
      service.leaks
      service.bound).information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).InformationSite who)
    (action : ((service.bounds.menu (serviceRuntime service.setup service.mode service.deadline)
      service.leaks).information
      (serviceInitialLaw service.setup service.mode) service.horizon service.scheduler).Choice who
        ((service.riskRestriction.site who site).1))
    (extra : action ∉ Set.range (service.riskRestriction.choice who site.1)) :
    ∃ past view response,
      site.1 = some (past, view) ∧ action.1 = some response ∧
        response ∈ (service.bounds.menu (serviceRuntime service.setup service.mode
          service.deadline) service.leaks).actions who
          past view ∧
        response ∉ service.bounds.riskActions (serviceRuntime service.setup service.mode
          service.deadline) service.leaks service.bound
          who past view ∧
        (serviceRuntime service.setup service.mode service.deadline).serviceRisk service.leaks
          service.bound who past view = false := by
  let effective := service.bounds.menu (serviceRuntime service.setup service.mode service.deadline)
    service.leaks
  let included := service.bounds.riskMenu_in_effective (serviceRuntime service.setup service.mode
    service.deadline) service.leaks
    service.bound
  rcases site with ⟨info, occurs⟩
  cases info with
  | none =>
      obtain ⟨_, _, response, member⟩ := occurs
      cases member
  | some data =>
      change (effective.information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).Choice
        who (some data) at action
      change action ∉ Set.range ((included.actionRestriction (serviceInitialLaw service.setup
        service.mode)
        service.horizon service.scheduler).choice who (some data)) at extra
      obtain ⟨response, value, available, absent⟩ := included.extra_choice_response
        (serviceInitialLaw service.setup service.mode) service.horizon service.scheduler who data.1
          data.2 action extra
      refine ⟨data.1, data.2, response, rfl, value, available, absent, ?_⟩
      cases risk : (serviceRuntime service.setup service.mode service.deadline).serviceRisk
        service.leaks service.bound who
          data.1 data.2 with
      | false => rfl
      | true =>
          have same := service.bounds.riskActions_of_risk (serviceRuntime service.setup
            service.mode service.deadline) service.leaks
            service.bound who data.1 data.2 risk
          change response ∉ service.bounds.riskActions (serviceRuntime service.setup service.mode
            service.deadline) service.leaks
            service.bound who data.1 data.2 at absent
          exact (absent (same.symm ▸ available)).elim

local instance effectiveHistory_nonempty :
    Nonempty ((service.bounds.menu (serviceRuntime service.setup service.mode service.deadline)
      service.leaks).protocol
      (serviceInitialLaw service.setup service.mode) service.horizon service.scheduler).History :=
  ⟨((service.bounds.menu (serviceRuntime service.setup service.mode service.deadline)
    service.leaks).protocol
    (serviceInitialLaw service.setup service.mode) service.horizon service.scheduler).initHistory⟩

/-- A charged excluded response is classified directly from the information
state and chosen material: a constructor breach, a noncanonical current-event
handle or a current-event guard failure, or any transmission that is not a
conformant first submission. No hidden-history quantification, new runtime
observation or gate is introduced. -/
def auditableBreachAtSite
    (who : Player)
    (site : ((service.bounds.riskMenu (serviceRuntime service.setup service.mode service.deadline)
      service.leaks
      service.bound).information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).InformationSite who)
    (action : ((service.bounds.menu (serviceRuntime service.setup service.mode service.deadline)
      service.leaks).information
      (serviceInitialLaw service.setup service.mode) service.horizon service.scheduler).Choice who
        ((service.riskRestriction.site who site).1)) : Prop :=
  auditableServiceChoice service.setup service.leaks
    (service.bounds.menu (serviceRuntime service.setup service.mode service.deadline)
      service.leaks) service.horizon service.scheduler
    who (service.riskRestriction.site who site).1 action ∨
  doomingServiceChoice service.setup service.leaks
    (service.bounds.menu (serviceRuntime service.setup service.mode service.deadline)
      service.leaks) service.horizon service.scheduler
    who (service.riskRestriction.site who site).1 action

/-- **Every excluded response is charged.** At a clear site the risk menu keeps
silence and every conformant first submission, so an excluded effective
response transmits and is not a conformant first submission. -/
theorem riskRestriction_extra_charged
    (who : Player)
    (site : ((service.bounds.riskMenu (serviceRuntime service.setup service.mode service.deadline)
      service.leaks
      service.bound).information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).InformationSite who)
    (action : ((service.bounds.menu (serviceRuntime service.setup service.mode service.deadline)
      service.leaks).information
      (serviceInitialLaw service.setup service.mode) service.horizon service.scheduler).Choice who
        ((service.riskRestriction.site who site).1))
    (extra : action ∉ Set.range (service.riskRestriction.choice who site.1)) :
    service.auditableBreachAtSite who site action := by
  obtain ⟨past, view, response, observed, chosen, available, absent, clear⟩ :=
    service.riskRestriction_extra_clear who site action extra
  rw [service.bounds.riskActions_of_clear (serviceRuntime service.setup service.mode
    service.deadline) service.leaks service.bound who past view clear] at absent
  refine Or.inr ⟨past, view, response, observed, chosen, ?_, fun conformant => ?_⟩
  · cases sent : response.transmission with
    | none =>
        exfalso
        have silent : response = ⟨none⟩ := by
          cases response
          cases sent
          rfl
        apply absent
        rw [silent]
        exact service.bounds.canonicalActions_subset_clear _ _ who past view
          (service.bounds.silence_canonical _ _ who past view)
    | some material => exact ⟨material, rfl⟩
  · apply absent
    classical
    exact Finset.mem_union_right _
      ((service.bounds.mem_conformantActions _ _ who past view response).mpr
        ⟨available, conformant⟩)

open Classical in
/-- An audited risk-menu SE extends to the complete effective runtime once
backend coverage holds. The source payoff includes actual retained charges.
Structural embedding, finite histories, decision recall, payoff bounds,
deposit sufficiency, the fixed clean comparator and the classification of
every excluded response as charged are derived for this service.

Coverage concerns actual signed evidence forbidden by the final settled
record. Delivery is conditional on the full observation and includes delivery
before the challenge-window bound. This contract implies collection after
each excluded response without independence or a continuation-fuel premise.
Coverage remains a hypothesis. -/
theorem risk_sequentialEquilibrium_extends
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (backend : EvidenceReportService (SettledEvidence service.setup service.mode))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (positive : ∀ who, 0 < observationRate who * deliveryRate who)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (reference : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (reference who).Admitted service.setup.program
      (CommitmentInterface.values _)) :
    let menu := service.bounds.riskMenu (serviceRuntime service.setup service.mode
      service.deadline) service.leaks service.bound
    let effective := service.bounds.menu (serviceRuntime service.setup service.mode
      service.deadline) service.leaks
    let initial := serviceInitialLaw service.setup service.mode
    let count := service.horizon
    let scheduler := service.scheduler
    let restriction := service.riskRestriction
    let sourceCertificate := (menu.bounded initial count scheduler).wellFoundedHistories
    let targetCertificate := (effective.bounded initial count scheduler).wellFoundedHistories
    let probability := fun who => observationRate who * deliveryRate who
    let sample := backend.sample
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks utility
    let deposit := service.auditDeposit base probability
    let audit := serviceSourceAudit service.setup service.mode service.deadline service.leaks sample
    let observe := (serviceRuntime service.setup service.mode
      service.deadline).serviceAuditObservation service.leaks
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∀ source : (menu.information initial count scheduler).BehavioralAssessment,
      source.IsSequentialEquilibrium (menu.decisionInformationAntichain initial count scheduler)
        sourceCertificate (fun who final => payoff final.state who) →
    ∃ target : (effective.information initial count scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (effective.decisionInformationAntichain initial count scheduler)
        targetCertificate (fun who final => payoff final.state who) ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      ((menu.information initial count scheduler).runBehavioralTerminalFrom sourceCertificate
          source.strategy (menu.protocol initial count scheduler).initHistory).map
          restriction.history =
        (effective.information initial count scheduler).runBehavioralTerminalFrom targetCertificate
          target.strategy (effective.protocol initial count scheduler).initHistory ∧
      ((menu.information initial count scheduler).runBehavioralTerminalFrom sourceCertificate
        source.strategy (menu.protocol initial count scheduler).initHistory).bind
          (fun final => (settle final.state).map (fun payoffs => (final.state, payoffs))) =
        ((effective.information initial count scheduler).runBehavioralTerminalFrom
          targetCertificate
          target.strategy (effective.protocol initial count scheduler).initHistory).bind
            (fun final => (settle final.state).map (fun payoffs => (final.state, payoffs))) := by
  classical
  intro menu effective initial count scheduler restriction sourceCertificate targetCertificate
    probability sample base deposit audit observe payoff settle source equilibrium
  let extremum := fun who (history : (effective.protocol initial count scheduler).History) =>
    base history.state who
  have effectiveBounds (who : Player)
      (history : (effective.protocol initial count scheduler).History) :
      FinitePayoffBounds.lower (extremum who) ≤ base history.state who ∧
        base history.state who ≤ FinitePayoffBounds.upper (extremum who) :=
    ⟨FinitePayoffBounds.lower_le (extremum who) history,
      FinitePayoffBounds.le_upper (extremum who) history⟩
  obtain ⟨target, targetSE, agrees, beliefs, histories, _joint⟩ :=
    restriction.sequential_equilibrium_extends_of_local_collection
      (menu.decisionInformationAntichain initial count scheduler)
      sourceCertificate targetCertificate (effective.uniformAssessment initial count scheduler)
      (effective.uniform_fullyMixed initial count scheduler)
      (effective.decisionRecall initial count scheduler)
      (fun who final => payoff final.state who) (fun who final => base final.state who)
      (fun who final => TerminalAudit.charge observe audit final.state who) deposit
      (fun _ _ => rfl) (service.auditableBreachAtSite)
      (fun who _ => FinitePayoffBounds.lower (extremum who))
      (fun who _ => FinitePayoffBounds.upper (extremum who)) (fun who _ => probability who)
      (fun who => asyncAuditDeposit_nonnegative service.setup service.leaks service.bounds
        service.horizon service.scheduler base probability who (positive who))
      (fun who _ _ _ _ => by
        change FinitePayoffBounds.upper (extremum who) - probability who *
          ((FinitePayoffBounds.upper (extremum who) -
            FinitePayoffBounds.lower (extremum who)) / probability who) ≤
              FinitePayoffBounds.lower (extremum who)
        rw [mul_div_cancel₀ _ (positive who).ne']
        exact le_of_eq (by ring))
      (fun _ who _ _ _ _ _ final _ => (effectiveBounds who final).2)
      (fun targetProfile who site action _ breach history => by
        let app := serviceApplication service.setup service.mode service.deadline service.leaks
        have input : ∃ past view, (restriction.site who site).1 = some (past, view) := by
          rcases breach with ⟨past, view, _, input, _⟩ | ⟨past, view, _, input, _⟩
          · exact ⟨past, view, input⟩
          · exact ⟨past, view, input⟩
        obtain ⟨past, view, input⟩ := input
        have observed : (effective.information initial count scheduler).infoOf who
            (restriction.history history.1).trace = (restriction.site who site).1 :=
          (restriction.observed who history.1).trans history.2
        have observedState : app.observe who (restriction.history history.1).state =
            some (past, view) :=
          (effective.info initial count scheduler who
            (restriction.history history.1).trace).symm.trans
            (observed.trans input)
        have active := (app.observe_isSome who (restriction.history history.1).state).mp
          (by rw [observedState]; rfl)
        cases current : (restriction.history history.1).state with
        | none => rw [current] at active; cases active
        | some control =>
            rcases control with ⟨remaining, actor, execution⟩
            rw [current] at active
            change actor = some who at active
            subst actor
            rcases breach with auditable | dooming
            · exact auditableServiceChoice_collection_committed service.setup service.leaks
                effective count scheduler service.completes backend targetProfile
                (restriction.history history.1) who remaining execution current
                (restriction.site who site).1 action observed auditable observationRate
                deliveryRate delivery_nonnegative coverage
            · exact doomingServiceChoice_collection_committed
                effective count scheduler service.completes backend targetProfile
                (restriction.history history.1) who remaining execution current
                (restriction.site who site).1 action observed dooming observationRate
                deliveryRate delivery_nonnegative coverage)
      (fun sourceProfile _ _ who site action extra _ belief => by
        obtain ⟨past, view, _response, observed, _, _, _, clear⟩ :=
          service.riskRestriction_extra_clear who site action extra
        obtain ⟨alternative, _fixed, clean⟩ := sourceServiceImmediateComparator_clean_lower
          service.bounds service.values service.initialValues service.capacity
            service.contract
          service.timely reference who (permitted who) sourceCertificate sourceProfile site past
          view observed clear sample backend.sample_authentic (fun final => base final.state who)
          (FinitePayoffBounds.lower (extremum who))
          (fun final _ => (effectiveBounds who (restriction.history final)).1) belief
        exact ⟨alternative, clean⟩)
      (fun _ _ _ who site action extra uncharged _ =>
        (uncharged (service.riskRestriction_extra_charged who site action extra)).elim)
      source equilibrium
  refine ⟨target, targetSE, agrees, beliefs, histories, ?_⟩
  rw [← histories, PMF.bind_map]
  rfl

end Vegas.AsyncServiceSpec
