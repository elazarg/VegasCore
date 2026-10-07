/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRiskExtension
import Vegas.Game.IntendedAuditedOutcome
import Vegas.Game.SourceServiceChoiceSupport
import GameTheoryExtensions.Analysis.Protocol.CopiedSiteLimit

/-! # From a native component family to an effective-runtime equilibrium

The source is the intended game under its audited utility: the forfeited
payoff of the public outcome, minus the deposit for each collected charge, and
no charge on the source side. The target is the risk-menu model of an
asynchronous service, observed through its typed readout and its expected
collection vector. Given, for every fully mixed Bayes sequence converging to an
intended sequential equilibrium, a pooled component family on the risk-menu
model with its obligations (`PooledLimitCertificate`), the limit theorem gives a
risk-menu sequential equilibrium with the intended law of readout and charges;
the zero source charges make every native path charge-free and realize the
intended payoff as settlement; and the risk-menu extension carries the
equilibrium, its terminal law and its settlement law to the complete effective
runtime. Every dependency mode and configured deadline is covered.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (service : AsyncServiceSpec Player L)

omit [Fintype Player] in
/-- The intended game of a service has finitely many histories. -/
instance intendedHistory_finite [Finite Player] :
    Finite service.setup.intendedProtocol.History :=
  service.setup.intended_finite_history
    (sourceService_finiteBindingTypes service.setup service.bounds service.values)

/-- The retained native model: the risk menu of the configured runtime. -/
abbrev riskModel :=
  (service.bounds.riskMenu (serviceRuntime service.setup service.mode service.deadline)
    service.leaks service.bound).information (serviceInitialLaw service.setup service.mode)
    service.horizon service.scheduler

/-- The native audited outcome: the typed readout and the expected collection
of every player under a sampling backend. -/
def nativeAuditedOutcome
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (history : ((service.bounds.riskMenu (serviceRuntime service.setup service.mode
      service.deadline) service.leaks service.bound).protocol
      (serviceInitialLaw service.setup service.mode) service.horizon
      service.scheduler).History) : service.setup.AuditedOutcome :=
  (serviceSourceReadout service.setup service.mode service.deadline service.leaks history.state,
    fun who => TerminalAudit.charge ((serviceRuntime service.setup service.mode
      service.deadline).serviceAuditObservation service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample)
      history.state who)

open Classical in
/-- **Composition into the effective runtime.** For a well-formed setup, every
sequential equilibrium of the intended game, and a pooled component family on
the risk-menu model for every fully mixed Bayes sequence converging to it,
there is a sequential equilibrium of the complete effective runtime, under the
audited payoff with the forfeited utility, whose joint law of typed readout and
realized settlement is the intended law of readout and payoff, and that charges
no player on its paths. Besides the component family, the only runtime
hypothesis is backend coverage of packets forbidden by the final record. -/
theorem intended_effective_sequentialEquilibrium_of_certificate
    (wellFormed : service.setup.WellFormed) {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ) (forfeit : ℝ)
    (backend : EvidenceReportService (SettledEvidence service.setup service.mode))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (positive : ∀ who, 0 < observationRate who * deliveryRate who)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (reference : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (reference who).Admitted service.setup.program
      (CommitmentInterface.values _)) :
    let forfeited := fun terminal : State L service.setup.program.terminalCtx =>
      forfeitUtility service.setup.program forfeit utility
        (service.setup.parameterOutcome parameter terminal)
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      forfeited
    let deposit := service.auditDeposit base (fun who => observationRate who * deliveryRate who)
    let effective := service.bounds.menu (serviceRuntime service.setup service.mode
      service.deadline) service.leaks
    let initial := serviceInitialLaw service.setup service.mode
    let observe := (serviceRuntime service.setup service.mode
      service.deadline).serviceAuditObservation service.leaks
    let audit := serviceSourceAudit service.setup service.mode service.deadline service.leaks
      backend.sample
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∀ intended : service.setup.intendedModel.BehavioralAssessment,
      intended.IsSequentialEquilibrium service.setup.intended_decision_antichain
        service.setup.intended_bounded.wellFoundedHistories
        (fun who final => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who)) →
      (∀ sequence : ℕ → service.setup.intendedModel.BehavioralAssessment,
        (∀ n, (sequence n).IsFullyMixed) →
        (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
          service.setup.intendedModel (sequence n) service.setup.intended_decision_antichain) →
        InformationModel.BehavioralAssessmentConvergesPointwise sequence intended →
        InformationModel.PooledLimitCertificate (N := service.riskModel)
          service.setup.intendedOutcome (service.nativeAuditedOutcome backend.sample)
          (instructionCount service.setup.program + 1) (2 * service.horizon + 1)
          ((service.bounds.riskMenu (serviceRuntime service.setup service.mode
            service.deadline) service.leaks service.bound).bounded initial service.horizon
            service.scheduler)
          ((service.bounds.riskMenu (serviceRuntime service.setup service.mode
            service.deadline) service.leaks service.bound).decisionRecall initial
            service.horizon service.scheduler)
          (service.setup.auditedUtility parameter utility forfeit deposit) sequence) →
      ∃ target : (effective.information initial service.horizon
          service.scheduler).BehavioralAssessment,
        target.IsSequentialEquilibrium
          (effective.decisionInformationAntichain initial service.horizon service.scheduler)
          (effective.bounded initial service.horizon service.scheduler).wellFoundedHistories
          (fun who final => payoff final.state who) ∧
        (∀ final ∈ ((effective.information initial service.horizon
            service.scheduler).runBehavioralTerminalFrom
            (effective.bounded initial service.horizon service.scheduler).wellFoundedHistories
            target.strategy (effective.protocol initial service.horizon
              service.scheduler).initHistory).support,
          ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
        ((effective.information initial service.horizon
            service.scheduler).runBehavioralTerminalFrom
            (effective.bounded initial service.horizon service.scheduler).wellFoundedHistories
            target.strategy (effective.protocol initial service.horizon
              service.scheduler).initHistory).bind
          (fun final => (settle final.state).map (fun payoffs =>
            (serviceSourceReadout service.setup service.mode service.deadline service.leaks
              final.state, payoffs))) =
          (service.setup.intendedModel.runBehavioral intended.strategy
              (instructionCount service.setup.program + 1)).map
            (fun final => (service.setup.protocolReadout final.state,
              fun who => (service.setup.protocolReadout final.state).elim 0
                (fun state => utility (service.setup.parameterOutcome parameter state) who))) := by
  intro forfeited base deposit effective initial observe audit payoff settle intended
    equilibrium certificate
  classical
  let menu := service.bounds.riskMenu (serviceRuntime service.setup service.mode
    service.deadline) service.leaks service.bound
  let bounded := menu.bounded initial service.horizon service.scheduler
  obtain ⟨sequence, mixed, bayes, converges, rational⟩ :=
    service.setup.intended_auditedSource wellFormed parameter utility forfeit deposit intended
      equilibrium
  obtain ⟨native, nativeSE, law⟩ :=
    (certificate sequence mixed bayes converges).exists_sequentialEquilibrium intended converges
      rational
  have nativeEquilibrium : native.IsSequentialEquilibrium
      (menu.decisionInformationAntichain initial service.horizon service.scheduler)
      bounded.wellFoundedHistories (fun who final => payoff final.state who) :=
    (native.isSequentialEquilibrium_iff_truncated_of_bounded _ _ bounded.wellFoundedHistories
      bounded _).mpr nativeSE
  obtain ⟨target, targetSE, _, _, histories, settlements⟩ :=
    service.risk_sequentialEquilibrium_extends forfeited backend observationRate deliveryRate
      delivery_nonnegative positive coverage reference permitted native nativeEquilibrium
  let riskLaw :=
      (menu.information initial service.horizon service.scheduler).runBehavioralTerminalFrom
    bounded.wellFoundedHistories native.strategy
    (menu.protocol initial service.horizon service.scheduler).initHistory
  let sourceLaw := service.setup.intendedModel.runBehavioral intended.strategy
    (instructionCount service.setup.program + 1)
  have riskLawEq : riskLaw = (menu.information initial service.horizon
      service.scheduler).runBehavioral native.strategy (2 * service.horizon + 1) :=
    InformationModel.runBehavioralTerminalFrom_initHistory _ _ _ bounded
  have equal : (riskLaw.map History.state).map (fun outcome =>
      (serviceSourceReadout service.setup service.mode service.deadline service.leaks outcome,
        fun who => TerminalAudit.charge observe audit outcome who)) =
      sourceLaw.map (fun final => (service.setup.protocolReadout final.state,
        (0 : Player → ℝ))) := by
    rw [PMF.map_comp, riskLawEq]
    exact law
  obtain ⟨clean, joint⟩ := TerminalAudit.clean_of_law_eq base observe audit deposit
    (serviceSourceReadout service.setup service.mode service.deadline service.leaks)
    (fun readout who => readout.elim 0 (fun terminal => forfeited terminal who))
    (fun _ => rfl) (riskLaw.map History.state) sourceLaw
    (fun final => service.setup.protocolReadout final.state) equal
  refine ⟨target, targetSE, fun final supported who => ?_, ?_⟩
  · rw [← histories, PMF.support_map] at supported
    obtain ⟨original, member, rfl⟩ := supported
    exact clean original.state ((PMF.mem_support_map_iff _ _ _).mpr ⟨original, member, rfl⟩) who
  · have pairs := congrArg (PMF.map (Prod.map (serviceSourceReadout service.setup service.mode
      service.deadline service.leaks) id)) settlements
    simp only [PMF.map_bind, PMF.map_comp] at pairs
    have plain : (fun final : service.setup.intendedProtocol.History =>
        (service.setup.protocolReadout final.state,
          fun who => (service.setup.protocolReadout final.state).elim 0
            (fun terminal => forfeited terminal who))) =
        (fun final => (service.setup.protocolReadout final.state,
          fun who => (service.setup.protocolReadout final.state).elim 0
            (fun state => utility (service.setup.parameterOutcome parameter state) who))) := by
      funext final
      refine Prod.ext rfl (funext fun who => ?_)
      have same := service.setup.intended_auditedUtility wellFormed parameter utility forfeit
        deposit final who
      simpa [Setup.auditedUtility, Setup.intendedOutcome] using same
    rw [← plain, ← joint, PMF.bind_map]
    convert pairs.symm using 2
    all_goals rfl

omit [Fintype Player] in
/-- The typed readout ignores private response normalization. -/
theorem serviceSourceReadout_normalization
    (state : (serviceApplication service.setup service.mode service.deadline
      service.leaks).ProtocolState) :
    serviceSourceReadout service.setup service.mode service.deadline service.leaks
        (((serviceRuntime service.setup service.mode service.deadline).reactiveNormalization
          service.leaks).state state) =
      serviceSourceReadout service.setup service.mode service.deadline service.leaks state := by
  cases state <;> rfl

open Classical in
/-- **Composition into the bounded raw runtime.** Under the hypotheses of
`intended_effective_sequentialEquilibrium_of_certificate`, there is a sequential
equilibrium of the bounded raw runtime, under the same audited payoff, whose
joint law of typed readout and realized settlement is the intended law of
readout and payoff, and that charges no player on its paths. The raw
equilibrium plays the canonical normal form of the effective one. -/
theorem intended_raw_sequentialEquilibrium_of_certificate
    (wellFormed : service.setup.WellFormed) {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ) (forfeit : ℝ)
    (backend : EvidenceReportService (SettledEvidence service.setup service.mode))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (positive : ∀ who, 0 < observationRate who * deliveryRate who)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (reference : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (reference who).Admitted service.setup.program
      (CommitmentInterface.values _)) :
    let forfeited := fun terminal : State L service.setup.program.terminalCtx =>
      forfeitUtility service.setup.program forfeit utility
        (service.setup.parameterOutcome parameter terminal)
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      forfeited
    let deposit := service.auditDeposit base (fun who => observationRate who * deliveryRate who)
    let raw := service.bounds.rawMenu (serviceRuntime service.setup service.mode
      service.deadline) service.leaks
    let initial := serviceInitialLaw service.setup service.mode
    let observe := (serviceRuntime service.setup service.mode
      service.deadline).serviceAuditObservation service.leaks
    let audit := serviceSourceAudit service.setup service.mode service.deadline service.leaks
      backend.sample
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∀ intended : service.setup.intendedModel.BehavioralAssessment,
      intended.IsSequentialEquilibrium service.setup.intended_decision_antichain
        service.setup.intended_bounded.wellFoundedHistories
        (fun who final => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who)) →
      (∀ sequence : ℕ → service.setup.intendedModel.BehavioralAssessment,
        (∀ n, (sequence n).IsFullyMixed) →
        (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
          service.setup.intendedModel (sequence n) service.setup.intended_decision_antichain) →
        InformationModel.BehavioralAssessmentConvergesPointwise sequence intended →
        InformationModel.PooledLimitCertificate (N := service.riskModel)
          service.setup.intendedOutcome (service.nativeAuditedOutcome backend.sample)
          (instructionCount service.setup.program + 1) (2 * service.horizon + 1)
          ((service.bounds.riskMenu (serviceRuntime service.setup service.mode
            service.deadline) service.leaks service.bound).bounded initial service.horizon
            service.scheduler)
          ((service.bounds.riskMenu (serviceRuntime service.setup service.mode
            service.deadline) service.leaks service.bound).decisionRecall initial
            service.horizon service.scheduler)
          (service.setup.auditedUtility parameter utility forfeit deposit) sequence) →
      ∃ target : (raw.information initial service.horizon service.scheduler).BehavioralAssessment,
        target.IsSequentialEquilibriumFor
          (raw.decisionInformationAntichain initial service.horizon service.scheduler)
          (fun who site => target.truncatedContinuationContext site
            (fun history => payoff history.state who) (2 * service.horizon + 1)) ∧
        (∀ final ∈ ((raw.information initial service.horizon service.scheduler).runBehavioral
            target.strategy (2 * service.horizon + 1)).support,
          ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
        ((raw.information initial service.horizon service.scheduler).runBehavioral
            target.strategy (2 * service.horizon + 1)).bind
          (fun final => (settle final.state).map (fun payoffs =>
            (serviceSourceReadout service.setup service.mode service.deadline service.leaks
              final.state, payoffs))) =
          (service.setup.intendedModel.runBehavioral intended.strategy
              (instructionCount service.setup.program + 1)).map
            (fun final => (service.setup.protocolReadout final.state,
              fun who => (service.setup.protocolReadout final.state).elim 0
                (fun state => utility (service.setup.parameterOutcome parameter state) who))) := by
  intro forfeited base deposit raw initial observe audit payoff settle intended
    equilibrium certificate
  classical
  let effective := service.bounds.menu (serviceRuntime service.setup service.mode
    service.deadline) service.leaks
  let effectiveBounded := effective.bounded initial service.horizon service.scheduler
  obtain ⟨effectiveTarget, effectiveSE, clean, joint⟩ :=
    service.intended_effective_sequentialEquilibrium_of_certificate wellFormed parameter utility
      forfeit backend observationRate deliveryRate delivery_nonnegative positive coverage
      reference permitted intended equilibrium certificate
  have truncated := (effectiveTarget.isSequentialEquilibrium_iff_truncated_of_bounded _ _
    effectiveBounded.wellFoundedHistories effectiveBounded _).mp effectiveSE
  obtain ⟨target, _, targetSE, _, stateLaw⟩ :=
    service.bounds.exists_canonicalRaw_sequentialEquilibrium
      (serviceRuntime service.setup service.mode service.deadline) service.leaks initial
      service.horizon service.scheduler effectiveTarget (fun who state => payoff state who)
      truncated
  have baseInvariant (state : (serviceApplication service.setup service.mode service.deadline
      service.leaks).ProtocolState) :
      base (((serviceRuntime service.setup service.mode service.deadline).reactiveNormalization
        service.leaks).state state) = base state := by
    funext who
    change (serviceSourceReadout service.setup service.mode service.deadline service.leaks
      _).elim 0 _ = (serviceSourceReadout service.setup service.mode service.deadline
        service.leaks state).elim 0 _
    rw [serviceSourceReadout_normalization]
  have observation (state : (serviceApplication service.setup service.mode service.deadline
      service.leaks).ProtocolState) :
      observe (((serviceRuntime service.setup service.mode
        service.deadline).reactiveNormalization service.leaks).state state) = observe state :=
    (serviceRuntime service.setup service.mode
        service.deadline).serviceAuditObservation_normalization
      service.leaks
      ((serviceRuntime service.setup service.mode service.deadline).reactiveNormalization
        service.leaks) state
  have payoffInvariant (state : (serviceApplication service.setup service.mode service.deadline
      service.leaks).ProtocolState) :
      payoff (((serviceRuntime service.setup service.mode service.deadline).reactiveNormalization
        service.leaks).state state) = payoff state := by
    funext who
    simp only [payoff, TerminalAudit.utility, TerminalAudit.charge, baseInvariant, observation]
  have settlementInvariant (state : (serviceApplication service.setup service.mode
      service.deadline service.leaks).ProtocolState) :
      settle (((serviceRuntime service.setup service.mode service.deadline).reactiveNormalization
        service.leaks).state state) = settle state := by
    simp only [settle, TerminalAudit.settlement, baseInvariant, observation]
  have effectiveLaw := InformationModel.runBehavioralTerminalFrom_initHistory
    (effective.information initial service.horizon service.scheduler)
    effectiveBounded.wellFoundedHistories effectiveTarget.strategy effectiveBounded
  refine ⟨target, ?_, ?_, ?_⟩
  · simpa only [payoffInvariant] using targetSE
  · intro final reached who
    have normalized :
        ((serviceRuntime service.setup service.mode service.deadline).reactiveNormalization
        service.leaks).state final.state ∈
        (((effective.information initial service.horizon service.scheduler).runBehavioral
          effectiveTarget.strategy (2 * service.horizon + 1)).map
            GameTheory.Protocol.ExecutionProtocol.History.state).support := by
      rw [← stateLaw, PMF.support_map]
      exact ⟨final, reached, rfl⟩
    rw [PMF.support_map, ← effectiveLaw] at normalized
    obtain ⟨original, member, sameState⟩ := normalized
    have invariant : TerminalAudit.charge observe audit
          (((serviceRuntime service.setup service.mode service.deadline).reactiveNormalization
        service.leaks).state final.state) who =
        TerminalAudit.charge observe audit final.state who := by
      simp only [TerminalAudit.charge, observation]
    rw [← invariant, ← sameState]
    exact clean original member who
  · have pairs := congrArg (fun law => law.bind fun state =>
      (settle state).map (fun payoffs =>
        (serviceSourceReadout service.setup service.mode service.deadline service.leaks state,
          payoffs))) stateLaw
    simp only [PMF.bind_map, Function.comp_def, settlementInvariant,
      serviceSourceReadout_normalization] at pairs
    rw [pairs, ← effectiveLaw]
    exact joint

end Vegas.AsyncServiceSpec
