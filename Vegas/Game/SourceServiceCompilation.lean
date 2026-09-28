/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceEquilibrium
import Vegas.Game.SourceServiceRawExtension

/-! # Original source SE in the audited bounded raw runtime

The compiler fixes the native service, the audit backend and the deposit
before selecting a source equilibrium. Every original sequential equilibrium of
the full source language has a sequential equilibrium of the bounded raw
runtime whose joint law of initial parameters, public outcome and realized
settlement is the source law of initial parameters, public outcome and payoff.
The authentic partial audit and positive conditional coverage are explicit
service assumptions.

The source edge is
`Vegas.SourceServiceSpec.exists_native_sequentialEquilibrium`
and the runtime edge is
`Vegas.sourceService_audited_raw_equilibrium_extends`.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

/-- Every original source sequential equilibrium has a sequential equilibrium
of the audited bounded raw runtime with the source joint law of the typed
terminal source state and payoff, the payoff realized as settlement. The audit
charges no player on any history the native equilibrium reaches. Every
commitment payload type is finite, because the service's message interface
represents every binding value (`SourceServiceSpec.values`). -/
theorem audited_raw_sequentialEquilibrium_preserved {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (EnvelopeEvidence service.setup service.leaks) →
      FinDist (List (EnvelopeEvidence service.setup service.leaks)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.2.sender = who →
      (runtime service.setup).permittedServiceEnvelope record.1 record.2.1 record.2.2 = false →
      probability who ≤ (sample actual).probOf {observed | record ∈ observed})
    (source : service.sourceModel.BehavioralAssessment)
    [∀ who (site : service.sourceModel.InformationSite who),
      Fintype (service.sourceModel.InformationHistory who site.1)]
    (equilibrium : source.IsSequentialEquilibriumFor
      (service.setup.decision_antichain (CommitmentInterface.values service.setup.program))
      (fun who site => source.continuationContext site
        (fun final => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        (instructionCount service.setup.program + 1))) :
    let raw := service.bounds.rawMenu (runtime service.setup) service.leaks
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    let settle := TerminalAudit.settlement base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    ∃ target : (raw.information (initialLaw service.setup) service.planLength
        service.scheduler).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (raw.decisionInformationAntichain (initialLaw service.setup) service.planLength
          service.scheduler)
        (fun who site => target.continuationContext site
          (fun history => payoff history.state who) service.fuel) ∧
      (∀ final ∈ ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioral target.strategy service.fuel).support, ∀ who,
        TerminalAudit.charge ((runtime service.setup).serviceAuditObservation service.leaks)
          (sourceServiceAudit service.setup service.leaks sample) final.state who = 0) ∧
      ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioral target.strategy service.fuel).bind
          (fun final => (settle final.state).map (fun payoffs =>
            (sourceReadout service.setup service.leaks final.state, payoffs))) =
        (service.sourceModel.runBehavioral source.strategy
            (instructionCount service.setup.program + 1)).map
              (fun final => (service.setup.protocolReadout final.state,
                fun who => (service.setup.protocolReadout final.state).elim 0
                  (fun state => utility (service.setup.parameterOutcome parameter state)
                    who))) := by
  classical
  intro raw base deposit payoff settle
  obtain ⟨native, nativeSE, nativeLaw⟩ := service.exists_native_sequentialEquilibrium
    (fun output who => output.elim 0
      (fun state => utility (service.setup.parameterOutcome parameter state) who))
    source equilibrium
  obtain ⟨target, targetSE, clear, targetLaw⟩ := sourceService_audited_raw_equilibrium_extends
    service.setup service.leaks service.bounds service.values service.capacity service.rosters
    service.opportunities.binding service.network parameter utility sample authentic
    probability positive coverage (sourceReadout service.setup service.leaks)
    (sourceReadout_normalization service.setup service.leaks) native nativeSE
  have jointLaw := congrArg (fun law => law.map (fun output =>
    (output, fun who => output.elim 0
      (fun state => utility (service.setup.parameterOutcome parameter state) who)))) nativeLaw
  simp only [FinDist.map_comp, Function.comp_def] at jointLaw
  exact ⟨target, targetSE, clear, targetLaw.trans jointLaw⟩

/-- With a complete audit, which reports all traffic, every hypothesis on the
audit backend holds with coverage one: the conclusion of
`audited_raw_sequentialEquilibrium_preserved` needs only the service and the
source equilibrium. -/
theorem completeAudit_raw_sequentialEquilibrium_preserved {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (source : service.sourceModel.BehavioralAssessment)
    [∀ who (site : service.sourceModel.InformationSite who),
      Fintype (service.sourceModel.InformationHistory who site.1)]
    (equilibrium : source.IsSequentialEquilibriumFor
      (service.setup.decision_antichain (CommitmentInterface.values service.setup.program))
      (fun who site => source.continuationContext site
        (fun final => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        (instructionCount service.setup.program + 1))) :
    let sample : List (EnvelopeEvidence service.setup service.leaks) →
        FinDist (List (EnvelopeEvidence service.setup service.leaks)) := FinDist.pure
    let raw := service.bounds.rawMenu (runtime service.setup) service.leaks
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun _ => 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    let settle := TerminalAudit.settlement base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    ∃ target : (raw.information (initialLaw service.setup) service.planLength
        service.scheduler).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (raw.decisionInformationAntichain (initialLaw service.setup) service.planLength
          service.scheduler)
        (fun who site => target.continuationContext site
          (fun history => payoff history.state who) service.fuel) ∧
      (∀ final ∈ ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioral target.strategy service.fuel).support, ∀ who,
        TerminalAudit.charge ((runtime service.setup).serviceAuditObservation service.leaks)
          (sourceServiceAudit service.setup service.leaks sample) final.state who = 0) ∧
      ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioral target.strategy service.fuel).bind
          (fun final => (settle final.state).map (fun payoffs =>
            (sourceReadout service.setup service.leaks final.state, payoffs))) =
        (service.sourceModel.runBehavioral source.strategy
            (instructionCount service.setup.program + 1)).map
              (fun final => (service.setup.protocolReadout final.state,
                fun who => (service.setup.protocolReadout final.state).elim 0
                  (fun state => utility (service.setup.parameterOutcome parameter state)
                    who))) := by
  intro sample raw base deposit payoff settle
  have preserved := service.audited_raw_sequentialEquilibrium_preserved parameter utility sample
    (fun actual observed drawn => by
      rw [FinDist.mem_support_pure.mp drawn])
    (fun _ => 1) (fun _ => one_pos)
    (fun _ actual _ present _ _ => (FinDist.probOf_pure_self actual _ present).ge)
    source equilibrium
  simpa only [min_self] using preserved

end SourceServiceSpec

end Vegas
