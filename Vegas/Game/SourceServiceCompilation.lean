/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceEquilibrium
import Vegas.Game.SourceServiceRawExtension
import GameTheoryExtensions.Protocol.ContinuationHorizon

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

omit [Fintype Player] in
/-- The source protocol of the service's program terminates within its
instruction bound. -/
theorem sourceTerminates : (service.setup.executionProtocol
    (CommitmentInterface.values service.setup.program)).WellFoundedHistories :=
  (service.setup.protocol_bounded _).wellFoundedHistories

/-- The bounded raw runtime terminates within its fuel. -/
theorem rawTerminates : ((service.bounds.rawMenu (runtime service.setup) service.leaks).protocol
    (initialLaw service.setup) service.planLength service.scheduler).WellFoundedHistories :=
  ((service.bounds.rawMenu (runtime service.setup) service.leaks).bounded _ _
    _).wellFoundedHistories

/-- The initial history of the source protocol. -/
abbrev sourceInitial := (service.setup.executionProtocol
  (CommitmentInterface.values service.setup.program)).initHistory

/-- The initial history of the bounded raw runtime. -/
abbrev rawInitial := ((service.bounds.rawMenu (runtime service.setup) service.leaks).protocol
  (initialLaw service.setup) service.planLength service.scheduler).initHistory

/-- Every original source sequential equilibrium has a sequential equilibrium
of the audited bounded raw runtime with the source joint law of the typed
terminal source state and payoff, the payoff realized as settlement. Both
equilibria and both laws are of complete (terminal) play. The audit
charges no player on any history the native equilibrium reaches. Every
commitment payload type is finite, because the service's message interface
represents every binding value (`SourceServiceSpec.values`). -/
theorem audited_raw_sequentialEquilibrium_preserved {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (EnvelopeEvidence service.setup service.leaks) →
      PMF (List (EnvelopeEvidence service.setup service.leaks)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.2.sender = who →
      (runtime service.setup).permittedServiceEnvelope record.1 record.2.1 record.2.2 = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (source : service.sourceModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium
      (service.setup.decision_antichain (CommitmentInterface.values service.setup.program))
      service.sourceTerminates
      (fun who final => (service.setup.protocolReadout final.state).elim 0
        (fun state => utility (service.setup.parameterOutcome parameter state) who))) :
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
      target.IsSequentialEquilibrium
        (raw.decisionInformationAntichain (initialLaw service.setup) service.planLength
          service.scheduler) service.rawTerminates
        (fun who history => payoff history.state who) ∧
      (∀ final ∈ ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioralTerminalFrom service.rawTerminates target.strategy
            service.rawInitial).support, ∀ who,
        TerminalAudit.charge ((runtime service.setup).serviceAuditObservation service.leaks)
          (sourceServiceAudit service.setup service.leaks sample) final.state who = 0) ∧
      ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioralTerminalFrom service.rawTerminates target.strategy
            service.rawInitial).bind
          (fun final => (settle final.state).map (fun payoffs =>
            (sourceReadout service.setup service.leaks final.state, payoffs))) =
        (service.sourceModel.runBehavioralTerminalFrom service.sourceTerminates source.strategy
            service.sourceInitial).map
              (fun final => (service.setup.protocolReadout final.state,
                fun who => (service.setup.protocolReadout final.state).elim 0
                  (fun state => utility (service.setup.parameterOutcome parameter state)
                    who))) := by
  classical
  intro raw base deposit payoff settle
  have sourceBounded := service.setup.protocol_bounded
    (CommitmentInterface.values service.setup.program)
  have rawBounded := raw.bounded (initialLaw service.setup) service.planLength service.scheduler
  have truncated := (source.isSequentialEquilibrium_iff_truncated_of_bounded service.sourceModel _
    service.sourceTerminates sourceBounded _).mp equilibrium
  obtain ⟨native, nativeSE, nativeLaw⟩ := service.exists_native_sequentialEquilibrium
    (fun output who => output.elim 0
      (fun state => utility (service.setup.parameterOutcome parameter state) who))
    source truncated
  obtain ⟨target, targetSE, clear, targetLaw⟩ := sourceService_audited_raw_equilibrium_extends
    service.setup service.leaks service.bounds service.values service.capacity service.rosters
    service.opportunities.binding service.network parameter utility sample authentic
    probability positive coverage (sourceReadout service.setup service.leaks)
    (sourceReadout_normalization service.setup service.leaks) native nativeSE
  have jointLaw := congrArg (fun law => law.map (fun output =>
    (output, fun who => output.elim 0
      (fun state => utility (service.setup.parameterOutcome parameter state) who)))) nativeLaw
  simp only [PMF.map_comp, Function.comp_def] at jointLaw
  refine ⟨target, (target.isSequentialEquilibrium_iff_truncated_of_bounded _ _
    service.rawTerminates rawBounded _).mpr targetSE, ?_, ?_⟩
  · rw [InformationModel.runBehavioralTerminalFrom_initHistory _ service.rawTerminates _
      rawBounded]
    exact clear
  · rw [InformationModel.runBehavioralTerminalFrom_initHistory _ service.rawTerminates _
        rawBounded,
      InformationModel.runBehavioralTerminalFrom_initHistory _ service.sourceTerminates _
        sourceBounded]
    exact targetLaw.trans jointLaw

/-- With a complete audit, which reports all traffic, every hypothesis on the
audit backend holds with coverage one: the conclusion of
`audited_raw_sequentialEquilibrium_preserved` needs only the service and the
source equilibrium. -/
theorem completeAudit_raw_sequentialEquilibrium_preserved {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (source : service.sourceModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium
      (service.setup.decision_antichain (CommitmentInterface.values service.setup.program))
      service.sourceTerminates
      (fun who final => (service.setup.protocolReadout final.state).elim 0
        (fun state => utility (service.setup.parameterOutcome parameter state) who))) :
    let sample : List (EnvelopeEvidence service.setup service.leaks) →
        PMF (List (EnvelopeEvidence service.setup service.leaks)) := PMF.pure
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
      target.IsSequentialEquilibrium
        (raw.decisionInformationAntichain (initialLaw service.setup) service.planLength
          service.scheduler) service.rawTerminates
        (fun who history => payoff history.state who) ∧
      (∀ final ∈ ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioralTerminalFrom service.rawTerminates target.strategy
            service.rawInitial).support, ∀ who,
        TerminalAudit.charge ((runtime service.setup).serviceAuditObservation service.leaks)
          (sourceServiceAudit service.setup service.leaks sample) final.state who = 0) ∧
      ((raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioralTerminalFrom service.rawTerminates target.strategy
            service.rawInitial).bind
          (fun final => (settle final.state).map (fun payoffs =>
            (sourceReadout service.setup service.leaks final.state, payoffs))) =
        (service.sourceModel.runBehavioralTerminalFrom service.sourceTerminates source.strategy
            service.sourceInitial).map
              (fun final => (service.setup.protocolReadout final.state,
                fun who => (service.setup.protocolReadout final.state).elim 0
                  (fun state => utility (service.setup.parameterOutcome parameter state)
                    who))) := by
  intro sample raw base deposit payoff settle
  have preserved := service.audited_raw_sequentialEquilibrium_preserved parameter utility sample
    (fun actual observed drawn => by
      rw [(PMF.mem_support_pure_iff _ _).mp drawn])
    (fun _ => 1) (fun _ => one_pos)
    (fun _ actual _ present _ _ => by simp [sample, PMF.toOuterMeasure_pure_apply, present])
    source equilibrium
  simpa only [min_self] using preserved

end SourceServiceSpec

end Vegas
