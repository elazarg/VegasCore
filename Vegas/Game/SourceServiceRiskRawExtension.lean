/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRiskExtension
import Vegas.Game.SourceServiceAliasEquilibrium

/-! # Audited risk-menu equilibrium in the bounded raw runtime

Signed-content enforcement and the explicit remaining effective-action
comparisons extend the risk-menu equilibrium to the complete effective menu.
Private-alias transport then supplies a raw-runtime equilibrium with the same
joint typed source readout and actual sampled payoff vector. The stages use
one authentic final-record coverage contract and one fixed deposit, retaining
prior charges and correlations.

The input is an audited risk-menu equilibrium. Embedding an original source
equilibrium and discharging the other effective-action comparisons remain
separate obligations; neither is assumed proved by this composition.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

/-- Conditional effective-action enforcement followed by exact private-alias
transport preserves the risk game's actual joint settlement law. The remaining
comparison predicate has no harmless-alias or source-equilibrium premise. -/
theorem risk_raw_sequentialEquilibrium_extends
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (backend : EvidenceReportService (SettledEvidence service.setup))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (positive : ∀ who, 0 < observationRate who * deliveryRate who)
    (coverage : FinalForbiddenEvidenceCoverage backend observationRate deliveryRate)
    (reference : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (reference who).Admitted service.setup.program
      (CommitmentInterface.values _)) :
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let raw := service.bounds.rawMenu (runtime service.setup) service.leaks
    let initial := initialLaw service.setup
    let count := service.horizon
    let scheduler := service.scheduler
    let sourceCertificate := (menu.bounded initial count scheduler).wellFoundedHistories
    let targetCertificate := (raw.bounded initial count scheduler).wellFoundedHistories
    let probability := fun who => observationRate who * deliveryRate who
    let base := baseUtility service.setup service.leaks utility
    let deposit := service.auditDeposit base probability
    let observe := (runtime service.setup).serviceAuditObservation service.leaks
    let audit := sourceServiceAudit service.setup service.leaks backend.sample
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    service.riskOtherExclusionComparisons utility backend.sample deposit →
    ∀ source : (menu.information initial count scheduler).BehavioralAssessment,
      source.IsSequentialEquilibrium (menu.decisionInformationAntichain initial count scheduler)
        sourceCertificate (fun who final => payoff final.state who) →
    ∃ target : (raw.information initial count scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium (raw.decisionInformationAntichain initial count scheduler)
        targetCertificate (fun who final => payoff final.state who) ∧
      ((menu.information initial count scheduler).runBehavioralTerminalFrom sourceCertificate
        source.strategy (menu.protocol initial count scheduler).initHistory).bind
          (fun final => (settle final.state).map (fun payoffs =>
            (sourceReadout service.setup service.leaks final.state, payoffs))) =
        ((raw.information initial count scheduler).runBehavioralTerminalFrom targetCertificate
          target.strategy (raw.protocol initial count scheduler).initHistory).bind
            (fun final => (settle final.state).map (fun payoffs =>
              (sourceReadout service.setup service.leaks final.state, payoffs))) := by
  intro menu raw initial count scheduler sourceCertificate targetCertificate probability base
    deposit observe audit payoff settle otherComparisons source equilibrium
  obtain ⟨effective, effectiveSE, _agrees, _beliefs, _histories, joint⟩ :=
    service.risk_sequentialEquilibrium_extends utility backend observationRate deliveryRate
      delivery_nonnegative positive coverage reference permitted otherComparisons
        source equilibrium
  obtain ⟨target, _strategy, targetSE, _beliefs, _states, rawJoint⟩ :=
    service.normalization_sequentialEquilibrium utility backend.sample deposit effective
      effectiveSE
  refine ⟨target, targetSE, ?_⟩
  have projected := congrArg (fun law => law.map (fun outcome =>
    (sourceReadout service.setup service.leaks outcome.1, outcome.2))) joint
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at projected
  exact projected.trans rawJoint

end Vegas.AsyncServiceSpec
