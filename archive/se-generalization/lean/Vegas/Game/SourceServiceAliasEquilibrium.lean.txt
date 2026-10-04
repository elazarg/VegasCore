/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceSpec
import Vegas.Game.SourceServiceAudit
import Vegas.Game.SourceServiceReadout
import Vegas.Pending.ReactiveAliasEquilibrium
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Final private-alias transport for an asynchronous native equilibrium

The complete normalized native menu already contains every effective packet
and every effective private binding choice. Adding its raw private aliases
preserves sequential equilibrium, projected beliefs and the joint source
readout and sampled payoff vector. The actual final traffic and contract record
are unchanged, so existing charges and correlated sampling are retained.

This is the final normalization stage. It assumes an equilibrium of the
complete normalized native game; obtaining that equilibrium from the risk menu
and embedding a source-language equilibrium remain separate proof obligations.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Private response names alter neither expected audited utility nor the
entire actual sampled settlement vector, at any initialized or partial state. -/
theorem sourceService_audited_normalization
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : Player → ℝ) (state : (application setup leaks).ProtocolState) :
    let normal := (runtime setup).reactiveNormalization leaks
    let base := baseUtility setup leaks utility
    let observe := (runtime setup).serviceAuditObservation leaks
    let audit := sourceServiceAudit setup leaks sample
    TerminalAudit.utility base observe audit deposit (normal.state state) =
        TerminalAudit.utility base observe audit deposit state ∧
      TerminalAudit.settlement base observe audit deposit (normal.state state) =
        TerminalAudit.settlement base observe audit deposit state := by
  intro normal base observe audit
  have readout := baseUtility_normalization setup leaks utility state
  have observed := (runtime setup).serviceAuditObservation_normalization leaks normal state
  change base (normal.state state) = base state at readout
  change observe (normal.state state) = observe state at observed
  constructor
  · funext who
    simp only [TerminalAudit.utility, TerminalAudit.charge, readout, observed]
  · simp only [TerminalAudit.settlement, readout, observed]

namespace AsyncServiceSpec

variable [Fintype Player] (service : AsyncServiceSpec Player L)

/-- An audited SE of the complete normalized native game lifts through raw
private action splitting. Consistent beliefs and the full joint actual source
readout and realized settlement law are preserved, including prior charges.
No monitoring-coverage or clean-history assumption enters this identity. -/
theorem normalization_sequentialEquilibrium
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (deposit : Player → ℝ) :
    let menu := service.bounds.menu (runtime service.setup) service.leaks
    let raw := service.bounds.rawMenu (runtime service.setup) service.leaks
    let normal := (runtime service.setup).reactiveNormalization service.leaks
    let initial := initialLaw service.setup
    let count := service.horizon
    let scheduler := service.scheduler
    let sourceCertificate := (menu.bounded initial count scheduler).wellFoundedHistories
    let targetCertificate := (raw.bounded initial count scheduler).wellFoundedHistories
    let base := baseUtility service.setup service.leaks utility
    let observe := (runtime service.setup).serviceAuditObservation service.leaks
    let audit := sourceServiceAudit service.setup service.leaks sample
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∀ source : (menu.information initial count scheduler).BehavioralAssessment,
      source.IsSequentialEquilibrium (menu.decisionInformationAntichain initial count scheduler)
        sourceCertificate (fun who final => payoff final.state who) →
    ∃ target : (raw.information initial count scheduler).BehavioralAssessment,
      target.strategy = (fun who => service.bounds.canonicalRawPolicy (runtime service.setup)
        service.leaks initial count scheduler who (source.strategy who)) ∧
      target.IsSequentialEquilibrium (raw.decisionInformationAntichain initial count scheduler)
        targetCertificate (fun who final => payoff final.state who) ∧
      (∀ who (site : (raw.information initial count scheduler).InformationSite who),
        (target.belief who site).map (normal.informationHistory raw
          (service.bounds.rawMenu_recall (runtime service.setup) service.leaks)
            initial count scheduler who site.1) =
          source.belief who (normal.site raw
            (service.bounds.rawMenu_recall (runtime service.setup) service.leaks)
              initial count scheduler who site)) ∧
      ((raw.information initial count scheduler).runBehavioralTerminalFrom targetCertificate
        target.strategy (raw.protocol initial count scheduler).initHistory).map
          (fun final => normal.state final.state) =
        ((menu.information initial count scheduler).runBehavioralTerminalFrom sourceCertificate
          source.strategy (menu.protocol initial count scheduler).initHistory).map History.state ∧
      ((menu.information initial count scheduler).runBehavioralTerminalFrom sourceCertificate
        source.strategy (menu.protocol initial count scheduler).initHistory).bind
          (fun final => (settle final.state).map (fun payoffs =>
            (sourceReadout service.setup service.leaks final.state, payoffs))) =
        ((raw.information initial count scheduler).runBehavioralTerminalFrom targetCertificate
          target.strategy (raw.protocol initial count scheduler).initHistory).bind
            (fun final => (settle final.state).map (fun payoffs =>
              (sourceReadout service.setup service.leaks final.state, payoffs))) := by
  intro menu raw normal initial count scheduler sourceCertificate targetCertificate base observe
    audit payoff settle source equilibrium
  have sourceTruncated := (source.isSequentialEquilibrium_iff_truncated_of_bounded
    (menu.information initial count scheduler)
    (menu.decisionInformationAntichain initial count scheduler) sourceCertificate
    (menu.bounded initial count scheduler)
      (fun who final => payoff final.state who)).mp equilibrium
  obtain ⟨target, strategy, targetTruncated, beliefs, stateLaw⟩ :=
    service.bounds.exists_canonicalRaw_sequentialEquilibrium (runtime service.setup) service.leaks
      initial count scheduler source (fun who state => payoff state who) sourceTruncated
  have normalization (state : (application service.setup service.leaks).ProtocolState) :
      payoff (normal.state state) = payoff state ∧ settle (normal.state state) = settle state :=
    sourceService_audited_normalization service.setup service.leaks utility sample deposit state
  have payoffSame (who : Player)
      (state : (application service.setup service.leaks).ProtocolState) :
      payoff (normal.state state) who = payoff state who := congrFun (normalization state).1 who
  have targetSE : target.IsSequentialEquilibrium
      (raw.decisionInformationAntichain initial count scheduler) targetCertificate
      (fun who final => payoff final.state who) := by
    apply (target.isSequentialEquilibrium_iff_truncated_of_bounded
      (raw.information initial count scheduler)
      (raw.decisionInformationAntichain initial count scheduler) targetCertificate
      (raw.bounded initial count scheduler) (fun who final => payoff final.state who)).mpr
    change target.IsSequentialEquilibriumFor
      (raw.decisionInformationAntichain initial count scheduler) (fun who site =>
        target.truncatedContinuationContext site
          (fun final => payoff (normal.state final.state) who) (2 * count + 1)) at targetTruncated
    have contexts :
        (fun who (site : (raw.information initial count scheduler).InformationSite who) =>
          target.truncatedContinuationContext site
          (fun final => payoff (normal.state final.state) who) (2 * count + 1)) =
        (fun who (site : (raw.information initial count scheduler).InformationSite who) =>
          target.truncatedContinuationContext site
          (fun final => payoff final.state who) (2 * count + 1)) := by
      funext who site
      exact congrArg (fun utility => target.truncatedContinuationContext site utility
        (2 * count + 1)) (funext fun final => payoffSame who final.state)
    exact contexts ▸ targetTruncated
  have terminalLaw :
      ((raw.information initial count scheduler).runBehavioralTerminalFrom targetCertificate
        target.strategy (raw.protocol initial count scheduler).initHistory).map
          (fun final => normal.state final.state) =
        ((menu.information initial count scheduler).runBehavioralTerminalFrom sourceCertificate
          source.strategy (menu.protocol initial count scheduler).initHistory).map
            History.state := by
    rw [InformationModel.runBehavioralTerminalFrom_initHistory _ _ _
      (raw.bounded initial count scheduler),
      InformationModel.runBehavioralTerminalFrom_initHistory _ _ _
        (menu.bounded initial count scheduler)]
    exact stateLaw
  refine ⟨target, strategy, targetSE, beliefs, terminalLaw, ?_⟩
  let readout := fun state : (application service.setup service.leaks).ProtocolState =>
    (settle state).map (fun payoffs =>
      (sourceReadout service.setup service.leaks state, payoffs))
  have readoutSame (state : (application service.setup service.leaks).ProtocolState) :
      readout (normal.state state) = readout state := by
    dsimp only [readout]
    rw [(normalization state).2, sourceReadout_normalization]
  calc
    _ = (((menu.information initial count scheduler).runBehavioralTerminalFrom sourceCertificate
        source.strategy (menu.protocol initial count scheduler).initHistory).map
          History.state).bind readout := (PMF.bind_map ..).symm
    _ = (((raw.information initial count scheduler).runBehavioralTerminalFrom targetCertificate
        target.strategy (raw.protocol initial count scheduler).initHistory).map
          (fun final => normal.state final.state)).bind readout :=
      congrArg (fun law => law.bind readout) terminalLaw.symm
    _ = _ := by
      rw [PMF.bind_map]
      apply bind_congr_on_support _
      intro final _
      exact readoutSame final.state

end AsyncServiceSpec
end Vegas
