/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateResolutionEffectiveExtension
import Vegas.Pending.ReactiveAliasEquilibrium

/-! # Source preservation in every bounded raw response of the concrete service

The risk-menu equilibrium extends by actual continuation comparisons, then
private response normalization supplies rational completion in the full raw
menu. The same sampled audit draw preserves the full typed source outcome and
realized payoff vector. This is a concrete certified service, not an arbitrary
asynchronous builder theorem.
-/

noncomputable section

namespace Vegas.LateResolutionService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory GameTheory.Math.Probability

abbrev rawMenu (bounds : MessageBounds nativeGraph) : app.ResponseMenu :=
  bounds.rawMenu (runtime setup) leaks

abbrev rawModel (bounds : MessageBounds nativeGraph) :=
  (rawMenu bounds).information (initialLaw setup) horizon scheduler

theorem rawCertificate (bounds : MessageBounds nativeGraph) :
    ((rawMenu bounds).protocol (initialLaw setup) horizon scheduler).WellFoundedHistories :=
  ((rawMenu bounds).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories

theorem auditedUtility_normalization
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) (state : app.ProtocolState) (who : Player) :
    auditedUtility sample deposit (((runtime setup).reactiveNormalization leaks).state state) who =
      auditedUtility sample deposit state who := by
  have observation := (runtime setup).serviceAuditObservation_normalization leaks
    ((runtime setup).reactiveNormalization leaks) state
  simp only [auditedUtility, GameTheory.Enforcement.TerminalAudit.utility,
    GameTheory.Enforcement.TerminalAudit.charge, baseUtility_normalization, observation]

/-- Every full effective-menu equilibrium lifts to an actual raw-menu SE.
The actual normalized terminal control law is kept, including off-path
private response aliases in the consistency construction. -/
theorem effective_equilibrium_extends_raw (bounds : MessageBounds nativeGraph)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (deposit : ℝ) (source : (effectiveModel bounds).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium
      ((effectiveMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
      (effectiveCertificate bounds)
      (fun who final => auditedUtility sample deposit final.state who)) :
    ∃ target : (rawModel bounds).BehavioralAssessment,
      target.IsSequentialEquilibrium
        ((rawMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
        (rawCertificate bounds)
        (fun who final => auditedUtility sample deposit final.state who) ∧
      (((rawModel bounds).runBehavioralTerminalFrom (rawCertificate bounds) target.strategy
        ((rawMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).map
          (fun final => ((runtime setup).reactiveNormalization leaks).state final.state)) =
        (((effectiveModel bounds).runBehavioralTerminalFrom (effectiveCertificate bounds)
          source.strategy
          ((effectiveMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).map
            ExecutionProtocol.History.state) := by
  classical
  have boundedSource := (source.isSequentialEquilibrium_iff_truncated_of_bounded
    (effectiveModel bounds)
    ((effectiveMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
    (effectiveCertificate bounds) ((effectiveMenu bounds).bounded (initialLaw setup)
      horizon scheduler) (fun who final => auditedUtility sample deposit final.state who)).mp
    equilibrium
  obtain ⟨target, _strategy, targetSE, _beliefs, stateLaw⟩ :=
    bounds.exists_canonicalRaw_sequentialEquilibrium (runtime setup) leaks (initialLaw setup)
      horizon scheduler source (fun who state => auditedUtility sample deposit state who)
        boundedSource
  have actualSE : target.IsSequentialEquilibriumFor
      ((rawMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
      (fun who site => target.truncatedContinuationContext site
        (fun final => auditedUtility sample deposit final.state who) 21) := by
    simpa only [auditedUtility_normalization, horizon] using targetSE
  refine ⟨target, (target.isSequentialEquilibrium_iff_truncated_of_bounded (rawModel bounds)
    ((rawMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
    (rawCertificate bounds) ((rawMenu bounds).bounded (initialLaw setup) horizon scheduler)
    (fun who final => auditedUtility sample deposit final.state who)).mpr actualSE, ?_⟩
  rw [InformationModel.runBehavioralTerminalFrom_initHistory (rawModel bounds)
      (rawCertificate bounds) target.strategy
      ((rawMenu bounds).bounded (initialLaw setup) horizon scheduler),
    InformationModel.runBehavioralTerminalFrom_initHistory (effectiveModel bounds)
      (effectiveCertificate bounds) source.strategy
      ((effectiveMenu bounds).bounded (initialLaw setup) horizon scheduler)]
  exact stateLaw

/-- Each original source sequential equilibrium has a full bounded raw native
SE with exactly its typed source outcome and the same realized settlement law.
No extra-response detection probability or conditional posterior is supplied. -/
theorem every_source_equilibrium_preserved_raw (bounds : MessageBounds nativeGraph)
    (covers : (⟨BaseTy.bool, true⟩ : Raw simpleExpr) ∈ bounds.values)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : ℝ) (nonnegative : 0 ≤ deposit) (source : sourceModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibrium (setup.decision_antichain sourceAdmission)
      sourceCertificate sourcePayoff) :
    ∃ target : (rawModel bounds).BehavioralAssessment,
      target.IsSequentialEquilibrium
        ((rawMenu bounds).decisionInformationAntichain (initialLaw setup) horizon scheduler)
        (rawCertificate bounds)
        (fun who final => auditedUtility sample deposit final.state who) ∧
      (sourceModel.runBehavioralTerminalFrom sourceCertificate source.strategy
        sourceArena.initHistory).map
          (fun final => (setup.protocolReadout final.state, fun who => sourcePayoff who final)) =
      ((rawModel bounds).runBehavioralTerminalFrom (rawCertificate bounds) target.strategy
        ((rawMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).bind
          (fun final =>
            (GameTheory.Enforcement.TerminalAudit.settlement
              (baseUtility setup leaks sourceUtility)
              ((runtime setup).serviceAuditObservation leaks)
              (sourceServiceAudit setup leaks sample) (fun _ => deposit) final.state).map
                (fun payoffs => (sourceReadout setup leaks final.state, payoffs))) := by
  obtain ⟨retained, _strategy, retainedSE, retainedJoint⟩ :=
    every_source_equilibrium_preserved_in_risk_menu bounds covers sample authentic deposit
      nonnegative source equilibrium
  obtain ⟨effective, effectiveSE, _agrees, effectiveState⟩ :=
    risk_equilibrium_extends_effective bounds covers sample authentic deposit nonnegative
      retained retainedSE
  obtain ⟨target, targetSE, rawState⟩ :=
    effective_equilibrium_extends_raw bounds sample deposit effective effectiveSE
  let settle (state : app.ProtocolState) :=
    (GameTheory.Enforcement.TerminalAudit.settlement (baseUtility setup leaks sourceUtility)
      ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
      (fun _ => deposit) state).map (fun payoffs => (sourceReadout setup leaks state, payoffs))
  have normalized (state : app.ProtocolState) :
      settle (((runtime setup).reactiveNormalization leaks).state state) = settle state := by
    have observation := (runtime setup).serviceAuditObservation_normalization leaks
      ((runtime setup).reactiveNormalization leaks) state
    simp only [settle, GameTheory.Enforcement.TerminalAudit.settlement,
      baseUtility_normalization, sourceReadout_normalization, observation]
  refine ⟨target, targetSE, ?_⟩
  rw [retainedJoint]
  change ((nativeModel bounds).runBehavioralTerminalFrom (nativeCertificate bounds)
      retained.strategy
      ((nativeMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).bind
        (fun final => settle final.state) =
    ((rawModel bounds).runBehavioralTerminalFrom (rawCertificate bounds) target.strategy
      ((rawMenu bounds).protocol (initialLaw setup) horizon scheduler).initHistory).bind
        (fun final => settle final.state)
  have joint := congrArg (fun law => law.bind settle) (rawState.trans effectiveState.symm)
  simpa only [PMF.bind_map, Function.comp_def, normalized] using joint.symm

end Vegas.LateResolutionService
