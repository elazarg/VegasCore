/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketExtension
import Vegas.Game.OnePacketLawApproximation
import Vegas.Game.OnePacketExclusionPayoff
import GameTheoryExtensions.Analysis.Protocol.CopiedSiteLimit

/-! # Sequential preservation for the one-packet game

The source is the intended game of a well-formed setup, observed through its
typed readout and the exclusion payoff it determines
(`Vegas.intendedReadoutExclusion`); the target is the one-packet game of the
default runtime, observed through its typed readout and native exclusion
payoff (`Vegas.readoutExclusion`). The utility of either observation is its
payoff component.

**From certificates.** If, for every fully mixed Bayes sequence converging to an
intended sequential equilibrium, a pooled component family on the one-packet
game meets the obligations of a pooled limit certificate, then some sequential
equilibrium of the one-packet game under the exclusion payoff has the intended
joint law of typed readout and exclusion payoff
(`Vegas.onePacket_intended_sequentialEquilibrium_of_certificates`). Every
intended sequential equilibrium is sequentially rational against the exclusion
payoff (`Vegas.SourceProgram.Setup.intended_exclusionSource`), which supplies
the source side of the limit theorem.

**The raw runtime.** Composed with the extension of one-packet equilibria to the
bounded raw runtime under the count audit, the same certificates give a
sequential equilibrium of the bounded raw runtime, under the exclusion payoff
minus the deposit for each collected count charge, that charges nobody on its
paths and whose joint law of normalized typed readout and exclusion payoff is
the intended one (`Vegas.onePacket_intended_raw_sequentialEquilibrium`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- The utility of an observation of readout and payoffs: its payoff component. -/
abbrev payoffComponent (outcome : Option (State L setup.program.terminalCtx) × (Player → ℝ))
    (who : Player) : ℝ :=
  outcome.2 who

open Classical in
/-- **Sequential equilibrium of the one-packet game from certificates.** For a
well-formed setup, every sequential equilibrium of the intended game, and a
pooled limit certificate on the one-packet game for every fully mixed Bayes
sequence converging to it, there is a sequential equilibrium of the one-packet
game under the exclusion payoff whose joint law of typed readout and exclusion
payoff is the intended one. -/
theorem onePacket_intended_sequentialEquilibrium_of_certificates
    (wellFormed : setup.WellFormed)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    (certificates : ∀ sequence : ℕ → setup.intendedModel.BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed) →
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent setup.intendedModel
        (sequence n) setup.intended_decision_antichain) →
      InformationModel.BehavioralAssessmentConvergesPointwise sequence intended →
      InformationModel.PooledLimitCertificate
        (N := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler)
        (intendedReadoutExclusion setup parameter utility excludedPayoff)
        (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
          utility excludedPayoff)
        (instructionCount setup.program + 1) (2 * horizon + 1)
        ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
          scheduler)
        ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall (initialLaw setup) horizon
          scheduler)
        (payoffComponent setup) sequence) :
    ∃ target : (onePacketModel setup leaks bounds (initialLaw setup) horizon
        scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        ((bounds.onePacketMenu (runtime setup) leaks).decisionInformationAntichain
          (initialLaw setup) horizon scheduler)
        ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories
        (fun who final => exclusionBase setup parameter utility excludedPayoff leaks final.state
          who) ∧
      ((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).map
          (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
            utility excludedPayoff) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  obtain ⟨sequence, mixed, bayes, converges, rational⟩ :=
    setup.intended_exclusionSource wellFormed parameter utility excludedPayoff intended
      equilibrium
  obtain ⟨target, targetSE, law⟩ :=
    (certificates sequence mixed bayes converges).exists_sequentialEquilibrium intended converges
      rational
  let bounded := (bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
    scheduler
  exact ⟨target, (target.isSequentialEquilibrium_iff_truncated_of_bounded _ _
    bounded.wellFoundedHistories bounded _).mpr targetSE, law⟩

open Classical in
/-- **Sequential equilibrium of the bounded raw runtime from certificates.**
Under the hypotheses of
`Vegas.onePacket_intended_sequentialEquilibrium_of_certificates`, bounds on the
utility, and a count-evidence service with a deposit covering the spread of
the exclusion payoff, there is a sequential equilibrium of the bounded raw
runtime under the exclusion payoff minus the deposit for each collected count
charge, that charges nobody on its paths, whose joint law of typed readout and
realized payoffs is the intended joint law of typed readout and exclusion
payoff. -/
theorem onePacket_intended_raw_sequentialEquilibrium (wellFormed : setup.WellFormed)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    (certificates : ∀ sequence : ℕ → setup.intendedModel.BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed) →
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent setup.intendedModel
        (sequence n) setup.intended_decision_antichain) →
      InformationModel.BehavioralAssessmentConvergesPointwise sequence intended →
      InformationModel.PooledLimitCertificate
        (N := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler)
        (intendedReadoutExclusion setup parameter utility excludedPayoff)
        (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
          utility excludedPayoff)
        (instructionCount setup.program + 1) (2 * horizon + 1)
        ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
          scheduler)
        ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall (initialLaw setup) horizon
          scheduler)
        (payoffComponent setup) sequence)
    (service : EvidenceReportService (CountEvidence (graph setup)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (deposit : Player → ℝ) (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      max 0 (max (excludedPayoff who) (upperUtility who)) -
          min 0 (min (excludedPayoff who) (lowerUtility who)) ≤
        observationRate who * deliveryRate who * deposit who) :
    let raw := bounds.rawMenu (runtime setup) leaks
    let observe := (application setup leaks).stateTraffic
    let audit := (runtime setup).countAudit leaks service.sample
    let base := exclusionBase setup parameter utility excludedPayoff leaks
    let payoff := TerminalAudit.utility base observe audit deposit
    let settle := TerminalAudit.settlement base observe audit deposit
    ∃ target : (raw.information (initialLaw setup) horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (raw.decisionInformationAntichain (initialLaw setup) horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => payoff history.state who) (2 * horizon + 1)) ∧
      (∀ final ∈ ((raw.information (initialLaw setup) horizon scheduler).runBehavioral
          target.strategy (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information (initialLaw setup) horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).bind
          (fun final => (settle final.state).map fun payoffs =>
            (sourceReadout setup leaks final.state, payoffs)) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  intro raw observe audit base payoff settle
  obtain ⟨native, nativeSE, law⟩ := onePacket_intended_sequentialEquilibrium_of_certificates
    setup leaks bounds horizon scheduler parameter utility excludedPayoff wellFormed intended
    equilibrium certificates
  obtain ⟨target, targetSE, clean, _, joint⟩ :=
    bounds.onePacket_raw_sequentialEquilibrium (runtime setup) leaks (initialLaw setup) horizon
      scheduler service observationRate deliveryRate delivery_nonnegative coverage
      (fun state who => base state who)
      (fun state => exclusionBase_normalization setup parameter utility excludedPayoff leaks state)
      (fun who => min 0 (min (excludedPayoff who) (lowerUtility who)))
      (fun who => max 0 (max (excludedPayoff who) (upperUtility who))) deposit
      (fun state who => (exclusionBase_mem_Icc setup parameter utility excludedPayoff
        leaks lowerUtility upperUtility lower_le le_upper state who).1)
      (fun state who => (exclusionBase_mem_Icc setup parameter utility excludedPayoff
        leaks lowerUtility upperUtility lower_le le_upper state who).2)
      deposit_nonnegative sufficient native nativeSE
  refine ⟨target, targetSE, clean, ?_⟩
  have pairs := congrArg (PMF.map (Prod.map (sourceReadout setup leaks) id)) joint
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Prod.map_apply, id_eq,
    sourceReadout_normalization] at pairs
  rw [pairs, ← law]
  rfl

end Vegas
