/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketBaseAssembly
import Vegas.Game.OnePacketBlindConstruction

/-! # Sequential compilation under honest-counterpart construction

The concrete service and count-audit assumptions give sequential-equilibrium
preservation once irregular hidden bindings have regular counterparts. All
own-completion, replay-fiber and value-blindness obligations are discharged.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  [Finite setup.intendedProtocol.History]

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local instance : Fintype ((bounds.onePacketMenu (runtime setup) leaks).protocol
    (initialLaw setup) horizon scheduler).History :=
  (bounds.onePacketMenu (runtime setup) leaks).historyFintype (initialLaw setup) horizon scheduler

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

open Classical in
/-- Every intended sequential equilibrium is implemented by a zero-charge
sequential equilibrium of the bounded raw runtime, assuming construction of
honest counterparts at the canonical perturbation scale. -/
theorem onePacket_intended_raw_sequentialEquilibrium_of_counterparts
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependent) {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)))
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount)
    (counterparts : ∀ (sequence : ℕ → setup.intendedModel.BehavioralAssessment),
      (∀ n, (sequence n).IsFullyMixed) → ∀
      (weights : ℕ → ∀ p,
        PMF (OnePacketPart setup leaks bounds horizon scheduler bounds.candidateCount p))
      (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      OnePacketAssembled setup leaks bounds horizon scheduler sequence
        (fun n => trembleScale
          (combinedFloor setup leaks bounds horizon scheduler (sequence n)) (2 * horizon + 2) n)
        (fun n => trembleScale_pos
          (combinedFloor_pos setup leaks bounds horizon scheduler (sequence n)))
        (fun n => trembleScale_le_one
          (combinedFloor_pos setup leaks bounds horizon scheduler (sequence n)).le
          (combinedFloor_le_one setup leaks bounds horizon scheduler (sequence n)))
        weights targetSequence →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
        ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
          (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
      ∀ who (site : (onePacketN).InformationSite who),
        ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
        ∀ {past : List (application setup leaks).PlayerEntry}
          {view : (application setup leaks).PlayerView}, site.1 = some (past, view) →
        ∀ {event : (graph setup).EventId},
        view.application.publicView.ownTurn? who = some event →
        OnePacketCounterpartInputs setup leaks bounds horizon scheduler sequence targetSequence
          site)
    (service : EvidenceReportService (CountEvidence (graph setup)))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
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
  let gapBound : ℝ := ∑ who, |upperUtility who - excludedPayoff who|
  have gapNonneg : 0 ≤ gapBound := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have gapLe : ∀ who, upperUtility who - excludedPayoff who ≤ gapBound := by
    intro who
    calc
      upperUtility who - excludedPayoff who ≤ |upperUtility who - excludedPayoff who| :=
        le_abs_self _
      _ ≤ ∑ player : Player, |upperUtility player - excludedPayoff player| :=
        Finset.single_le_sum (f := fun player : Player =>
          |upperUtility player - excludedPayoff player|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ who)
      _ = gapBound := rfl
  apply onePacket_intended_raw_sequentialEquilibrium_of_blindInputs setup leaks bounds horizon
    scheduler parameter utility excludedPayoff wellFormed independent contract timely retains
    lowerUtility upperUtility lower_le le_upper below intended equilibrium
    (slots := bounds.candidateCount) ?_ service observationRate deliveryRate delivery_nonnegative
    coverage deposit deposit_nonnegative sufficient
  intro sequence mixed _bayes _converges
  let base := OnePacketBaseInputs.ofCounterparts wellFormed sequence mixed (2 * horizon + 2)
    gapBound gapNonneg covers coversInputs capacity slots_pos (counterparts sequence mixed)
  exact base.toBlindInputs setup leaks bounds horizon scheduler parameter utility excludedPayoff
    wellFormed contract timely retains mixed lower_le le_upper gapLe le_rfl

end Vegas
