/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateDecomposition
import Vegas.Game.OnePacketLateCommitments
import Vegas.Game.OnePacketValueTransport
import Vegas.Game.OnePacketNonLateDecomposition

/-! # Assembling the one-packet certificate from value blindness

The value decompositions of the one-packet certificate follow from the bounds on
the utility, the exclusion payoff at most every intended outcome, a gap bound,
and value blindness of the completion value at forced sites
(`Vegas.onePacket_lateDecomposition`,
`Vegas.onePacket_nonLateDecomposition_of_pending`).
Late commitments of intended values follow from value-blind late options and
value-blind late commitments (`Vegas.OnePacketBaseInputs.lateCommitments_of_blind`).
So the base inputs with these hypotheses give the open inputs
(`Vegas.OnePacketBlindInputs.toOpenInputs`) and sequential equilibrium of the
one-packet game and of the bounded raw runtime with the intended joint law
(`Vegas.onePacket_intended_sequentialEquilibrium_of_blindInputs`,
`Vegas.onePacket_intended_raw_sequentialEquilibrium_of_blindInputs`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

open Classical in
/-- **The open inputs by value blindness.** The base inputs, a gap bound above
the spread of the utility over the exclusion payoff, late options covering the
bounded slots, value blindness of the completion value at forced late
deliveries and at the other forced sites, and value-blind late commitments. -/
structure OnePacketBlindInputs (upperUtility : Player → ℝ)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment) (slots : Nat) extends
    OnePacketBaseInputs setup leaks bounds horizon scheduler sequence slots where
  /-- The gap bound is at least the spread of the utility over the exclusion
  payoff. -/
  gap_le : ∀ who, upperUtility who - excludedPayoff who ≤ gapBound
  /-- **Value blindness at late deliveries.** -/
  lateValueBlind : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler
        slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one weights targetSequence →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
        ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
          (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
      ∃ blindError : ℕ → ℝ, Tendsto blindError atTop (nhds 0) ∧
        ∀ n who (site : (onePacketN).InformationSite who),
          ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ¬ OwingAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
            (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
            ((onePacketN).agentAt site) →
          (∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
            |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
                (PMF.pure choice) -
              (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
                site (PMF.pure choice)) *
              siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
              blindError n) ∧
          ∀ option,
            |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
                (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one (slots := slots) n ((onePacketN).agentAt site) option) -
              (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
                site (onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
                  scale_le_one (slots := slots) n ((onePacketN).agentAt site) option)) *
              siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
              blindError n
  /-- The late options cover the bounded prepared slots. -/
  slotsCover : bounds.candidateCount ≤ slots
  /-- **Value-blind late commitments.** -/
  lateCommitBlind : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler
        slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one weights targetSequence →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
        ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
          (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
      ∃ blindError : ℕ → ℝ, Tendsto blindError atTop (nhds 0) ∧
        LateCommitBlind setup leaks bounds horizon scheduler parameter utility excludedPayoff
          sequence scale scale_pos scale_le_one (slots := slots) targetSequence blindError
  /-- **Value blindness away from late deliveries.** -/
  nonLateValueBlind : ∀ (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler
        slots p)) (targetSequence : ℕ → (onePacketN).BehavioralAssessment),
      OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one weights targetSequence →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
        ((bounds.onePacketMenu (runtime setup) leaks).decisionRecall
          (initialLaw setup) horizon scheduler).decisionInformationAntichain) →
      ∃ blindError : ℕ → ℝ, Tendsto blindError atTop (nhds 0) ∧
        ∀ n who (site : (onePacketN).InformationSite who),
          ¬ FreeAgent setup leaks bounds horizon scheduler ((onePacketN).agentAt site) →
          ¬ ownedKeyed (FreeAgent setup leaks bounds horizon scheduler)
            (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon scheduler)
            ((onePacketN).agentAt site) →
          pendingEvent setup leaks who site.1 ≠ none →
          (∀ choice, onePacketCompared setup leaks bounds horizon scheduler who site choice →
            |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
                (PMF.pure choice) -
              (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
                site (PMF.pure choice)) *
              siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
                (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
              blindError n) ∧
          |siteStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
              (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale scale_pos
                scale_le_one n ((onePacketN).agentAt site)) -
            (1 - onePacketSiteFailure setup leaks bounds horizon scheduler (targetSequence n)
              site (onePacketPrescribed setup leaks bounds horizon scheduler sequence scale
                scale_pos scale_le_one n ((onePacketN).agentAt site))) *
            siteValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
              (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site| ≤
            blindError n

/-- **The open inputs from value blindness.** For a well-formed setup, under the
asynchronous contract with timely delays and retention of first covered
canonical packets, with the utility between the bounds and the exclusion payoff
at most every intended outcome, the inputs by value blindness give the open
inputs. -/
def OnePacketBlindInputs.toOpenInputs {lowerUtility upperUtility : Player → ℝ}
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment} {slots : Nat}
    (inputs : OnePacketBlindInputs setup leaks bounds horizon scheduler parameter utility
      excludedPayoff upperUtility sequence slots)
    (wellFormed : setup.WellFormed) {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain) :
    OnePacketOpenInputs setup leaks bounds horizon scheduler parameter utility excludedPayoff
      sequence slots where
  toOnePacketBaseInputs := inputs.toOnePacketBaseInputs
  valueTransport weights targetSequence assembled mixed bayes := by
    classical
    let range := fun who : Player => max 0 (max (excludedPayoff who) (upperUtility who)) -
      min 0 (min (excludedPayoff who) (lowerUtility who))
    let total := ∑ who, range who
    have rangeNonneg : ∀ who, 0 ≤ range who := fun who => by
      have := le_max_left 0 (max (excludedPayoff who) (upperUtility who))
      have := min_le_left 0 (min (excludedPayoff who) (lowerUtility who))
      simp only [range]
      linarith
    have rangeLe : ∀ who, range who ≤ total := fun who =>
      Finset.single_le_sum (fun player _ => rangeNonneg player) (Finset.mem_univ who)
    have totalNonneg : 0 ≤ total := Finset.sum_nonneg fun player _ => rangeNonneg player
    let valueError := fun n => 2 * (((Fintype.card Player * (2 * horizon + 1) : ℕ) *
      (1 - slotRetention (inputs.scale n))) * total) + 12 * inputs.scale n * total
    have valueLimit : Tendsto valueError atTop (nhds 0) := by
      have retention := tendsto_slotRetention inputs.scale_vanishing
      have limit := (((((tendsto_const_nhds (x := (1 : ℝ))).sub retention).const_mul
        ((Fintype.card Player * (2 * horizon + 1) : ℕ) : ℝ)).mul_const total).const_mul 2).add
        (((inputs.scale_vanishing.const_mul 12).mul_const total))
      simp only [sub_self, mul_zero, zero_mul, add_zero] at limit
      exact limit
    refine ⟨valueError, 4 * total, valueLimit, by positivity,
      fun n who site choice forced unkeyed atTurn debtFree intended decision past view atSite =>
        ?_⟩
    obtain ⟨turnPast, turnView, response, event, turnSite, _, _, turn⟩ := atTurn
    rw [atSite, Option.some.injEq, Prod.mk.injEq] at turnSite
    obtain ⟨pastEq, viewEq⟩ := turnSite
    subst pastEq viewEq
    have beliefs := inputs.beliefInputs setup leaks bounds horizon scheduler weights
      targetSequence assembled mixed bayes who site
      forced (not_owingAgent_of_siteDebtFree setup leaks bounds horizon scheduler debtFree)
      atSite turn decision
    obtain ⟨policy, gainLe⟩ := onePacket_valueTransport_le setup leaks bounds horizon scheduler
      parameter utility excludedPayoff wellFormed contract timely retains lowerUtility
      upperUtility lower_le le_upper sequence inputs.scale inputs.scale_pos inputs.scale_le_one
      weights targetSequence assembled n site choice forced unkeyed
      ⟨_, _, response, event, atSite, by assumption, by assumption, turn⟩ intended decision
      atSite (beliefs.ownIntended n)
    refine ⟨policy, gainLe.trans ?_, fun point =>
      (abs_intended_historyGain_le setup parameter utility excludedPayoff lowerUtility
        upperUtility lower_le le_upper (sequence n) _ point).trans (by linarith [rangeLe who])⟩
    have retentionLe := slotRetention_le_one (inputs.scale_pos n).le (inputs.scale_le_one n)
    have scaleNonneg := (inputs.scale_pos n).le
    have irregularNonneg : 0 ≤ expect ((targetSequence n).belief who site) (fun history =>
        if RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace
        then (0 : ℝ) else 1) :=
      expect_nonneg _ _ fun history _ => by split <;> norm_num
    have retentionTerm : 0 ≤ ((Fintype.card Player * (2 * horizon + 1) : ℕ) : ℝ) *
        (1 - slotRetention (inputs.scale n)) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have first := mul_le_mul_of_nonneg_left (rangeLe who) retentionTerm
    have second := mul_le_mul_of_nonneg_left (rangeLe who) scaleNonneg
    have third := mul_le_mul_of_nonneg_right (rangeLe who) irregularNonneg
    simp only [valueError, range] at first second third ⊢
    nlinarith [first, second, third]
  lateCommitments := inputs.toOnePacketBaseInputs.lateCommitments_of_blind setup leaks bounds
    horizon scheduler parameter utility excludedPayoff wellFormed contract timely retains
    lowerUtility upperUtility lower_le le_upper sourceMixed sourceBayes inputs.slotsCover
    (fun weights targetSequence assembled mixed bayes => by
      obtain ⟨blindError, blindLimit, blind⟩ :=
        inputs.lateValueBlind weights targetSequence assembled mixed bayes
      exact ⟨blindError, blindLimit, fun n who site forced notOwing keyed =>
        (blind n who site forced notOwing keyed).2⟩)
    inputs.lateCommitBlind
  lateDecomposition := onePacket_lateDecomposition setup leaks bounds horizon scheduler parameter
    utility excludedPayoff wellFormed contract timely retains lowerUtility upperUtility lower_le
    le_upper sequence below inputs.scale inputs.scale_pos inputs.scale_le_one
    inputs.scale_vanishing inputs.gapBound inputs.gap_le inputs.gapBound_nonneg
    inputs.lateValueBlind
  nonLateDecomposition := onePacket_nonLateDecomposition_of_pending setup leaks bounds horizon
    scheduler parameter utility excludedPayoff wellFormed contract timely retains lowerUtility
    upperUtility lower_le le_upper sequence below inputs.scale inputs.scale_pos inputs.scale_le_one
    inputs.scale_vanishing inputs.gapBound inputs.gap_le inputs.gapBound_nonneg
    inputs.nonLateValueBlind

/-- **Sequential equilibrium of the one-packet game from value blindness.** For
a well-formed setup, under the asynchronous contract with timely delays and
retention of first covered canonical packets, with the utility between bounds
and the exclusion payoff at most every intended outcome, for every sequential
equilibrium of the intended game, if every fully mixed Bayes sequence
converging to it supplies the open inputs by value blindness, there is a
sequential equilibrium of the one-packet game under the exclusion payoff whose
joint law of typed readout and exclusion payoff is the intended one.

Each player's hidden initial cells must be independent of the other initial
cells (`Vegas.SourceProgram.Setup.PrivateInputsIndependent`). This is a device
of the comparison of late deliveries, not a known limit of preservation; it
holds over an empty context and when a single player owns hidden cells, but a
correlated prior over private values, as in the private-value auction with a
non-product prior, is not covered by this theorem. -/
theorem onePacket_intended_sequentialEquilibrium_of_blindInputs (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependent)
    {delay bound : (graph setup).EventId → Nat}
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
    {slots : Nat}
    (inputs : ∀ sequence : ℕ → setup.intendedModel.BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed) →
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent setup.intendedModel
        (sequence n) setup.intended_decision_antichain) →
      InformationModel.BehavioralAssessmentConvergesPointwise sequence intended →
      OnePacketBlindInputs setup leaks bounds horizon scheduler parameter utility
        excludedPayoff upperUtility sequence slots) :
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
          (intendedReadoutExclusion setup parameter utility excludedPayoff) :=
  onePacket_intended_sequentialEquilibrium_of_openInputs setup leaks bounds horizon scheduler
    parameter utility excludedPayoff wellFormed independent contract timely retains intended
    equilibrium
    fun sequence mixed bayes converges =>
      (inputs sequence mixed bayes converges).toOpenInputs setup leaks bounds horizon scheduler
        parameter utility excludedPayoff wellFormed contract timely retains lower_le le_upper
        below mixed bayes

/-- **Sequential equilibrium of the bounded raw runtime from value blindness.**
Under the hypotheses of
`Vegas.onePacket_intended_sequentialEquilibrium_of_blindInputs`, bounds on the
utility, and a count-evidence service with a deposit covering the spread of the
exclusion payoff, there is a sequential equilibrium of the bounded raw runtime
under the exclusion payoff minus the deposit for each collected count charge,
that charges nobody on its paths, whose joint law of typed readout and realized
payoffs is the intended joint law of typed readout and exclusion payoff. -/
theorem onePacket_intended_raw_sequentialEquilibrium_of_blindInputs
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
    {slots : Nat}
    (inputs : ∀ sequence : ℕ → setup.intendedModel.BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed) →
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent setup.intendedModel
        (sequence n) setup.intended_decision_antichain) →
      InformationModel.BehavioralAssessmentConvergesPointwise sequence intended →
      OnePacketBlindInputs setup leaks bounds horizon scheduler parameter utility
        excludedPayoff upperUtility sequence slots)
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
          (intendedReadoutExclusion setup parameter utility excludedPayoff) :=
  onePacket_intended_raw_sequentialEquilibrium_of_openInputs setup leaks bounds horizon scheduler
    parameter utility excludedPayoff wellFormed independent contract timely retains intended
    equilibrium
    (fun sequence mixed bayes converges =>
      (inputs sequence mixed bayes converges).toOpenInputs setup leaks bounds horizon scheduler
        parameter utility excludedPayoff wellFormed contract timely retains lower_le le_upper
        below mixed bayes)
    service observationRate deliveryRate delivery_nonnegative coverage lowerUtility upperUtility
    lower_le le_upper deposit deposit_nonnegative sufficient

end Vegas
