/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryCommitmentGainBounds
import Vegas.Game.RecoverySilenceComparison
import Vegas.Game.RecoveryDisclosureComparison
import Vegas.Game.RecoveryUnintendedComparison
import Vegas.Game.RecoveryNonLateChoices
import Vegas.Game.RecoverySourceBeliefBounds
import Vegas.Game.RecoveryIrregularBeliefBounds
import Vegas.Game.RecoveryFirstActivationValue
import Vegas.Game.RecoveryCompletionPotential
import Vegas.Game.IntendedChoiceReach
import Vegas.Game.OnePacketNonLateValueBlind

/-! # Uniform source incentive bounds for nonlate commitments -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)
local notation "Menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))

open Classical in
/-- All pure nonlate pending responses compare with exclusion or an original
source deviation, with one error vanishing uniformly over information sites. -/
theorem nativeComparison_nonlate_pending_comparisons [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [Finite setup.intendedProtocol.History]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependent)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (upper : Player → ℝ) (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who) (choice : (N).Choice who site.1),
        ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ¬ LateDelivery setup leaks who site.1 →
        ∀ {event : (graph setup).EventId}, pendingEvent setup leaks who site.1 = some event →
        let common := nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
          positive le_one weights n
        let certificate := ((Menu).bounded (initialLaw setup) horizon
          (NativeScheduler)).wellFoundedHistories
        let stopped := fun final : (NP).History => ¬ Clear final.state ∨
          DecodedState setup leaks (failureProfile setup.program)
            (ProtocolState.OwesFailure who setup.program) final.state
        let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
          exclusionBase setup parameter utility excludedPayoff leaks final.state who
        let gain := expect ((nativeComparisonSequence setup leaks bounds horizon scheduler sequence
          scale positive le_one weights n).belief who site) (fun history =>
            expect ((N).runBehavioralUntil certificate
                (Profile.update (sig := (N).behavioralSignature) common who
                  ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
              expect ((N).runBehavioralUntil certificate common stopped history.1) payoff)
        gain ≤ error n ∨ ∃ sourceDeviation : setup.intendedModel.AssessmentDeviation who,
          gain ≤ intendedSiteGain setup parameter utility excludedPayoff (sequence n)
            sourceDeviation + error n := by
  obtain ⟨commitError, commitLimit, commitments⟩ :=
    nativeComparison_intendedCommitment_gain_bounds setup leaks bounds horizon scheduler
      wellFormed independent covers coversInputs capacity sequence sourceMixed sourceBayes scale
      positive le_one scaleEq weights opportunity inclusion timely completes parameter utility
      excludedPayoff below upper le_upper boundNonneg readoutBounded excludedBounded
  obtain ⟨drift, driftLimit, irregular⟩ := nativeComparison_irregular_bounds setup leaks bounds
    horizon scheduler wellFormed independent sequence sourceMixed scale positive le_one scaleEq
    covers coversInputs capacity weights
  let rowError := fun n =>
    2 * ((2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
      (2 * horizon + 1)) + 2 * payoffBound * (1 - slotRetention (scale n)) +
    2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1)) +
    (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
      (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound)
  let error := fun n => |commitError n| + rowError n + 2 * payoffBound * |drift n|
  have scaleLimit : Tendsto scale atTop (nhds 0) := by
    have identity : scale = fun n => trembleScale
        (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
        (2 * horizon + 2) n := funext scaleEq
    rw [identity]
    exact tendsto_trembleScale _
      (fun n => combinedFloor_pos setup leaks bounds horizon (NativeScheduler) (sequence n))
      (fun n => combinedFloor_le_one setup leaks bounds horizon (NativeScheduler) (sequence n))
  have retentionLimit : Tendsto (fun n => 1 - slotRetention (scale n)) atTop (nhds 0) := by
    simpa only [sub_self] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_slotRetention scaleLimit)
  have cubeLimit : Tendsto (fun n => scale n ^ 3) atTop (nhds 0) := by
    simpa using scaleLimit.pow 3
  have rowLimit : Tendsto rowError atTop (nhds 0) := by
    have first := (((retentionLimit.const_mul (Fintype.card Player : ℝ)).const_mul
      (2 * payoffBound)).mul_const (2 * horizon + 1 : ℝ)).const_mul 2
    have physical := (((cubeLimit.add ((cubeLimit.add cubeLimit).const_mul
      (2 * horizon + 1 : ℝ))).const_mul 2).mul_const (2 * horizon + 1 : ℝ)).add
      (cubeLimit.mul_const (2 * horizon + 1 : ℝ))
    convert (((first.add (retentionLimit.const_mul (2 * payoffBound))).add
      ((cubeLimit.mul_const (2 * horizon + 1 : ℝ)).const_mul (2 * payoffBound))).add
      (physical.mul_const (2 * payoffBound))) using 1 <;> norm_num [rowError]
  have errorLimit : Tendsto error atTop (nhds 0) := by
    simpa only [abs_zero, zero_mul, mul_zero, add_zero, zero_add] using
      ((commitLimit.abs.add rowLimit).add ((driftLimit.abs).const_mul (2 * payoffBound)))
  refine ⟨error, errorLimit, ?_⟩
  intro n who site choice notFree notOwing nonlate event pending common certificate stopped payoff
    gain
  have rowNonneg : 0 ≤ rowError n := by
    have retention := slotRetention_le_one (positive n).le (le_one n)
    have := (positive n).le
    dsimp only [rowError]
    positivity
  have errorCovers : commitError n ≤ error n := by
    dsimp only [error]
    have : 0 ≤ 2 * payoffBound * |drift n| := by positivity
    linarith [le_abs_self (commitError n)]
  by_cases intendedChoice : IntendedCommitment setup leaks bounds horizon (NativeScheduler) site
      choice
  · right
    obtain ⟨past, view, response, material, named, serial, payload, outputEq, value,
      atSite, selected, sends, packet, _after, _legal⟩ := intendedChoice
    have submitted : (runtime setup).submittedEvent? leaks response = some named := by
      unfold EventGraphRuntime.submittedEvent?
      simp only [sends, packet, Payload.event?]
    have atTurn := commitsAtTurn_of_notOwing wellFormed site notOwing choice selected submitted
    obtain ⟨deviation, bounded⟩ := commitments n who site choice notFree notOwing nonlate atTurn
      ⟨past, view, response, material, named, serial, payload, outputEq, value,
        atSite, selected, sends, packet, _after, _legal⟩
    exact ⟨deviation, bounded.trans (by linarith only [errorCovers])⟩
  left
  obtain ⟨past, view, atSite⟩ : ∃ past view, site.1 = some (past, view) := by
    cases observed : site.1 with
    | none => rw [observed] at pending; cases pending
    | some pair => exact ⟨pair.1, pair.2, rfl⟩
  obtain ⟨response, selected, member⟩ := choice_response setup leaks bounds horizon
    (NativeScheduler) site atSite choice
  have regularRows : ∀ history : (N).InformationHistory who site.1,
      RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) who history.1.trace →
      expect ((N).runBehavioralUntil certificate
          (Profile.update (sig := (N).behavioralSignature) common who
            ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
        expect ((N).runBehavioralUntil certificate common stopped history.1) payoff ≤ rowError n :=
      by
    intro history regular
    cases sends : response.transmission with
    | none =>
        have silent : choice.1 = some ⟨none⟩ := by
          rw [selected]
          congr 1
          exact congrArg (fun transmission =>
            (⟨transmission⟩ : (application setup leaks).Action)) sends
        exact nativeComparison_silence_history_comparison setup leaks bounds horizon scheduler
          wellFormed covers capacity sequence scale positive le_one weights n opportunity inclusion
          timely completes site choice notFree notOwing nonlate event pending silent atSite
          parameter utility excludedPayoff below (upper who) (fun outcome => le_upper outcome who)
          boundNonneg (readoutBounded who) (excludedBounded who) history regular
    | some material =>
        obtain ⟨named, submitted⟩ := submittedEvent_of_transmits setup leaks bounds member sends
        have atTurn := commitsAtTurn_of_notOwing wellFormed site notOwing choice selected submitted
        cases packet : material.call.packet with
        | malformed raw => exact (onePacket_not_malformed bounds member sends raw packet).elim
        | commitment named candidate =>
            have near := nativeComparison_unintendedCommitment_history_comparison setup leaks
              bounds horizon scheduler wellFormed covers capacity sequence scale positive le_one
              weights n opportunity inclusion timely completes site choice notFree notOwing nonlate
              atTurn intendedChoice atSite response selected material sends named candidate packet
              parameter utility excludedPayoff below (upper who)
              (fun outcome => le_upper outcome who) boundNonneg (readoutBounded who)
              (excludedBounded who) history regular
            have := (positive n).le
            have retention := slotRetention_le_one (positive n).le (le_one n)
            dsimp only [rowError]
            exact near.trans (by
              have retained : 0 ≤ 2 * payoffBound *
                  (Fintype.card Player * (1 - slotRetention (scale n))) *
                  (2 * horizon + 1) := by positivity
              have extra : 0 ≤ 2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1)) +
                  (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
                    (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound) := by
                positivity
              linarith)
        | opening named handle raw =>
            have forced := forcedAgent_of_not_free setup leaks bounds horizon (NativeScheduler)
              notFree
            have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon (NativeScheduler)
              notOwing
            have ownIntended := ownCompletionsIntended_of_siteNotOwes wellFormed debtFree history
            have allDebtFree := not_owesFailure_of_regular wellFormed (sequence n) atSite forced
              history regular ownIntended
            have stateForced := forcedState_of_regular wellFormed (sequence n) atSite forced
              history regular ownIntended
            obtain ⟨remaining, execution, point, current, actualAt, never, ordered, decoded,
              intended, reached⟩ := firstActivation_history_facts setup leaks bounds horizon
                (NativeScheduler)
                wellFormed site pending nonlate history stateForced allDebtFree
            have namedEq : named = event := by
              have fromPacket : (runtime setup).submittedEvent? leaks response = some named := by
                unfold EventGraphRuntime.submittedEvent?
                simp only [sends, packet, Payload.event?]
              have pendingNamed := pendingEvent_of_turnSubmission setup leaks bounds horizon
                (NativeScheduler) site atSite (by
                  obtain ⟨p, v, r, e, seen, chosen, submittedAt, turn⟩ := atTurn
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (atSite.symm.trans seen))
                  have rEq := Option.some.inj (selected.symm.trans chosen)
                  subst r
                  have eEq := Option.some.inj (fromPacket.symm.trans submittedAt)
                  subst e
                  exact turn) choice selected fromPacket
              exact Option.some.inj (pendingNamed.symm.trans pending)
            subst named
            obtain ⟨payload, binding, checks, outputEq, codeEq, _node⟩ :=
              onePacket_opening_node member sends packet
            let key := LateKey.ofView setup leaks who (execution.recall who)
              (execution.observe (application setup leaks) who)
            have pendingHere := pending
            rw [actualAt] at pendingHere
            have decided := decidedEvent_eq_of_pending setup leaks horizon (NativeScheduler)
              pendingHere ((Menu).toRawTrace (initialLaw setup) horizon (NativeScheduler)
                (current ▸ history.1.trace)) rfl
              (lateKey_some who (execution.recall who)
                (execution.observe (application setup leaks) who))
            have near := nativeComparison_firstActivation_disclosure_gain_le setup leaks bounds
              horizon scheduler wellFormed covers capacity sequence scale positive le_one weights n
              opportunity inclusion timely completes site (PMF.pure choice) history current actualAt
              event pending never key decided outputEq codeEq ordered decoded intended reached
              parameter utility excludedPayoff below (upper who)
              (fun outcome => le_upper outcome who) boundNonneg (readoutBounded who)
              (excludedBounded who)
            have := (positive n).le
            dsimp only [rowError]
            exact near.trans (by
              have extra : 0 ≤ 2 * payoffBound * (scale n ^ 3 * (2 * horizon + 1)) +
                  (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
                    (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * payoffBound) := by
                positivity
              linarith)
  let belief := (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
    positive le_one weights n).belief who site
  let native := fun history : (N).InformationHistory who site.1 =>
    expect ((N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) common who
          ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1) payoff -
      expect ((N).runBehavioralUntil certificate common stopped history.1) payoff
  let bad := fun history : (N).InformationHistory who site.1 =>
    if RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) who
      history.1.trace then (0 : ℝ) else 1
  have payoffBounded : ∀ final, |payoff final| ≤ payoffBound := by
    intro final
    dsimp only [payoff]
    split
    · exact excludedBounded who
    · rw [exclusionBase_eq_readout]
      exact readoutBounded who _
  have rows : ∀ history, native history ≤ rowError n + 2 * payoffBound * bad history := by
    intro history
    by_cases regular : RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) who
        history.1.trace
    · simpa only [bad, regular, ↓reduceIte, mul_zero, add_zero] using regularRows history regular
    · have first := expect_abs_le_of_bounded (μ := (N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) common who
          ((common who).withLaw site.1 (PMF.pure choice))) stopped history.1)
        boundNonneg payoffBounded
      have second := expect_abs_le_of_bounded
        (μ := (N).runBehavioralUntil certificate common stopped history.1)
        boundNonneg payoffBounded
      dsimp only [native, bad]
      rw [ite_eq_right regular, mul_one]
      linarith [(abs_le.mp first).2, (abs_le.mp second).1]
  have averaged := expect_mono (μ := belief) (fun history _ => rows history)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  rw [expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    expect_constant, expect_const_mul] at averaged
  have pendingHere := pending
  rw [atSite] at pendingHere
  have rare := irregular n who site notFree notOwing atSite (pendingEvent_spec pendingHere).1
  have scaled : 2 * payoffBound * expect belief bad ≤ 2 * payoffBound * |drift n| :=
    mul_le_mul_of_nonneg_left (rare.trans (le_abs_self (drift n)))
      (by positivity : 0 ≤ 2 * payoffBound)
  have complete : expect belief native ≤ rowError n + 2 * payoffBound * |drift n| := by
    linarith only [averaged, scaled]
  change expect belief native ≤ error n
  dsimp only [error]
  linarith only [complete, abs_nonneg (commitError n)]

end Vegas.RecoveryOnePacket
