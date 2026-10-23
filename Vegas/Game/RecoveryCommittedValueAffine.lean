/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryCommittedContinuationValue
import Vegas.Game.OnePacketCommitDecisionFailure
import Vegas.Game.OnePacketLateCommitments
import Vegas.Game.RecoveryKeyedFailure
import GameTheoryExtensions.Math.Probability.AffineDecorrelation

/-! # Keyed payoff factors under the actual common posterior -/

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
local notation "RApp" => recoveryApplication (runtime setup) leaks
local notation "RawNative" => ReactiveApplication.protocol (application setup leaks)
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks

local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)

open Classical in
/-- The original common posterior factors an arbitrary intended commitment
and its source continuation value. Only actual recovery service premises are used. -/
theorem nativeComparison_committed_value_sub_le [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p)) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    {who : Player} (site : (N).InformationSite who)
    (late : LateDelivery setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon (NativeScheduler) site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {unforced gamma : ℝ}
    (unforcedMass : expect ((nativeComparisonSequence setup leaks bounds horizon scheduler
      sequence scale positive le_one weights n).belief who site) (fun history =>
        if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1) ≤ unforced)
    (decorrelated : BeliefDecorrelated ((nativeComparisonSequence setup leaks bounds horizon
      scheduler sequence scale positive le_one weights n).belief who site)
      (fun history => operationalRecord setup leaks bounds horizon (NativeScheduler)
        history.1.trace)
      (fun history => nativeDecodedState setup leaks history.1.state) gamma)
    (choice : (N).Choice who site.1) (response : (application setup leaks).Action)
    (selected : choice.1 = some response) {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    {storedValue : L.Val payload}
    (after : material.call.candidateAfter who view.application.candidates (.prepared serial) =
      .openable ⟨payload, storedValue⟩)
    (offered : sourceOfValue setup event outputEq storedValue ∈
      setup.intendedMenu who (projectView setup leaks who site.1))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let target := nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
      positive le_one weights n
    let common := target.strategy
    let certificate := ((NMenu).bounded (initialLaw setup) horizon
      (NativeScheduler)).wellFoundedHistories
    let law := PMF.pure choice
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw site.1 law)
    let stopped := fun final : (NP).History => ¬ ClearState final.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
      exclusionBase setup parameter utility excludedPayoff leaks final.state who
    let error := (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
      (2 * horizon + 1)
    |expect (target.belief who site) (fun history =>
        expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff) -
      (excludedPayoff who +
        (1 - localFailure (2 * horizon + 1) target site
          {final | DecisionFailed key final.state} law) *
          (siteCommitValue setup leaks bounds horizon (NativeScheduler) parameter utility
            excludedPayoff target (setup.intendedOpeningProfile (sequence n).strategy) site
              (sourceOfValue setup event outputEq storedValue) - excludedPayoff who))| ≤
      error + 2 * payoffBound * unforced +
      4 * payoffBound * ((2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3) + unforced) +
      4 * payoffBound * gamma := by
  intro target common certificate law installed stopped payoff error
  let belief := target.belief who site
  let failure := fun history : (N).InformationHistory who site.1 =>
    expect (localHistoryRun (2 * horizon + 1) target site law history)
      (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0)
  let value := fun history : (N).InformationHistory who site.1 =>
    decodedCommitValue setup leaks bounds horizon (NativeScheduler) parameter utility
      excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) who (siteRank site.1)
        (sourceOfValue setup event outputEq storedValue) history.1
  let valueOf : setup.ProtocolState → ℝ := fun found => match found with
    | none => excludedPayoff who
    | some point => if IntendedReached setup point then
        expect (ProtocolState.step setup.program point
            (fun _ => sourceOfValue setup event outputEq storedValue))
          (sourcePointValue setup parameter utility excludedPayoff
            (setup.intendedOpeningProfile (sequence n).strategy) who) else excludedPayoff who
  let result := fun history : (N).InformationHistory who site.1 =>
    expect ((N).runBehavioralUntil certificate installed stopped history.1) payoff
  let lumping := nativeComparisonLumping setup leaks bounds horizon scheduler sequence scale
    positive
    le_one weights covers capacity n who
  let lumped := fun record : List (Option (OperationalState setup leaks)) =>
    expect ((fun law => law.bind (lumping.kernel key (none : LateOption bounds.candidateCount)))^[
        2 * horizon + 1]
      (PMF.pure (Sum.inr (committedImage event who (who, .prepared serial)
        (record.headD (operationalState setup leaks none)))))) (lumping.failure key)
  let pathError : ℝ := (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)
  have pathNonneg : 0 ≤ pathError := by
    have := (positive n).le
    dsimp only [pathError]
    positivity
  have errorNonneg : 0 ≤ error := by
    have retained := slotRetention_le_one (positive n).le (le_one n)
    have := (positive n).le
    dsimp only [error]
    positivity
  have failureUnit : ∀ history, 0 ≤ failure history ∧ failure history ≤ 1 := by
    intro history
    exact expect_mem_unit _ _ fun _ => by split <;> norm_num
  have lumpedUnit : ∀ record, 0 ≤ lumped record ∧ lumped record ≤ 1 := by
    intro record
    exact expect_mem_unit _ _ (lumping.failure_unit key)
  have valueBounded : ∀ found, |valueOf found| ≤ payoffBound := by
    intro found
    cases found with
    | none => exact excludedBounded
    | some point =>
        simp only [valueOf]
        split
        · exact expect_abs_le_of_bounded boundNonneg
            (fun _ => expect_abs_le_of_bounded boundNonneg readoutBounded)
        · exact excludedBounded
  have valueEq : ∀ history : (N).InformationHistory who site.1,
      value history = valueOf (nativeDecodedState setup leaks history.1.state) := by
    intro history
    obtain ⟨remaining, execution, current, _, _, ordered⟩ :=
      ordered_of_site setup leaks bounds horizon (NativeScheduler) atSite history
    unfold value decodedCommitValue
    rw [current]
    change _ = valueOf (decodedPoint setup execution.application.config)
    rw [decodedPoint_eq_of_isPrefix ordered]
    rfl
  have failureNear : expect belief (fun history => |failure history - lumped
      (operationalRecord setup leaks bounds horizon (NativeScheduler) history.1.trace)|) ≤
      pathError + unforced := by
    have pointwise : ∀ history ∈ belief.support,
        |failure history - lumped (operationalRecord setup leaks bounds horizon (NativeScheduler)
          history.1.trace)| ≤ pathError +
          if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1 := by
      intro history supported
      by_cases forced : ForcedState setup leaks who history.1.state
      · simp only [forced, ↓reduceIte, add_zero]
        have assembled := nativeComparisonSequence_assembled setup leaks bounds horizon scheduler
          sequence scale positive le_one weights
        have near := certificate_lateCommit_historyDecisionFailure setup leaks bounds horizon
          (NativeScheduler) sequence scale positive le_one
          (fun n => nativeComparisonWeights setup leaks bounds horizon scheduler (weights n))
          (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
            le_one weights) assembled n covers (by
              have := capacity who
              omega) (le_refl _) site late debtFree siteKey pending node atSite choice response
          selected sends packet after history forced
        have lumpedEq : lumped (operationalRecord setup leaks bounds horizon (NativeScheduler)
            history.1.trace) =
            certificateCommitFailure setup leaks bounds horizon (NativeScheduler) sequence scale
              positive le_one covers (by have := capacity who; omega) (le_refl _)
              (fun n => nativeComparisonWeights setup leaks bounds horizon scheduler (weights n))
              (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
                positive le_one weights) assembled n who key event serial history.1.state := by
          simp only [lumped, operationalRecord_headD]
          rfl
        rw [lumpedEq]
        exact near
      · simp only [forced, ↓reduceIte]
        have := failureUnit history
        have := lumpedUnit (operationalRecord setup leaks bounds horizon (NativeScheduler)
          history.1.trace)
        rw [abs_le]
        constructor <;> linarith
    have averaged := expect_mono pointwise (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
    rw [expect_add (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _),
      expect_constant] at averaged
    exact averaged.trans (by dsimp only [belief]; linarith [unforcedMass])
  have payoffNear : expect belief (fun history =>
      |result history - (excludedPayoff who +
        (1 - failure history) * (value history - excludedPayoff who))|) ≤
      error + 2 * payoffBound * unforced := by
    have payoffBounded : ∀ final, |payoff final| ≤ payoffBound := by
      intro final
      dsimp only [payoff]
      split
      · exact excludedBounded
      · rw [exclusionBase_eq_readout]
        exact readoutBounded _
    have pointwise : ∀ history ∈ belief.support,
        |result history - (excludedPayoff who +
          (1 - failure history) * (value history - excludedPayoff who))| ≤
        error + 2 * payoffBound *
          if ForcedState setup leaks who history.1.state then (0 : ℝ) else 1 := by
      intro history _supported
      by_cases forced : ForcedState setup leaks who history.1.state
      · simp only [forced, ↓reduceIte, mul_zero, add_zero]
        obtain ⟨remaining, execution, current, recallEq, observeEq, ordered⟩ :=
          ordered_of_site setup leaks bounds horizon (NativeScheduler) atSite history
        have actualAt : site.1 = some (execution.recall who,
            execution.observe (application setup leaks) who) := by
          simpa only [recallEq, observeEq] using atSite
        obtain ⟨point, decoded, intendedPoint, reachedPoint⟩ :=
          intendedReached_of_forced_debtFree wellFormed site debtFree history current ordered forced
        have member : response ∈ bounds.onePacketActions (runtime setup) leaks who
            (execution.recall who) (execution.observe (application setup leaks) who) := by
          obtain ⟨other, chosen, member⟩ := choice_response setup leaks bounds horizon
            (NativeScheduler) site actualAt choice
          cases Option.some.inj (selected.symm.trans chosen)
          exact member
        have pendingAt := pending
        rw [actualAt] at pendingAt
        have rawTrace := ((NMenu).toRawTrace (initialLaw setup) horizon (NativeScheduler)
          (current ▸ history.1.trace))
        have decided := decidedEvent_eq_of_pending setup leaks horizon (NativeScheduler) pendingAt
          rawTrace rfl (by simpa only [recallEq, observeEq, atSite] using siteKey)
        have near := nativeComparison_commitment_value_affine setup leaks bounds horizon scheduler
          wellFormed covers capacity sequence scale positive le_one weights n opportunity inclusion
          timely completes site choice response selected history current actualAt member material
          sends event packet pending key decided outputEq codeEq
          (by simpa only [observeEq] using after) ordered decoded intendedPoint offered parameter
          utility excludedPayoff boundNonneg readoutBounded excludedBounded
        have valueHere : value history = expect (ProtocolState.step setup.program point
            (fun _ => sourceOfValue setup event outputEq storedValue))
            (sourcePointValue setup parameter utility excludedPayoff
              (setup.intendedOpeningProfile (sequence n).strategy) who) := by
          dsimp only [value, decodedCommitValue]
          rw [current]
          simp only [decoded, reachedPoint, ↓reduceIte]
        rw [← valueHere] at near
        exact near
      · simp only [forced, ↓reduceIte, mul_one]
        have resultBound := expect_abs_le_of_bounded boundNonneg payoffBounded
          (μ := ((N).runBehavioralUntil certificate installed stopped history.1))
        have sourceBound : |value history| ≤ payoffBound := by rw [valueEq]; exact valueBounded _
        have failedUnit := failureUnit history
        have mixtureBound : |excludedPayoff who +
            (1 - failure history) * (value history - excludedPayoff who)| ≤ payoffBound := by
          rw [abs_le] at excludedBounded sourceBound ⊢
          constructor <;> nlinarith
        exact (abs_sub _ _).trans (by linarith)
    have averaged := expect_mono pointwise (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
    rw [expect_add (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _),
      expect_constant, expect_const_mul] at averaged
    have nonneg : 0 ≤ 2 * payoffBound := by linarith
    have scaled := mul_nonneg nonneg (sub_nonneg.mpr unforcedMass)
    dsimp only [belief] at averaged
    nlinarith
  have affine := abs_expect_affine_sub_le_of_decorrelated belief
    (fun history => operationalRecord setup leaks bounds horizon (NativeScheduler) history.1.trace)
    (fun history => nativeDecodedState setup leaks history.1.state) decorrelated failure result
      value
    lumped valueOf (excludedPayoff who)
    (fun history => by have := failureUnit history; rw [abs_le]; constructor <;> linarith)
    (fun record => by have := lumpedUnit record; rw [abs_le]; constructor <;> linarith)
    valueBounded valueEq excludedBounded failureNear payoffNear
  have failureEq : localFailure (2 * horizon + 1) target site
      {final | DecisionFailed key final.state} law = expect belief failure := by
    unfold localFailure
    rw [expect_localRun]
    rfl
  rw [failureEq]
  exact affine

end Vegas.RecoveryOnePacket
