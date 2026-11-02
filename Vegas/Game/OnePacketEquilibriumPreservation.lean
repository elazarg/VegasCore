/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketNonLateComparisons
import Vegas.Game.OnePacketKeyedComparisons
import Vegas.Game.OnePacketCommonCompletion
import Vegas.Game.OnePacketComparisonRetention
import Vegas.Game.OnePacketOwingOptimality
import Vegas.Game.OnePacketExclusionPayoff
import GameTheoryExtensions.Analysis.Protocol.LocalSimulationLimit
import GameTheoryExtensions.Analysis.Protocol.GainComparison

/-! # Intended sequential equilibria in the native one-packet runtime

One common native completion supplies the assessment sequence, operational
weights and consistent limit used by every local comparison. Its limiting
sequential equilibrium preserves the complete source configuration and fixed
exit payoff jointly, and every supported execution remains free of defaults.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  {Public : Type*} {signal : State L setup.context → Public}

local notation "Initial" => initialLaw setup
local notation "Menu" => bounds.onePacketMenu runtime leaks
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler

local instance nativeEquilibriumHistoryFintype : Fintype (E).History :=
  (Menu).historyFintype Initial horizon scheduler

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
private theorem intended_onePacket_sequentialEquilibrium_preserved_of_bounded_utility
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Opportunity runtime leaks Initial horizon scheduler delay)
    (inclusion : ProtectedInclusion runtime leaks Initial horizon scheduler bound)
    (completes : CompletesPlay runtime leaks Initial horizon scheduler)
    (timely : runtime.AsyncTimely delay bound)
    (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount) :
    ∃ native : (N).BehavioralAssessment,
      native.IsSequentialEquilibriumFor
        ((Menu).decisionInformationAntichain Initial horizon scheduler)
        (fun who site => native.truncatedContinuationContext site
          (fun final => exclusionBase setup runtime parameter utility excludedPayoff leaks
            final.state who) (2 * horizon + 1)) ∧
      (∀ final ∈ ((N).runBehavioral native.strategy (2 * horizon + 1)).support,
        ∀ control, final.state = some control →
          control.execution.application.config.defaulted = ∅) ∧
      ((N).runBehavioral native.strategy (2 * horizon + 1)).map
        (readoutExclusion setup runtime leaks bounds Initial horizon scheduler parameter utility
          excludedPayoff) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  classical
  obtain ⟨sourceSequence, sourceMixed, sourceBayes, sourceConverges, sourceRational⟩ :=
    setup.intended_exclusionSource wellFormed parameter utility excludedPayoff intended equilibrium
  let floors := fun n =>
    combinedFloor setup runtime leaks bounds horizon scheduler (sourceSequence n)
  let scale := fun n => trembleScale (floors n) (2 * horizon + 2) n
  have floorPositive := fun n =>
    combinedFloor_pos setup runtime leaks bounds horizon scheduler (sourceSequence n)
  have floorLeOne := fun n =>
    combinedFloor_le_one setup runtime leaks bounds horizon scheduler (sourceSequence n)
  have positive : ∀ n, 0 < scale n := fun n => trembleScale_pos (floorPositive n)
  have le_one : ∀ n, scale n ≤ 1 := fun n =>
    trembleScale_le_one (floorPositive n).le (floorLeOne n)
  have vanishes : Tendsto scale atTop (nhds 0) :=
    tendsto_trembleScale floors floorPositive floorLeOne
  obtain ⟨weights, sequence, limit, index, assembled, mixed, bayes, increasing, converges,
      consistent, pooled, _limits, freeOptimal, _publicOptimal⟩ :=
    setup.exists_onePacket_consistent_completion runtime leaks bounds Initial horizon scheduler
      parameter utility excludedPayoff sourceSequence bounds.candidateCount scale positive le_one
      vanishes
  have assembledNative : OnePacketAssembled setup runtime leaks bounds horizon scheduler
      sourceSequence scale positive le_one weights sequence := assembled
  let payoffBound : ℝ := ∑ player,
    (max 0 (max (excludedPayoff player) (upperUtility player)) -
      min 0 (min (excludedPayoff player) (lowerUtility player)))
  obtain ⟨nonnegative, readoutBounded, excludedBounded⟩ :=
    exclusionPayoffs_bounded setup parameter utility excludedPayoff lowerUtility upperUtility
      lower_le le_upper
  have payoffBounded : ∀ who (final : (E).History),
      |exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who| ≤
        payoffBound := by
    intro who final
    cases current : final.state with
    | none => simpa only [exclusionBase, abs_zero] using nonnegative
    | some control =>
        change |if who ∈ control.execution.application.config.defaulted then excludedPayoff who
          else exclusionReadoutUtility setup parameter utility excludedPayoff
            (sourceReadout setup runtime leaks (some control)) who| ≤ payoffBound
        split
        · exact excludedBounded who
        · exact readoutBounded who _
  obtain ⟨nonlateError, nonlateLimit, nonlateComparisons⟩ :=
    OnePacketComparison.assembled_nonlate_local_comparisons setup runtime leaks bounds horizon
      scheduler wellFormed independent observable covers coversInputs capacity sourceSequence
      sourceMixed sourceBayes scale positive le_one (fun _ => rfl) weights sequence assembledNative
      mixed bayes opportunity inclusion timely completes parameter utility excludedPayoff below
      upperUtility le_upper nonnegative readoutBounded excludedBounded payoffBounded
  obtain ⟨keyedError, keyedLimit, keyedComparisons⟩ :=
    if slotsPositive : 0 < bounds.candidateCount then
      OnePacketComparison.assembled_keyed_local_comparisons setup runtime leaks bounds horizon
        scheduler wellFormed independent observable sourceSequence sourceMixed sourceBayes scale
        positive le_one (fun _ => rfl) covers coversInputs capacity slotsPositive weights sequence
        assembledNative mixed bayes opportunity inclusion timely parameter utility excludedPayoff
        payoffBound nonnegative completes payoffBounded excludedBounded below upperUtility le_upper
        readoutBounded pooled
    else
      ⟨fun _ => 0, tendsto_const_nhds, by
        intro _ who _ _ _ _ _
        have impossible := capacity who
        omega⟩
  let error := fun n => |nonlateError n| + |keyedError n|
  have errorVanishes : Tendsto error atTop (nhds 0) := by
    simpa only [abs_zero, add_zero] using nonlateLimit.abs.add keyedLimit.abs
  have comparisons : ∀ n who (site : (N).InformationSite who),
      ¬ FreeAgent setup runtime leaks bounds Initial horizon scheduler ((N).agentAt site) →
      ∀ choice : (N).Choice who site.1,
        localGain (2 * horizon + 1) (fun final => final.state)
            (exclusionBase setup runtime parameter utility excludedPayoff leaks)
              (sequence n) site (PMF.pure choice) ≤ error n ∨
        ∃ mixture : PMF (setup.intendedModel.AssessmentDeviation who),
          localGain (2 * horizon + 1) (fun final => final.state)
              (exclusionBase setup runtime parameter utility excludedPayoff leaks)
                (sequence n) site (PMF.pure choice) ≤
            expect mixture (intendedSiteGain setup parameter utility excludedPayoff
              (sourceSequence n)) + error n := by
    intro n who site notFree choice
    by_cases owing : OwingAgent setup runtime leaks bounds Initial horizon scheduler
        ((N).agentAt site)
    · left
      rw [owingAgent_localGain_eq_zero setup runtime leaks bounds horizon scheduler parameter
        utility excludedPayoff completes (sequence n) site owing]
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    by_cases keyed : ownedKeyed
        (FreeAgent setup runtime leaks bounds Initial horizon scheduler)
        (LateDeliveryAgent setup runtime leaks bounds Initial horizon scheduler) ((N).agentAt site)
    · have bounded := keyedComparisons n who site notFree owing keyed choice
      exact GainComparison.mono_error bounded (by
        dsimp only [error]
        linarith [le_abs_self (keyedError n), abs_nonneg (nonlateError n)])
    · have bounded := nonlateComparisons n who site notFree owing keyed choice
      exact GainComparison.mono_error bounded (by
        dsimp only [error]
        linarith [le_abs_self (nonlateError n), abs_nonneg (keyedError n)])
  let sourceObserve := intendedReadoutExclusion setup parameter utility excludedPayoff
  let targetObserve := readoutExclusion setup runtime leaks bounds Initial horizon scheduler
    parameter utility excludedPayoff
  let lawError := fun n => ((min (Fintype.card Player) 1 * horizon : ℕ) : ℝ) *
    (1 - slotRetention (scale n))
  have lawVanishes : Tendsto lawError atTop (nhds 0) := by
    simpa [lawError] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_slotRetention vanishes)).const_mul
        (((min (Fintype.card Player) 1 * horizon : ℕ) : ℝ))
  have initialized : ∀ n outcome,
      |((((N).runBehavioral (sequence n).strategy (2 * horizon + 1)).map targetObserve)
          outcome).toReal -
        (((setup.intendedModel.runBehavioral (sourceSequence n).strategy
          (instructionCount setup.program + 1)).map sourceObserve) outcome).toReal| ≤ lawError n :=
      by
    intro n outcome
    exact (OnePacketComparison.assembled_initialized_readout_exclusion_withinTV setup runtime
      leaks bounds horizon scheduler wellFormed covers capacity sourceSequence scale positive
      le_one weights sequence assembledNative n
      (fun control trace _ => opportunity control
        ((Menu).toRawTrace Initial horizon scheduler trace))
      (fun control trace _ => inclusion control
        ((Menu).toRawTrace Initial horizon scheduler trace)) timely
      (fun control trace _ ended => completes control
        ((Menu).toRawTrace Initial horizon scheduler trace) ended)
      parameter utility excludedPayoff).apply outcome
  obtain ⟨nativeSE, nativeLaw⟩ :=
    sequentialEquilibrium_of_copied_comparisons_limit_of_lawError sourceObserve targetObserve
      (instructionCount setup.program + 1) (2 * horizon + 1)
      ((Menu).bounded Initial horizon scheduler) ((Menu).decisionRecall Initial horizon scheduler)
      (payoffComponent setup) intended sourceSequence sourceConverges sourceRational sequence
      (fun _ site => ¬ FreeAgent setup runtime leaks bounds Initial horizon scheduler
        ((N).agentAt site)) error errorVanishes
      (fun n who site notFree choice => by
        have compared := comparisons n who site notFree choice
        unfold intendedSiteGain payoffComponent at compared
        simpa only [localGain, assessmentComparisonWith, expect_map, targetObserve, sourceObserve,
          readoutExclusion, payoffComponent, Function.comp_def] using compared)
      lawError lawVanishes initialized limit index increasing converges consistent
      (fun who site free law => by
        rw [← limit.continuationContext_eq_truncated_of_bounded
          ((Menu).bounded Initial horizon scheduler).wellFoundedHistories
          ((Menu).bounded Initial horizon scheduler)]
        exact freeOptimal who site (not_not.mp free) law)
  have readoutLaw := congrArg (fun law => law.map Prod.fst) nativeLaw
  simp only [PMF.map_comp, targetObserve, sourceObserve, readoutExclusion,
    intendedReadoutExclusion, Function.comp_def] at readoutLaw
  refine ⟨limit, nativeSE, ?_, nativeLaw⟩
  intro final supported control current
  exact onePacket_defaulted_eq_empty_of_readout_law setup runtime leaks bounds Initial horizon
    scheduler wellFormed intended.strategy limit.strategy (2 * horizon + 1) readoutLaw final
      supported control current

private theorem exists_bounded_utility_extension
    {History Outcome Agent : Type*} [Finite History]
    (readout : History → Option Outcome) (payoff : Outcome → Agent → ℝ) :
    ∃ extension : Outcome → Agent → ℝ, ∃ bound : Agent → ℝ,
      (∀ who, 0 ≤ bound who) ∧
      (∀ outcome who, |extension outcome who| ≤ bound who) ∧
      ∀ history outcome, readout history = some outcome → extension outcome = payoff outcome := by
  classical
  let := Fintype.ofFinite History
  let bound := fun who => ∑ history, |(readout history).elim 0 (fun outcome => payoff outcome who)|
  let extension := fun outcome who =>
    if ∃ history, readout history = some outcome then payoff outcome who else 0
  have nonnegative : ∀ who, 0 ≤ bound who :=
    fun _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨extension, bound, nonnegative, ?_, ?_⟩
  · intro outcome who
    by_cases represented : ∃ history, readout history = some outcome
    · simp only [extension, ite_eq_left represented]
      obtain ⟨history, observed⟩ := represented
      have bounded := Finset.single_le_sum
        (fun other (_ : other ∈ Finset.univ) =>
          abs_nonneg ((readout other).elim 0 (fun result => payoff result who)))
        (Finset.mem_univ history)
      simpa only [observed, Option.elim_some] using bounded
    · simpa only [extension, ite_eq_right represented, abs_zero] using nonnegative who
  · intro history outcome observed
    funext who
    exact ite_eq_left ⟨history, observed⟩

open Classical in
/-- Every intended sequential equilibrium has an actual native one-packet
implementation with the same joint configuration and base payoff law. -/
theorem intended_onePacket_sequentialEquilibrium_preserved
    (wellFormed : setup.WellFormed)
    (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Opportunity runtime leaks Initial horizon scheduler delay)
    (inclusion : ProtectedInclusion runtime leaks Initial horizon scheduler bound)
    (completes : CompletesPlay runtime leaks Initial horizon scheduler)
    (timely : runtime.AsyncTimely delay bound)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount) :
    ∃ native : (N).BehavioralAssessment,
      native.IsSequentialEquilibriumFor
        ((Menu).decisionInformationAntichain Initial horizon scheduler)
        (fun who site => native.truncatedContinuationContext site
          (fun final => exclusionBase setup runtime parameter utility excludedPayoff leaks
            final.state who) (2 * horizon + 1)) ∧
      (∀ final ∈ ((N).runBehavioral native.strategy (2 * horizon + 1)).support,
        ∀ control, final.state = some control →
          control.execution.application.config.defaulted = ∅) ∧
      ((N).runBehavioral native.strategy (2 * horizon + 1)).map
        (readoutExclusion setup runtime leaks bounds Initial horizon scheduler parameter utility
          excludedPayoff) =
        (setup.intendedModel.runBehavioral intended.strategy
          (instructionCount setup.program + 1)).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  classical
  let readout : setup.intendedProtocol.History ⊕ (E).History →
      Option (Parameter × PublicOutcome setup.program) := fun history =>
    (Sum.elim (fun source => setup.protocolReadout source.state)
      (fun native => sourceReadout setup runtime leaks native.state) history).map
        (setup.parameterOutcome parameter)
  obtain ⟨extension, bound, nonnegative, bounded, agrees⟩ :=
    exists_bounded_utility_extension readout utility
  have sourceAgrees (history : setup.intendedProtocol.History) terminal
      (observed : setup.protocolReadout history.state = some terminal) :
      extension (setup.parameterOutcome parameter terminal) =
        utility (setup.parameterOutcome parameter terminal) := by
    exact agrees (.inl history) _ (by simp only [readout, Sum.elim_inl, observed, Option.map_some])
  have nativeAgrees (history : (E).History) terminal
      (observed : sourceReadout setup runtime leaks history.state = some terminal) :
      extension (setup.parameterOutcome parameter terminal) =
        utility (setup.parameterOutcome parameter terminal) := by
    exact agrees (.inr history) _ (by simp only [readout, Sum.elim_inr, observed, Option.map_some])
  have sourcePayoff :
      (fun who (history : setup.intendedProtocol.History) =>
        (setup.protocolReadout history.state).elim 0
          (fun terminal => extension (setup.parameterOutcome parameter terminal) who)) =
      (fun who (history : setup.intendedProtocol.History) =>
        (setup.protocolReadout history.state).elim 0
          (fun terminal => utility (setup.parameterOutcome parameter terminal) who)) := by
    funext who history
    cases observed : setup.protocolReadout history.state with
    | none => rfl
    | some terminal => exact congrFun (sourceAgrees history terminal observed) who
  have extensionEquilibrium : setup.IntendedSequentialEquilibrium parameter extension intended := by
    unfold Setup.IntendedSequentialEquilibrium at equilibrium ⊢
    rw [sourcePayoff]
    exact equilibrium
  have extensionBelow : ∀ (history : setup.intendedProtocol.History) terminal,
      setup.protocolReadout history.state = some terminal →
        ∀ who, excludedPayoff who ≤ extension (setup.parameterOutcome parameter terminal) who := by
    intro history terminal observed who
    rw [sourceAgrees history terminal observed]
    exact below history terminal observed who
  obtain ⟨native, rational, clear, law⟩ :=
    intended_onePacket_sequentialEquilibrium_preserved_of_bounded_utility parameter extension
      excludedPayoff wellFormed independent observable opportunity inclusion completes timely
      (fun who => -bound who) bound
      (fun outcome who => (abs_le.mp (bounded outcome who)).1)
      (fun outcome who => (abs_le.mp (bounded outcome who)).2)
      extensionBelow intended extensionEquilibrium covers coversInputs capacity
  have readoutPayoff {readout : Option (Config Player L setup.program.terminalCtx)}
      (same : ∀ terminal, readout = some terminal →
        extension (setup.parameterOutcome parameter terminal) =
          utility (setup.parameterOutcome parameter terminal)) :
      exclusionReadoutUtility setup parameter extension excludedPayoff readout =
        exclusionReadoutUtility setup parameter utility excludedPayoff readout := by
    funext who
    cases observed : readout with
    | none => rfl
    | some terminal =>
      simp only [exclusionReadoutUtility, Option.elim_some, exclusionTerminalUtility,
        exclusionUtility]
      rw [same terminal observed]
  have nativePayoff (history : (E).History) :
      exclusionBase setup runtime parameter extension excludedPayoff leaks history.state =
        exclusionBase setup runtime parameter utility excludedPayoff leaks history.state := by
    have readoutSame := readoutPayoff (nativeAgrees history)
    funext who
    cases current : history.state with
    | none => rfl
    | some control =>
      simp only [exclusionBase, current] at readoutSame ⊢
      rw [congrFun readoutSame who]
  have nativeObservation :
      readoutExclusion setup runtime leaks bounds Initial horizon scheduler parameter extension
          excludedPayoff =
        readoutExclusion setup runtime leaks bounds Initial horizon scheduler parameter utility
          excludedPayoff := by
    funext history
    exact congrArg (fun payoff => (sourceReadout setup runtime leaks history.state, payoff))
      (nativePayoff history)
  have sourceObservation : intendedReadoutExclusion setup parameter extension excludedPayoff =
      intendedReadoutExclusion setup parameter utility excludedPayoff := by
    funext history
    exact congrArg (fun payoff => (setup.protocolReadout history.state, payoff))
      (readoutPayoff (sourceAgrees history))
  refine ⟨native, ?_, clear, ?_⟩
  · have same :
        (fun who (history : (E).History) => exclusionBase setup runtime parameter extension
          excludedPayoff leaks history.state who) =
        (fun who (history : (E).History) => exclusionBase setup runtime parameter utility
          excludedPayoff leaks history.state who) := by
      funext who history
      exact congrFun (nativePayoff history) who
    change native.IsSequentialEquilibriumFor _
      (fun who site => native.truncatedContinuationContext site
        ((fun player (history : (E).History) => exclusionBase setup runtime parameter extension
          excludedPayoff leaks history.state player) who) (2 * horizon + 1)) at rational
    rw [same] at rational
    exact rational
  · rwa [nativeObservation, sourceObservation] at law

end Vegas
