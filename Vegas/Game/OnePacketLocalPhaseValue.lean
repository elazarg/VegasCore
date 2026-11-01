/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCompletionPoint
import Vegas.Game.OnePacketComparisonContinuationValue
import Vegas.Game.OnePacketLateLumping
import Vegas.Game.OnePacketSuccessorBoundary

/-! # Continuation transport through a local source-event response -/

noncomputable section

namespace Vegas.OnePacketComparison

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

open Classical in
/-- Current-event completion potentials approximate the common stopped future
value. The remaining bad mass is the actual missing-completion-point mass on success. -/
theorem local_phase_value_sub_le_of_boundary_values
    [∀ player, DecidableEq ((N).InfoState player)]
    (source : setup.intendedModel.BehavioralAssessment)
    (common : ∀ player, (N).BehavioralPolicy player)
    (terminalCompletes : ∀ (final : (application setup runtime leaks).Control),
      ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      final.execution.application.config.defaulted = ∅ →
      (application setup runtime leaks).terminal (some final) →
      final.execution.application.config.cut.Terminal)
    (certificate : (NP).WellFoundedHistories) (who : Player) (info : (N).InfoState who)
    (law : PMF ((N).Choice who info)) (history : (NP).History)
    {remaining : Nat} {execution : (application setup runtime leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (observed : (N).infoOf who history.trace = info)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some who) (key : LateKey setup runtime leaks)
    (decided : decidedEvent (runtime := runtime) key = some event)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound)
    (boundaryError : ℝ) (boundaryErrorNonneg : 0 ≤ boundaryError)
    (boundaryValues : ∀ (nextRank : Nat) (start : (NP).History)
      (anchor : (application setup runtime leaks).Execution),
      start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ →
      ReachedBoundary setup runtime leaks horizon scheduler nextRank anchor →
      ∀ point : ProtocolState setup.program,
      sourceServicePrefix? setup nextRank anchor.application.config = some point →
      ProtocolState.Intended setup.program point →
      let stopped := fun final : (NP).History => ¬ Clear final.state ∨
        DecodedState setup runtime leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure who setup.program) final.state
      |expect ((N).runBehavioralUntil certificate common stopped start)
          (fun final => if stopped final then excludedPayoff who else
            exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who) -
        sourcePointValue setup parameter utility excludedPayoff
          (setup.intendedOpeningProfile source.strategy) who point| ≤
        boundaryError *
          (application setup runtime leaks).rank horizon start.state) :
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw info law)
    let phase := fun final : (NP).History =>
      LateStopped setup runtime leaks bounds horizon scheduler rank final ∨ ¬ Clear
        final.state
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let fresh := fun control : (application setup runtime leaks).Control =>
      ¬ StoreEventFailed control.execution.application.config.store event
    let phaseLaw := (N).runBehavioralUntil certificate installed phase history
    let potential := fun final =>
      (completionPoint setup runtime leaks bounds horizon scheduler rank fresh final).elim
        (excludedPayoff who) (sourcePointValue setup parameter utility excludedPayoff
          (setup.intendedOpeningProfile source.strategy) who)
    |expect ((N).runBehavioralUntil certificate installed stopped history)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who) -
      expect phaseLaw potential| ≤
      boundaryError *
        (2 * horizon + 1) +
      2 * payoffBound * (phaseLaw.toOuterMeasure
        {final | completionPoint setup runtime leaks bounds horizon scheduler rank fresh
          final =
          none ∧ ¬ DecisionFailed (runtime := runtime) key final.state}).toReal := by
  intro installed phase stopped fresh phaseLaw potential
  let payoff := fun final : (NP).History => if stopped final then excludedPayoff who else
    exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
  let later := fun final : (NP).History =>
    expect ((N).runBehavioralUntil certificate installed stopped final) payoff
  let error := boundaryError *
    (2 * horizon + 1)
  let bad := {final : (NP).History |
    completionPoint setup runtime leaks bounds horizon scheduler rank fresh final = none ∧
      ¬ DecisionFailed (runtime := runtime) key final.state}
  have coefficientNonneg : 0 ≤ boundaryError := boundaryErrorNonneg
  have errorNonneg : 0 ≤ error := mul_nonneg coefficientNonneg (by positivity)
  have baseBounded : ∀ final : (NP).History,
      |exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who| ≤
        payoffBound := by
    intro final
    cases final.state with
    | none => simpa only [exclusionBase, abs_zero] using boundNonneg
    | some control =>
        change |if who ∈ control.execution.application.config.defaulted then excludedPayoff who
          else exclusionReadoutUtility setup parameter utility excludedPayoff
            (sourceReadout setup runtime leaks (some control)) who| ≤ payoffBound
        split
        · exact excludedBounded
        · exact readoutBounded _
  have payoffBounded : ∀ final, |payoff final| ≤ payoffBound := by
    intro final
    dsimp only [payoff]
    split
    · exact excludedBounded
    · exact baseBounded final
  have laterBounded : ∀ final, |later final| ≤ payoffBound :=
    fun _ => expect_abs_le_of_bounded boundNonneg payoffBounded
  have sourceBounded : ∀ point,
      |sourcePointValue setup parameter utility excludedPayoff
        (setup.intendedOpeningProfile source.strategy) who point| ≤ payoffBound := by
    intro point
    unfold sourcePointValue
    exact expect_abs_le_of_bounded boundNonneg readoutBounded
  have potentialBounded : ∀ final, |potential final| ≤ payoffBound := by
    intro final
    dsimp only [potential]
    cases completionPoint setup runtime leaks bounds horizon scheduler rank fresh final with
    | none => exact excludedBounded
    | some point => exact sourceBounded point
  have clear : execution.application.config.defaulted = ∅ :=
    defaulted_eq_empty_of_decodedIntended
      ((decodedPoint_eq_of_isPrefix ordered).trans decoded) intended
  have going : ¬ phase history := by
    rintro (⟨control, state, completed, done, atRank⟩ | unclear)
    · rw [current] at state
      cases Option.some.inj state
      have before := (ordered.2 completed).mp done
      omega
    · exact unclear (by rw [current]; exact clear)
  have running : ¬ (NP).terminal history.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have active : (NP).active history.state who := by rw [current]; rfl
  have splitLaw := debtStopped_eq_bind_eventPhase (runtime := runtime) certificate installed who
    history _ current
    ordered point decoded intended
  have pointwise : ∀ final ∈ phaseLaw.support,
      |later final - potential final| ≤ error +
        if final ∈ bad then 2 * payoffBound else 0 := by
    intro final member
    by_cases badFinal : final ∈ bad
    · rw [ite_eq_left badFinal]
      have := (abs_sub _ _).trans (add_le_add (laterBounded final) (potentialBounded final))
      linarith
    · rw [ite_eq_right badFinal, add_zero]
      cases found : completionPoint setup runtime leaks bounds horizon scheduler rank
        fresh final
          with
      | none =>
        have failed : DecisionFailed (runtime := runtime) key final.state := by
          by_contra notFailed
          exact badFinal ⟨found, notFailed⟩
        have debt : DecodedState setup runtime leaks (failureProfile setup.program)
            (ProtocolState.OwesFailure who setup.program) final.state := by
          cases state : final.state with
          | none => simp only [state, DecisionFailed] at failed
          | some control =>
              have failure : event ∈ control.execution.application.config.cut.completed ∧
                  StoreEventFailed control.execution.application.config.store event := by
                simpa only [state, DecisionFailed, decided] using failed
              simpa only [state] using decodedDebt_of_failed_event (runtime := runtime) final
                control state event failure.1 who owned failure.2
        have halt : stopped final := Or.inr debt
        dsimp only [later, potential]
        rw [(N).runBehavioralUntil_of_stopped certificate installed halt, expect_pure,
          show payoff final = excludedPayoff who from ite_eq_left halt, found]
        change |excludedPayoff who - excludedPayoff who| ≤ error
        simpa only [sub_self, abs_zero] using errorNonneg
      | some target =>
        obtain ⟨control, state, _completed, targetDecoded, targetIntended, _fresh⟩ :=
          completionPoint_spec (runtime := runtime) rank fresh final target found
        have decodedState : nativeDecodedState setup runtime leaks final.state = some target := by
          rw [state]
          exact targetDecoded
        obtain ⟨anchor, anchorState, _clear, _completed, atRank, boundary⟩ :=
          counted_stopped_boundary_of_intended (runtime := runtime) (completes :=
            terminalCompletes) certificate
            installed history current ordered event
            ready final member decodedState targetIntended
        have after := runUntil_after_localLaw_eq certificate
          ((bounds.onePacketMenu runtime leaks).decisionRecall (initialLaw setup) horizon
            scheduler).actsOnceWhereItMatters common who info law phase stopped history
          observed active running going final member
        have near := boundaryValues (rank + 1) final anchor anchorState boundary target atRank
          targetIntended
        have depth : (application setup runtime leaks).rank horizon final.state ≤ 2 * horizon + 1
          := by
          have := (application setup runtime leaks).trace_bound (initialLaw setup) horizon
            scheduler
            ((bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon
              scheduler final.trace)
          omega
        dsimp only [later, potential]
        rw [after, found]
        exact near.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast depth) coefficientNonneg)
  rw [splitLaw, expect_bind_tower_bounded _ _ _ payoffBounded]
  change |expect phaseLaw later - expect phaseLaw potential| ≤ _
  rw [← expect_sub (payoffIntegrable_of_bounded _ _ laterBounded)
    (payoffIntegrable_of_bounded _ _ potentialBounded)]
  let gap := fun final => later final - potential final
  have gapIntegrable : PayoffIntegrable phaseLaw gap :=
    payoffIntegrable_sub (payoffIntegrable_of_bounded _ _ laterBounded)
      (payoffIntegrable_of_bounded _ _ potentialBounded)
  have upper := expect_le_add_event_gap phaseLaw bad (fun _ => error) gap (2 * payoffBound)
    (payoffIntegrable_constant _ _) gapIntegrable
    (fun final member outside => by
      have := (abs_le.mp (pointwise final member)).2
      rw [ite_eq_right outside, add_zero] at this
      exact this)
    (fun final member inside => by
      have := (abs_le.mp (pointwise final member)).2
      simpa only [ite_eq_left inside] using this)
  have lower := expect_le_add_event_gap phaseLaw bad (fun _ => error) (fun final => -gap final)
    (2 * payoffBound) (payoffIntegrable_constant _ _) (payoffIntegrable_neg gapIntegrable)
    (fun final member outside => by
      have := (abs_le.mp (pointwise final member)).1
      rw [ite_eq_right outside, add_zero] at this
      linarith)
    (fun final member inside => by
      have := (abs_le.mp (pointwise final member)).1
      rw [ite_eq_left inside] at this
      linarith)
  rw [expect_constant] at upper lower
  rw [expect_neg] at lower
  exact abs_le.mpr ⟨by linarith, upper⟩


open Classical in
/-- The same assembled native assessment transports local stopped values to
source completion potentials, with only the actual exceptional stop mass. -/
theorem assembled_local_phase_value_sub_le
    [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      (NP).Trace (some control) → control.execution.application.config.defaulted = ∅ →
        OpportunityAt runtime leaks control.execution delay)
    (inclusion : ∀ control : (application setup runtime leaks).Control,
      (NP).Trace (some control) → control.execution.application.config.defaulted = ∅ →
        ProtectedInclusionAt runtime leaks control.execution bound)
    (timely : runtime.AsyncTimely delay bound)
    (completes : ∀ control : (application setup runtime leaks).Control,
      (NP).Trace (some control) → control.execution.application.config.defaulted = ∅ →
        (application setup runtime leaks).terminal (some control) →
          control.execution.application.config.cut.Terminal)
    (certificate : (NP).WellFoundedHistories) (who : Player) (info : (N).InfoState who)
    (law : PMF ((N).Choice who info)) (history : (NP).History)
    {remaining : Nat} {execution : (application setup runtime leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (observed : (N).infoOf who history.trace = info)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some who) (key : LateKey setup runtime leaks)
    (decided : decidedEvent (runtime := runtime) key = some event)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {payoffBound : ℝ} (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let common := (targetSequence n).strategy
    let installed := Profile.update (sig := (N).behavioralSignature) common who
      ((common who).withLaw info law)
    let phase := fun final : (NP).History =>
      LateStopped setup runtime leaks bounds horizon scheduler rank final ∨ ¬ Clear final.state
    let stopped := fun final : (NP).History => ¬ Clear final.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let fresh := fun control : (application setup runtime leaks).Control =>
      ¬ StoreEventFailed control.execution.application.config.store event
    let phaseLaw := (N).runBehavioralUntil certificate installed phase history
    let potential := fun final =>
      (completionPoint setup runtime leaks bounds horizon scheduler rank fresh final).elim
        (excludedPayoff who) (sourcePointValue setup parameter utility excludedPayoff
          (setup.intendedOpeningProfile (sequence n).strategy) who)
    |expect ((N).runBehavioralUntil certificate installed stopped history)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who) -
      expect phaseLaw potential| ≤
      (2 * payoffBound * (1 - slotRetention (scale n))) * (2 * horizon + 1) +
      2 * payoffBound * (phaseLaw.toOuterMeasure
        {final | completionPoint setup runtime leaks bounds horizon scheduler rank fresh final =
          none ∧ ¬ DecisionFailed (runtime := runtime) key final.state}).toReal := by
  apply local_phase_value_sub_le_of_boundary_values setup runtime leaks bounds horizon scheduler
    (sequence n) (targetSequence n).strategy completes certificate who info law history current
    observed event ready owned key decided ordered point decoded intended parameter utility
    excludedPayoff boundNonneg readoutBounded excludedBounded
    (2 * payoffBound * (1 - slotRetention (scale n))) (by
      have retention := slotRetention_le_one (positive n).le (le_one n)
      positivity)
  intro nextRank start anchor state boundary target atRank targetIntended
  exact assembled_stopped_boundary_value_sub_le setup runtime leaks bounds horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights targetSequence assembled n
    opportunity inclusion timely completes certificate nextRank start anchor state boundary target
    atRank targetIntended parameter utility excludedPayoff who boundNonneg
    (fun final => by
      cases final.state with
      | none => simpa only [exclusionBase, abs_zero] using boundNonneg
      | some control =>
          change |if who ∈ control.execution.application.config.defaulted then excludedPayoff who
            else exclusionReadoutUtility setup parameter utility excludedPayoff
              (sourceReadout setup runtime leaks (some control)) who| ≤ payoffBound
          split
          · exact excludedBounded
          · exact readoutBounded _) excludedBounded

end Vegas.OnePacketComparison
