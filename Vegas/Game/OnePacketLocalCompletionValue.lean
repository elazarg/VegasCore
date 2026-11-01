/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLocalPhaseValue
import Vegas.Game.OnePacketCompletionPotential
import Vegas.Game.OnePacketEventPhaseLaw

/-! # Physical completion values for native local responses -/

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
/-- Native local continuation values approximate physical completion values,
with exceptional mass measured by the actual bad-stop observable. -/
theorem local_completion_value_sub_le_of_boundary_values
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
    |expect ((N).runBehavioralUntil certificate installed stopped history)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who) -
      expect phaseLaw (completionValue setup runtime leaks bounds horizon scheduler parameter
        utility excludedPayoff (setup.intendedOpeningProfile source.strategy) rank fresh who
        (fun _ => excludedPayoff who))| ≤
      boundaryError *
        (2 * horizon + 1) +
      2 * payoffBound * expect phaseLaw
        (lateBadStop setup runtime leaks bounds horizon scheduler rank fresh event) := by
  intro installed phase stopped fresh phaseLaw
  have clear : execution.application.config.defaulted = ∅ :=
    defaulted_eq_empty_of_decodedIntended
      ((decodedPoint_eq_of_isPrefix ordered).trans decoded) intended
  have phaseEq := pending_until_eq_clearUntil (runtime := runtime) certificate installed history
    current ordered clear event ready
  have completed : ∀ final ∈ phaseLaw.support,
      ∃ control : (application setup runtime leaks).Control, final.state = some control ∧
        event ∈ control.execution.application.config.cut.completed := by
    intro final supported
    have lateMember : final ∈ ((N).runBehavioralUntil certificate installed
        (LateStopped setup runtime leaks bounds horizon scheduler rank) history).support := by
      rw [phaseEq]
      exact supported
    obtain ⟨anchor, state, action, primary, sampled, drained⟩ :=
      lateStop_primary_drain (runtime := runtime) certificate installed ordered ready
        (fun last trace ended same => by
          have lastClear : last.execution.application.config.defaulted = ∅ := by
            rw [same]
            exact clear
          rw [terminalCompletes last trace lastClear ended]
          exact Finset.mem_univ _) history current rfl final lateMember
    refine ⟨anchor, state, ?_⟩
    rw [drained]
    apply EventGraph.Config.Step.path_completed_mono primary.drain_graph_steps
    rw [execution.application.config.step_cut event ready action primary.config sampled]
    exact (EventOrder.Cut.mem_complete _ event ready event).mpr (Or.inl rfl)
  have badMass := completionPoint_badMass_eq_lateBadStop phaseLaw rank key event decided fresh
    completed
  have comparison := local_phase_value_sub_le_of_boundary_values setup runtime leaks bounds
    horizon scheduler source common terminalCompletes certificate who info law history current
    observed event ready owned key decided ordered point decoded intended parameter utility
    excludedPayoff boundNonneg readoutBounded excludedBounded boundaryError boundaryErrorNonneg
    boundaryValues
  dsimp only at comparison
  rw [badMass] at comparison
  exact comparison


open Classical in
/-- The same assembled native assessment transports local stopped values to
physical completion values, with only the actual exceptional stop mass. -/
theorem assembled_local_completion_value_sub_le
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
    |expect ((N).runBehavioralUntil certificate installed stopped history)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who) -
      expect phaseLaw (completionValue setup runtime leaks bounds horizon scheduler parameter
        utility excludedPayoff (setup.intendedOpeningProfile (sequence n).strategy) rank fresh who
        (fun _ => excludedPayoff who))| ≤
      (2 * payoffBound * (1 - slotRetention (scale n))) * (2 * horizon + 1) +
      2 * payoffBound * expect phaseLaw
        (lateBadStop setup runtime leaks bounds horizon scheduler rank fresh event) := by
  apply local_completion_value_sub_le_of_boundary_values setup runtime leaks bounds horizon
    scheduler
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
