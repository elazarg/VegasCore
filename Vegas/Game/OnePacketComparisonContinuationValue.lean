/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketComparisonRetention
import Vegas.Game.OnePacketStoppedContinuationValue

/-! # Source continuation values of the common recovery comparison profile -/

noncomputable section

namespace Vegas.OnePacketComparison

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk native ∅))

omit [Fintype Player] in
private theorem sourceContinuation_value_of_prefix
    (profile : BehavioralProfile setup.program)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player)
    {rank : Nat} {config : (graph setup).Config} {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank config = some point) :
    expect (sourceContinuation setup profile rank config)
      (fun readout => exclusionReadoutUtility setup parameter utility excludedPayoff readout who) =
      sourcePointValue setup parameter utility excludedPayoff profile who point := by
  have lawEq : sourceContinuation setup profile rank config =
      (setup.continuationLaw profile (some point)).map some :=
    congrArg (fun decoded => (setup.continuationLaw profile decoded).map some) decoded
  exact congrArg (fun law => expect law
    (fun readout => exclusionReadoutUtility setup parameter utility excludedPayoff readout who))
    lawEq

open Classical in
/-- The same common recovery weights approximate the source value at every
intended boundary, under counted native service and completion. -/
theorem assembled_stopped_boundary_value_sub_le
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale positive
      le_one weights targetSequence) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      OpportunityAt (runtime setup) leaks control.execution delay)
    (inclusion : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      ProtectedInclusionAt (runtime setup) leaks control.execution bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : ∀ control : (application setup leaks).Control,
      (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
      (application setup leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (certificate : (NP).WellFoundedHistories)
    (rank : Nat) (start : (NP).History) (anchor : (application setup leaks).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) {payoffBound : ℝ}
    (boundNonneg : 0 ≤ payoffBound)
    (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let stopped := fun history : (NP).History => ¬ Clear history.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) history.state
    |expect ((N).runBehavioralUntil certificate
        ((targetSequence n).strategy) stopped start)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup parameter utility excludedPayoff leaks final.state who) -
      sourcePointValue setup parameter utility excludedPayoff
        (setup.intendedOpeningProfile (sequence n).strategy) who point| ≤
      (2 * payoffBound * (Fintype.card Player * (1 - slotRetention (scale n)))) *
        (application setup leaks).rank horizon start.state := by
  intro stopped
  have retained := assembled_dominatesHonestFrom_boundary setup leaks bounds horizon
    scheduler
    wellFormed covers capacity sequence scale positive le_one weights targetSequence
      assembled n opportunity inclusion timely
    completes certificate rank start anchor state boundary point decoded intended
  have estimate := counted_stopped_boundary_value_sub_le opportunity inclusion timely
    completes wellFormed covers capacity
    (sequence n) certificate rank start anchor state boundary point decoded intended
    ((targetSequence n).strategy) (slotRetention_nonneg (positive n).le (le_one n))
    (slotRetention_le_one (positive n).le (le_one n)) retained parameter utility excludedPayoff who
    boundNonneg (fun history => by
      rw [exclusionBase_eq_readout]
      exact readoutBounded _) excludedBounded
  have sourceValue := sourceContinuation_value_of_prefix setup
    (setup.intendedOpeningProfile (sequence n).strategy) parameter utility excludedPayoff who
    decoded
  rw [sourceValue] at estimate
  exact estimate

end Vegas.OnePacketComparison
