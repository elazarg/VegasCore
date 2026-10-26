/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketStoppedContinuationValue
import Vegas.Game.RecoveryCountedService
import Vegas.Game.StoppedHonestComparison

/-! # Source values of stopped continuations on the actual recovery service -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (recoveryApplication runtime leaks).Scheduler}
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : Recovery.Opportunity runtime leaks initial horizon recoveryScheduler delay)
  (inclusion : Recovery.ProtectedInclusion runtime leaks initial horizon recoveryScheduler
    bound)
  (timely : runtime.AsyncTimely delay bound)
  (completes : Recovery.CompletesPlay runtime leaks initial horizon recoveryScheduler)

local notation "scheduler" => RecoveryProjection.nativeScheduler runtime leaks
  recoveryScheduler
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))

include initialized nativeLaw opportunity inclusion timely completes in
open Classical in
/-- Actual recovery service supplies the reference source value; choice retention
controls its approximation before public exclusion or latent own debt. -/
theorem recovery_stopped_boundary_value_sub_le
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (rank : Nat) (start : (E).History) (execution : (application setup runtime leaks).Execution)
    (state : start.state = some ⟨horizon - execution.environmentRecall.length, none, execution⟩)
    (boundary : ReachedBoundary setup runtime leaks horizon scheduler rank execution)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    (profile : ∀ who, (N).BehavioralPolicy who)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (dominates : DominatesHonestFrom setup runtime leaks bounds (initialLaw setup) horizon scheduler
      assessment retention profile start)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) {payoffBound : ℝ}
    (boundNonneg : 0 ≤ payoffBound)
    (payoffBounded : ∀ history : (E).History,
      |exclusionBase setup runtime parameter utility excludedPayoff leaks history.state who| ≤
        payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let stopped := fun history : (E).History => ¬ Clear history.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) history.state
    |expect ((N).runBehavioralUntil certificate profile stopped start)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who) -
      expect (sourceContinuation setup (setup.intendedOpeningProfile assessment.strategy) rank
        execution.application.config)
        (fun readout =>
          exclusionReadoutUtility setup parameter utility excludedPayoff readout who)| ≤
      (2 * payoffBound * (1 - retention)) *
        (application setup runtime leaks).rank horizon start.state  := by
  exact counted_stopped_boundary_value_sub_le (runtime := runtime)
    (opportunity := Recovery.Opportunity.clear_counted_native (runtime := runtime) bounds
      initialized nativeLaw
      opportunity)
    (inclusion := Recovery.ProtectedInclusion.clear_counted_native (runtime := runtime) bounds
      initialized nativeLaw
      inclusion)
    (timely := timely)
    (completes := Recovery.CompletesPlay.clear_counted_native (runtime := runtime) bounds
      initialized nativeLaw
      completes)
    wellFormed covers capacity assessment certificate rank start execution state boundary point
    decoded intended profile nonnegative le_one dominates parameter utility excludedPayoff who
    boundNonneg payoffBounded excludedBounded

end Vegas
