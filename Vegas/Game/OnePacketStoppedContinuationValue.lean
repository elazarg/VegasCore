/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketHonestStoppedLaw
import Vegas.Game.StoppedHonestComparison

/-! # Source values of stopped continuations under counted native service -/

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
  {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : ∀ control : (application setup runtime leaks).Control,
    (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    OpportunityAt runtime leaks control.execution delay)
  (inclusion : ∀ control : (application setup runtime leaks).Control,
    (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    ProtectedInclusionAt runtime leaks control.execution bound)
  (timely : runtime.AsyncTimely delay bound)
  (completes : ∀ control : (application setup runtime leaks).Control,
    (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
    ExclusionEvidence 0 ∅ (RecoveryState.mk control.execution.application ∅) →
    (application setup runtime leaks).terminal (some control) →
    control.execution.application.config.cut.Terminal)

local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks) (fun native => ExclusionEvidence 0 ∅ (RecoveryState.mk
    native ∅))

include opportunity inclusion timely completes in
open Classical in
/-- Actual recovery service supplies the reference source value; choice retention
controls its approximation before public exclusion or latent own debt. -/
theorem counted_stopped_boundary_value_sub_le
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
        (application setup runtime leaks).rank horizon start.state := by
  classical
  intro stopped
  let honest := honestProfile setup runtime leaks bounds (initialLaw setup) horizon scheduler
    assessment
  let payoff := fun final : (E).History => if stopped final then excludedPayoff who else
    exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
  have bounded : ∀ final, |payoff final| ≤ payoffBound := by
    intro final
    dsimp only [payoff]
    split
    · exact excludedBounded
    · exact payoffBounded final
  have sourceLaw := counted_honest_boundary_readout_law (runtime := runtime) opportunity inclusion
    timely completes wellFormed covers capacity assessment certificate rank start execution state
      boundary point decoded intended
  have sourceEq : sourceContinuation setup (setup.intendedOpeningProfile assessment.strategy) rank
      execution.application.config =
        (setup.continuationLaw (setup.intendedOpeningProfile assessment.strategy)
          (some point)).map some := by
    exact congrArg (fun decoded =>
      (setup.continuationLaw (setup.intendedOpeningProfile assessment.strategy) decoded).map some)
      decoded
  have decodedPointEq := (decodedPoint_eq_of_isPrefix boundary.ordered).trans decoded
  obtain ⟨lawEq, noStop⟩ := honest_debt_stopped_terminal_law_of_readout_law (runtime := runtime)
    bounds wellFormed
    assessment certificate start point (decodedPoint_staticAt decodedPointEq) intended
    (sourceLaw.trans sourceEq) who
  have reference : expect ((N).runBehavioralUntil certificate honest stopped start) payoff =
      expect (sourceContinuation setup (setup.intendedOpeningProfile assessment.strategy) rank
        execution.application.config)
        (fun readout =>
          exclusionReadoutUtility setup parameter utility excludedPayoff readout who) := by
    calc
      _ = expect ((N).runBehavioralUntil certificate honest stopped start)
          (fun final => exclusionBase setup runtime parameter utility excludedPayoff leaks
            final.state who)
          := expect_congr_on_support fun final member => by
            exact ite_eq_right (noStop final member)
      _ = expect ((N).runBehavioralTerminalFrom certificate honest start)
          (fun final => exclusionBase setup runtime parameter utility excludedPayoff leaks
            final.state who)
          := by rw [lawEq]
      _ = expect (((N).runBehavioralTerminalFrom certificate honest start).map
          (fun final => sourceReadout setup runtime leaks final.state))
          (fun readout =>
            exclusionReadoutUtility setup parameter utility excludedPayoff readout who)
          := by simp only [expect_map, Function.comp_def, exclusionBase_eq_readout]
      _ = _ := by rw [sourceLaw]
  change |expect _ payoff - _| ≤ _
  rw [← reference]
  have comparison := onePacket_stopped_expect_sub_le_remainingResponses setup runtime leaks bounds
    (initialLaw setup) horizon scheduler
    assessment certificate stopped profile start nonnegative le_one dominates payoff boundNonneg
      bounded
  exact comparison.trans (mul_le_mul_of_nonneg_left
    (by
      exact_mod_cast
        (application setup runtime leaks).remainingResponses_le_rank horizon start.state)
    (by positivity))

end Vegas
