module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketHonestStoppedDistribution
public import Vegas.Game.StoppedHonestComparison
public import Vegas.Game.SourceDebtObservation

@[expose] public section

/-! # Source values of stopped continuations under counted native service -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts setup.informationGraph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
  {bounds : MessageBounds setup.informationGraph}
  {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  {delay bound : setup.informationGraph.EventId → Nat}
  (opportunity : ∀ control : (application setup timeouts leaks).Control,
    ((bounds.onePacketMenu timeouts leaks).protocol (initialDistribution setup) horizon
      scheduler).Trace (some control) →
    control.execution.application.config.defaulted = ∅ →
    OpportunityAt timeouts leaks control.execution delay)
  (inclusion : ∀ control : (application setup timeouts leaks).Control,
    ((bounds.onePacketMenu timeouts leaks).protocol (initialDistribution setup) horizon
      scheduler).Trace (some control) →
    control.execution.application.config.defaulted = ∅ →
    ProtectedInclusionAt timeouts leaks control.execution bound)
  (timely : (AsyncTimely timeouts) delay bound)
  (completes : ∀ control : (application setup timeouts leaks).Control,
    ((bounds.onePacketMenu timeouts leaks).protocol (initialDistribution setup) horizon
      scheduler).Trace (some control) →
    control.execution.application.config.defaulted = ∅ →
    (application setup timeouts leaks).terminal (some control) →
    control.execution.application.config.cut.Terminal)

local notation "N" => onePacketModel setup timeouts leaks bounds (initialDistribution setup) horizon
  scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) (initialDistribution setup) horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup timeouts leaks)
    (fun native : EventGraphRuntime.State setup.informationGraph =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

include opportunity inclusion timely completes in
open Classical in
/-- Counted native service supplies the reference source value; choice retention
controls its approximation before public exclusion or latent own debt. -/
theorem counted_stopped_boundary_value_sub_le
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount setup.informationGraph player < bounds.candidateCount)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (rank : Nat) (start : (E).History) (execution : (application setup timeouts leaks).Execution)
    (state : start.state = some ⟨horizon - execution.environmentRecall.length, none, execution⟩)
    (boundary : ReachedBoundary setup timeouts leaks horizon scheduler rank execution)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    (profile : ∀ who, (N).BehavioralPolicy who)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (dominates : DominatesHonestFrom setup timeouts leaks bounds (initialDistribution setup) horizon
      scheduler
      assessment retention profile start)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) {payoffBound : ℝ}
    (boundNonneg : 0 ≤ payoffBound)
    (payoffBounded : ∀ history : (E).History,
      |exclusionBase setup timeouts parameter utility excludedPayoff leaks history.state who| ≤
        payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let stopped := fun history : (E).History => ¬ Clear history.state ∨
      DecodedState setup timeouts leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) history.state
    |expect ((N).runBehavioralUntil certificate profile stopped start)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state who) -
      expect (sourceContinuation setup (setup.intendedOpeningProfile assessment.strategy) rank
        execution.application.config)
        (fun readout =>
          exclusionReadoutUtility setup parameter utility excludedPayoff readout who)| ≤
      (2 * payoffBound * (1 - retention)) *
        (application setup timeouts leaks).rank horizon start.state := by
  classical
  intro stopped
  let honest := honestProfile setup timeouts leaks bounds (initialDistribution setup) horizon
    scheduler
    assessment
  let payoff := fun final : (E).History => if stopped final then excludedPayoff who else
    exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state who
  have bounded : ∀ final, |payoff final| ≤ payoffBound := by
    intro final
    dsimp only [payoff]
    split
    · exact excludedBounded
    · exact payoffBounded final
  have sourceDistribution := counted_honest_boundary_readout_distribution
    (timeouts := timeouts) opportunity inclusion
    timely completes covers capacity assessment certificate rank start execution state
      boundary point decoded intended
  have sourceEq : sourceContinuation setup (setup.intendedOpeningProfile assessment.strategy) rank
      execution.application.config =
        (setup.continuationDistribution (setup.intendedOpeningProfile assessment.strategy)
          (some point)).map some := by
    exact congrArg (fun decoded =>
      (setup.continuationDistribution (setup.intendedOpeningProfile assessment.strategy)
        decoded).map some)
      decoded
  have decodedPointEq := (decodedPoint_eq_of_isPrefix boundary.ordered).trans decoded
  obtain ⟨lawEq, noStop⟩ := honest_debt_stopped_terminal_distribution_of_readout_distribution
    (timeouts := timeouts)
    bounds wellFormed
    assessment certificate start point (decodedPoint_staticAt decodedPointEq) intended
    (sourceDistribution.trans sourceEq) who
  have reference : expect ((N).runBehavioralUntil certificate honest stopped start) payoff =
      expect (sourceContinuation setup (setup.intendedOpeningProfile assessment.strategy) rank
        execution.application.config)
        (fun readout =>
          exclusionReadoutUtility setup parameter utility excludedPayoff readout who) := by
    calc
      _ = expect ((N).runBehavioralUntil certificate honest stopped start)
          (fun final => exclusionBase setup timeouts parameter utility excludedPayoff leaks
            final.state who)
          := expect_congr_on_support fun final member => by
            exact ite_eq_right (noStop final member)
      _ = expect ((N).runBehavioralTerminalFrom certificate honest start)
          (fun final => exclusionBase setup timeouts parameter utility excludedPayoff leaks
            final.state who)
          := by rw [lawEq]
      _ = expect (((N).runBehavioralTerminalFrom certificate honest start).map
          (fun final => sourceReadout setup timeouts leaks final.state))
          (fun readout =>
            exclusionReadoutUtility setup parameter utility excludedPayoff readout who)
          := by
            rw [expect_map]
            apply expect_congr_on_support
            intro final member
            have projected : sourceReadout setup timeouts leaks final.state ∈
                (sourceContinuation setup (setup.intendedOpeningProfile assessment.strategy) rank
                  execution.application.config).support := by
              rw [← sourceDistribution]
              exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, member, rfl⟩
            change sourceReadout setup timeouts leaks final.state ∈
              ((setup.continuationDistribution (setup.intendedOpeningProfile assessment.strategy)
                (sourceServicePrefix? setup rank execution.application.config)).map some).support
              at projected
            obtain ⟨terminal, _, read⟩ := (PMF.mem_support_map_iff _ _ _).mp projected
            exact exclusionBase_eq_readout_of_readout setup timeouts parameter utility
              excludedPayoff leaks final.state terminal read.symm who
      _ = _ := by rw [sourceDistribution]
  change |expect _ payoff - _| ≤ _
  rw [← reference]
  have comparison := onePacket_stopped_expect_sub_le_remainingResponses setup timeouts leaks bounds
    (initialDistribution setup) horizon scheduler
    assessment certificate stopped profile start nonnegative le_one dominates payoff boundNonneg
      bounded
  exact comparison.trans (mul_le_mul_of_nonneg_left
    (by
      exact_mod_cast
        (application setup timeouts leaks).remainingResponses_le_rank horizon start.state)
    (by positivity))

end Vegas
