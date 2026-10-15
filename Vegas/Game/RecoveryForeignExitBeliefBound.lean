/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryForeignFailureBound
import GameTheory.Math.Probability.ExpectationComposition

/-! # Foreign exit bounds averaged over an actual history belief -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

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

/-- Averaging the actual stopped common comparison over a belief charges only
its irregular-history mass plus square plus scale times the protocol depth.
The focal continuation policy is arbitrary. -/
theorem nativeComparison_foreign_exit_mass_le_irregular_add_depth [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    (focal : Player) (focalPolicy : (N).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (certificate :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).WellFoundedHistories)
    (extraStop : (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History → Prop)
    (belief : PMF (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History)
    (clearOwnTurn : ∀ history ∈ belief.support,
      ∃ (control : (application setup leaks).Control) (current : (graph setup).EventId),
        history.state = some control ∧
        control.execution.application.publicView.ownTurn? focal = some current ∧
        PublicExclusionRecord (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup))) :
    ((belief.bind (fun history => (N).runBehavioralUntil certificate
      (Function.update (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale
        positive le_one weights n) focal focalPolicy)
      (fun history => ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
        (fun native => PublicExclusionRecord (⟨native, ∅⟩ : RecoveryState (graph setup)))
          history.state ∨
        DecodedState setup leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
      history)).toOuterMeasure
      {final | ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
        (fun native => PublicExclusionRecord (⟨native, ∅⟩ : RecoveryState (graph setup)))
          final.state ∧
        focal ∉ nativeFailureOwners (runtime setup) leaks final.state}).toReal ≤
      (belief.toOuterMeasure {history | ¬ RegularTrace setup leaks bounds horizon (NativeScheduler)
        (sequence n) focal history.trace}).toReal +
        ((scale n) ^ 2 + scale n) * (2 * horizon + 1) := by
  classical
  let profile := Function.update (nativeComparisonStrategy setup leaks bounds horizon scheduler
    sequence scale positive le_one weights n) focal focalPolicy
  let stopped := fun history :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History =>
    ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
      (fun native => PublicExclusionRecord (⟨native, ∅⟩ : RecoveryState (graph setup)))
        history.state ∨
      DecodedState setup leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history
  let kernel := fun history => (N).runBehavioralUntil certificate profile stopped history
  let exits := {final :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History |
    ¬ ReactiveApplication.stateInvariant (app := application setup leaks)
      (fun native => PublicExclusionRecord (⟨native, ∅⟩ : RecoveryState (graph setup)))
        final.state ∧
      focal ∉ nativeFailureOwners (runtime setup) leaks final.state}
  let irregular := {history :
      (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History |
    ¬ RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) focal history.trace}
  let payoff := fun history => @ite ℝ (history ∈ exits) (Classical.propDecidable _) 1 0
  let badPayoff := fun history => @ite ℝ (history ∈ irregular) (Classical.propDecidable _) 1 0
  let cost := ((scale n) ^ 2 + scale n) * (2 * horizon + 1)
  let future := fun history => expect (kernel history) payoff
  have payoffBounded : ∀ history, |payoff history| ≤ 1 := by
    intro history
    dsimp only [payoff]
    split <;> norm_num
  have badBounded : ∀ history, |badPayoff history| ≤ 1 := by
    intro history
    dsimp only [badPayoff]
    split <;> norm_num
  have futureBounded : ∀ history, |future history| ≤ 1 :=
    fun _ => expect_abs_le_of_bounded (by norm_num) payoffBounded
  have costNonnegative : 0 ≤ cost :=
    mul_nonneg (add_nonneg (sq_nonneg _) (positive n).le) (by positivity)
  have pointwise : ∀ history ∈ belief.support, future history ≤ badPayoff history + cost := by
    intro history member
    by_cases regular : RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n)
        focal history.trace
    · obtain ⟨control, current, state, turn, clear⟩ := clearOwnTurn history member
      have notBad : history ∉ irregular := fun failed => failed regular
      have row : future history ≤ cost := by
        rcases history with ⟨stateBefore, trace⟩
        change stateBefore = some control at state
        subst stateBefore
        have depth := (application setup leaks).trace_bound (initialLaw setup) horizon
          (NativeScheduler) ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace
            (initialLaw setup) horizon (NativeScheduler) trace)
        have rankBound : (application setup leaks).rank horizon (some control) ≤
            2 * horizon + 1 := by omega
        have rankReal : ((application setup leaks).rank horizon (some control) : ℝ) ≤
            2 * horizon + 1 := by exact_mod_cast rankBound
        calc
          future ⟨some control, trace⟩ =
              ((kernel ⟨some control, trace⟩).toOuterMeasure exits).toReal :=
            expect_indicator (kernel ⟨some control, trace⟩) exits
          _ ≤ ((scale n) ^ 2 + scale n) *
              (application setup leaks).rank horizon (some control) :=
            nativeComparison_foreign_exit_mass_le_rank setup leaks bounds horizon scheduler
              wellFormed covers capacity sequence scale positive le_one weights n focal focalPolicy
              opportunity inclusion timely certificate extraStop control trace current turn clear
              regular
          _ ≤ cost := mul_le_mul_of_nonneg_left rankReal
            (add_nonneg (sq_nonneg _) (positive n).le)
      simpa only [badPayoff, notBad, ↓reduceIte, zero_add] using row
    · have bad : history ∈ irregular := regular
      have upper : future history ≤ 1 + cost :=
        (le_abs_self _).trans ((futureBounded history).trans (le_add_of_nonneg_right
          costNonnegative))
      simpa only [badPayoff, bad, ↓reduceIte] using upper
  have badIntegrable := payoffIntegrable_of_bounded belief badPayoff badBounded
  have constantIntegrable := payoffIntegrable_constant belief cost
  have averaged := expect_mono pointwise (payoffIntegrable_of_bounded belief future futureBounded)
    (payoffIntegrable_add badIntegrable constantIntegrable)
  calc
    _ = expect (belief.bind kernel) payoff := (expect_indicator (belief.bind kernel) exits).symm
    _ = expect belief future := expect_bind_tower_bounded belief kernel payoff payoffBounded
    _ ≤ expect belief (fun history => badPayoff history + cost) := averaged
    _ = expect belief badPayoff + cost :=
      (expect_add badIntegrable constantIntegrable).trans
        (congrArg (fun value => expect belief badPayoff + value) (expect_constant belief cost))
    _ = _ := congrArg (fun value => value + cost) (expect_indicator belief irregular)

end Vegas.RecoveryOnePacket
