/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryHonestRecall
import Vegas.Game.RecoveryNativeComparison

/-! # The common comparison strategy retains honest boundary continuations -/

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
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon (NativeScheduler)

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem apply_eq_one_of_subsingleton {α : Type} [Subsingleton α]
    (law : PMF α) (choice : α) : law choice = 1 := by
  rw [← law.tsum_coe, tsum_eq_single choice (fun other different =>
    (different (Subsingleton.elim other choice)).elim)]

/-- Actual recovery service makes every reached honest input nonlate and forced,
so the original common weights retain its honest choice at every future step. -/
theorem nativeComparison_dominatesHonestFrom_boundary [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p)) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (completes : Recovery.CompletesPlay (runtime setup) leaks Initial horizon scheduler)
    (certificate : (NP).WellFoundedHistories)
    (rank : Nat) (start : (NP).History) (anchor : (application setup leaks).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup leaks horizon (NativeScheduler) rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    DominatesHonestFrom setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
      (sequence n) (slotRetention (scale n))
      (nativeComparisonStrategy setup leaks bounds horizon scheduler sequence scale positive le_one
        weights n) start := by
  classical
  have sourceLaw := recovery_honest_boundary_readout_law (initialLaw_initialized setup)
    (initialLaw_native setup) opportunity inclusion timely completes wellFormed covers capacity
    (sequence n) certificate rank start anchor state boundary point decoded intended
  have sourceEq : sourceContinuation setup (setup.intendedOpeningProfile (sequence n).strategy) rank
      anchor.application.config =
        (setup.continuationLaw (setup.intendedOpeningProfile (sequence n).strategy)
          (some point)).map some :=
    congrArg (fun decoded =>
      (setup.continuationLaw (setup.intendedOpeningProfile (sequence n).strategy) decoded).map some)
      decoded
  have static := decodedPoint_staticAt
    ((decodedPoint_eq_of_isPrefix boundary.ordered).trans decoded)
  intro fuel history reached who choice
  by_cases current : history.state = none
  · have observed : (N).infoOf who history.trace = none := by
      change ((bounds.onePacketMenu (runtime setup) leaks).signals (initialLaw setup) horizon
        (NativeScheduler)).infoOf who history.trace = none
      rw [ReactiveApplication.ResponseMenu.info, current]
      rfl
    revert choice
    rw [observed]
    intro choice
    have : Subsingleton ((N).Choice who none) :=
      InformationModel.subsingleton_choice_of_menu_subsingleton _ _ Set.subsingleton_singleton
    rw [apply_eq_one_of_subsingleton _ choice, apply_eq_one_of_subsingleton _ choice,
      ENNReal.toReal_one, mul_one]
    exact slotRetention_le_one (positive n).le (le_one n)
  · obtain ⟨control, controlState⟩ := Option.ne_none_iff_exists'.mp current
    obtain ⟨decodedPoint, decodedEq, intendedPoint⟩ :=
      honest_reached_intended_of_readout_law bounds wellFormed (sequence n) certificate start
        point static intended (sourceLaw.trans sourceEq) fuel history reached control controlState
    have forced : Vegas.forcedAgent (bounds.onePacketMenu (runtime setup) leaks)
        (initialLaw setup) horizon (NativeScheduler) who ((N).infoOf who history.trace) := by
      apply forcedAgent_of_history history
      rw [controlState]
      exact (forcedState_iff_decodedPoint control).mpr
        ⟨decodedPoint, decodedEq, forcedPoint_of_intended who intendedPoint⟩
    have notLate := recovery_honest_reached_not_late (initialLaw_initialized setup)
      (initialLaw_native setup) opportunity timely inclusion completes wellFormed covers capacity
      (sequence n) certificate rank start anchor state boundary point decoded intended fuel
      history reached who
    exact onePacketMixture_ge_honest_of_not_late setup leaks bounds horizon (NativeScheduler)
      sequence scale positive le_one n
      (nativeComparisonWeights setup leaks bounds horizon scheduler (weights n))
      notLate ⟨history, rfl⟩ forced choice

end Vegas.RecoveryOnePacket
