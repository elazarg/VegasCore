/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketInitializedLaw
import Vegas.Game.OnePacketCertificateDischarge

/-! # The common comparison strategy retains honest boundary continuations -/

noncomputable section

namespace Vegas.OnePacketComparison

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem apply_eq_one_of_subsingleton {α : Type} [Subsingleton α]
    (law : PMF α) (choice : α) : law choice = 1 := by
  rw [← law.tsum_coe, tsum_eq_single choice (fun other different =>
    (different (Subsingleton.elim other choice)).elim)]

/-- Counted native service makes every reached honest input nonlate and forced,
so the original common weights retain its honest choice at every future step. -/
theorem assembled_dominatesHonestFrom_boundary
    [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      positive
      le_one weights targetSequence) (n : ℕ)
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
    (certificate : (NP).WellFoundedHistories)
    (rank : Nat) (start : (NP).History) (anchor : (application setup runtime leaks).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup runtime leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    DominatesHonestFrom setup runtime leaks bounds (initialLaw setup) horizon scheduler
      (sequence n) (slotRetention (scale n))
      ((targetSequence n).strategy) start := by
  classical
  have sourceLaw := counted_honest_boundary_readout_law (runtime := runtime) opportunity inclusion
    timely
    completes wellFormed covers capacity
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
      change ((bounds.onePacketMenu runtime leaks).signals (initialLaw setup) horizon
        scheduler).infoOf who history.trace = none
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
      honest_reached_intended_of_readout_law bounds wellFormed (sequence n)
        certificate start
        point static intended (sourceLaw.trans sourceEq) fuel history reached control controlState
    have forced : Vegas.forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks)
        (initialLaw setup) horizon scheduler who ((N).infoOf who history.trace) := by
      apply forcedAgent_of_history (runtime := runtime) history
      rw [controlState]
      exact (forcedState_iff_decodedPoint (runtime := runtime) control).mpr
        ⟨decodedPoint, decodedEq, forcedPoint_of_intended who intendedPoint⟩
    have notLate := counted_honest_reached_not_late (runtime := runtime) opportunity timely
      inclusion completes
      wellFormed covers capacity
      (sequence n) certificate rank start anchor state boundary point decoded intended fuel
      history reached who
    change slotRetention (scale n) *
      ((honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler (sequence n)
        who
        ((N).infoOf who history.trace)) choice).toReal ≤
      (((targetSequence n).strategy who ((N).infoOf who history.trace)) choice).toReal
    rw [assembled n]
    exact onePacketMixture_ge_honest_of_not_late setup runtime leaks bounds horizon scheduler
      sequence scale positive le_one n
      (weights n)
      notLate ⟨history, rfl⟩ forced choice

theorem assembled_dominatesHonestFrom_initialized
    [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      positive
      le_one weights targetSequence) (n : ℕ)
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
    (certificate : (NP).WellFoundedHistories) :
    DominatesHonestFrom setup runtime leaks bounds (initialLaw setup) horizon scheduler
      (sequence n) (slotRetention (scale n))
      ((targetSequence n).strategy) (NP).initHistory := by
  classical
  let players := honestProfile setup runtime leaks bounds (initialLaw setup) horizon scheduler
    (sequence n)
  intro fuel history reached who choice
  by_cases empty : history.state = none
  · have observed : (N).infoOf who history.trace = none := by
      change ((bounds.onePacketMenu runtime leaks).signals (initialLaw setup) horizon
        scheduler).infoOf who history.trace = none
      rw [ReactiveApplication.ResponseMenu.info, empty]
      rfl
    revert choice
    rw [observed]
    intro choice
    have : Subsingleton ((N).Choice who none) :=
      InformationModel.subsingleton_choice_of_menu_subsingleton _ _ Set.subsingleton_singleton
    have unit (law : PMF ((N).Choice who none)) : law choice = 1 := by
      rw [← law.tsum_coe, tsum_eq_single choice (fun other different =>
        (different (Subsingleton.elim other choice)).elim)]
    rw [unit, unit, ENNReal.toReal_one, mul_one]
    exact slotRetention_le_one (positive n).le (le_one n)
  · obtain ⟨control, current⟩ := Option.ne_none_iff_exists'.mp empty
    obtain ⟨point, decoded, intended⟩ := counted_honest_initialized_intended (runtime := runtime)
      opportunity
      inclusion timely
      completes
      wellFormed covers capacity (sequence n) certificate fuel history reached control
        current
    have forced : Vegas.forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks)
        (initialLaw setup) horizon scheduler who ((N).infoOf who history.trace) := by
      apply forcedAgent_of_history (runtime := runtime) history
      rw [current]
      exact (forcedState_iff_decodedPoint (runtime := runtime) control).mpr
        ⟨point, decoded, forcedPoint_of_intended who intended⟩
    have notLate := counted_honest_initialized_not_late (runtime := runtime) opportunity inclusion
      timely
      completes wellFormed covers capacity
      (sequence n) certificate fuel history reached who
    change slotRetention (scale n) *
      ((honestChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler (sequence n)
        who
        ((N).infoOf who history.trace)) choice).toReal ≤
      (((targetSequence n).strategy who ((N).infoOf who history.trace)) choice).toReal
    rw [assembled n]
    exact onePacketMixture_ge_honest_of_not_late setup runtime leaks bounds horizon scheduler
      sequence scale positive le_one n
      (weights n)
      notLate ⟨history, rfl⟩ forced choice


end Vegas.OnePacketComparison
