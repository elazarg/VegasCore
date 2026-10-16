/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueMarkerSum
import Vegas.Game.PhaseOpponentRawBindingMass

/-! # The actual native binding marker sum over the fixed position range -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "original" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial runtimePlan (encodeInputs draw))
local notation "M" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) original horizon scheduler
local notation "P" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) original horizon scheduler

open Classical in
private theorem position_fin (noise : ℝ) (profile : ∀ who, (M).BehavioralPolicy who)
    (history : (P).History) (who : Player) (index : Fin ((M).ownPlay who history.trace).length) :
    (if phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon scheduler who
        (((M).ownPlay who history.trace).get index) then
      (M).ownPlayReachProbability (profile who) (((M).ownPlay who history.trace).take index.val) *
        phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler noise who
          (((M).ownPlay who history.trace).get index) *
        (M).ownPlayReachProbability (profile who)
          (((M).ownPlay who history.trace).drop index.val).tail *
        (M).counterfactualReachProbability profile who history.trace
    else 0) =
      phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon scheduler
        noise who profile history index.val := by
  have recorded : phaseOwnRecordAt setup mode runtime leaks bounds runtimePlan horizon scheduler
      who history index.val = ((M).ownPlay who history.trace).get index := by
    unfold phaseOwnRecordAt
    rw [List.drop_eq_getElem_cons index.isLt]
    rfl
  simp only [phaseRawBindingPositionWeight, recorded, phaseMarkedHistoryWeight,
    phaseRawMixtureOwnPlayWeight]

private theorem position_zero (noise : ℝ) (profile : ∀ who, (M).BehavioralPolicy who)
    (history : (P).History) (who : Player) (index : Nat)
    (outside : ((M).ownPlay who history.trace).length ≤ index) :
    phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon scheduler
      noise who profile history index = 0 := by
  classical
  have empty : ((M).ownPlay who history.trace).drop index = [] :=
    List.drop_eq_nil_iff.mpr outside
  have noBinding : ¬phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon
      scheduler who (phaseOwnRecordAt setup mode runtime leaks bounds runtimePlan horizon scheduler
        who history index) := by
    rw [phaseOwnRecordAt, empty, List.headD_nil]
    rintro ⟨event, serial, preparation, evidence, same⟩
    cases congrArg (fun action : (app).Action => action.transmission) same
  exact ite_eq_right noBinding

private theorem position_sum (noise : ℝ) (profile : ∀ who, (M).BehavioralPolicy who)
    (history : (P).History) (who : Player) :
    (∑ index : Fin ((M).ownPlay who history.trace).length,
      phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon scheduler
        noise who profile history index.val) =
      ∑ index ∈ Finset.range (2 * horizon + 1),
        phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon scheduler
          noise who profile history index := by
  rw [Fin.sum_univ_eq_sum_range]
  apply Finset.sum_subset
    (Finset.range_mono (phase_ownPlay_length_le setup mode runtime leaks bounds runtimePlan horizon
      scheduler who history))
  intro index _inside outside
  exact position_zero setup mode runtime leaks bounds runtimePlan horizon scheduler noise profile
    history who index (by simpa only [Finset.mem_range, not_lt] using outside)

open Classical in
/-- The actual universal path coefficient yields EXACTLY the existing native
foreign RAW binding-position sum. Opaque initial-law transport changes only
finite histories and policies, retaining all original private-memory carriers. -/
theorem phase_binding_marker_sum_eq_position
    (initial : PMF (PhaseRuntimeState (serviceGraph setup mode)))
    (initialLaw : initial = original)
    (noise : ℝ) (focal : Player) (final : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some final)) (chance : ℝ)
    (factor : ∀ profile : ∀ who,
      ((menu).information initial horizon scheduler).BehavioralPolicy who,
      (((menu).information initial horizon scheduler).historyReachWeight profile
        ⟨some final, trace⟩).toReal =
        chance * ∏ who, ((menu).information initial horizon scheduler).ownPlayReachProbability
          (profile who) (((menu).information initial horizon scheduler).ownPlay who trace))
    (profile : ∀ who, ((menu).information initial horizon scheduler).BehavioralPolicy who) :
    let nativeTrace : (P).Trace (some final) := initialLaw ▸ trace
    let nativeProfile : ∀ who, (M).BehavioralPolicy who := initialLaw ▸ profile
    chance * (∑ index : (Σ who,
        Fin (((menu).information initial horizon scheduler).ownPlay who trace).length),
      if index.1 ≠ focal ∧ phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon
          scheduler index.1
            ((((menu).information initial horizon scheduler).ownPlay index.1 trace).get index.2)
      then
        phaseRawMixtureAtom setup mode runtime leaks bounds runtimePlan horizon scheduler noise
          index.1
            ((((menu).information initial horizon scheduler).ownPlay index.1 trace).get index.2) *
          ∏ other ∈ Finset.univ.erase index,
            (((profile other.1
                ((((menu).information initial horizon scheduler).ownPlay other.1 trace).get
                  other.2).1).map Subtype.val)
              (some ((((menu).information initial horizon scheduler).ownPlay other.1 trace).get
                other.2).2)).toReal
      else 0) =
      ∑ who ∈ Finset.univ.erase focal, ∑ index ∈ Finset.range (2 * horizon + 1),
        phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon scheduler
          noise who nativeProfile ⟨some final, nativeTrace⟩ index := by
  subst initial
  intro nativeTrace nativeProfile
  have sum := phase_binding_marker_sum_counterfactual setup mode runtime leaks bounds runtimePlan
    original horizon scheduler noise focal final trace chance factor profile
  apply sum.trans
  apply Finset.sum_congr rfl
  intro who _member
  trans ∑ index : Fin ((M).ownPlay who trace).length,
    phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon scheduler
      noise who profile ⟨some final, trace⟩ index.val
  · exact Finset.sum_congr rfl fun index _ =>
      position_fin setup mode runtime leaks bounds runtimePlan horizon scheduler noise profile
        ⟨some final, trace⟩ who index
  · exact position_sum setup mode runtime leaks bounds runtimePlan horizon scheduler
      noise profile ⟨some final, trace⟩ who

end Vegas
