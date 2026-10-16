/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMarkedReach
import Vegas.Game.PhaseOpponentRawBindingMass
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay

/-! # Foreign raw-send shares under literal focal recall replay -/

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
local notation "initial" => PMF.map
  (fun draw => PhaseRuntimeState.initial runtimePlan (encodeInputs draw)) setup.initialLaw
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

private theorem foreign_position_replay_factor
    (profile selected : ∀ who, (N).BehavioralPolicy who) (focal owner : Player)
    (foreign : owner ≠ focal)
    (off : ∀ other, other ≠ focal → profile other = selected other)
    (control : (app).Control) (trace : (E).Trace (some control))
    (ownFactor : ℝ) (originalOwn : (N).playerReachProbability profile focal trace = ownFactor)
    (replayedOwn : (N).playerReachProbability selected focal trace = 1)
    (noise : ℝ) (index : Nat) :
    phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon scheduler
        noise owner profile ⟨some control, trace⟩ index =
      ownFactor * phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon
        scheduler noise owner selected ⟨some control, trace⟩ index := by
  classical
  obtain ⟨records, recordEq, _provenance, chance, _nonnegative, _natureMass, factor⟩ :=
    (N).exists_continuation_ownPlay_factor (.start : (E).Trace (E).init) trace
      (TracePrefix.start trace)
  have recordsEq (who) : records who = (N).ownPlay who trace := by
    simpa only [InfoSignals.ownPlay, List.append_nil] using (recordEq who).symm
  have universal (players : ∀ who, (N).BehavioralPolicy who) :
      ((N).historyReachWeight players ⟨some control, trace⟩).toReal =
        chance * ∏ who, (N).ownPlayReachProbability (players who) ((N).ownPlay who trace) := by
    simpa only [historyReachWeight, runBehavioral, Trace.length, Nat.sub_zero, recordsEq,
      ExecutionProtocol.initHistory] using factor players
  have cf (players : ∀ who, (N).BehavioralPolicy who) :=
    (menu).counterfactual_of_history_factor initial horizon scheduler control trace chance
      universal players owner
  have focalPresent : focal ∈ Finset.univ.erase owner := by
    exact Finset.mem_erase.mpr ⟨Ne.symm foreign, Finset.mem_univ _⟩
  have common :
      (∏ other ∈ (Finset.univ.erase owner).erase focal,
        (N).ownPlayReachProbability (profile other) ((N).ownPlay other trace)) =
      ∏ other ∈ (Finset.univ.erase owner).erase focal,
        (N).ownPlayReachProbability (selected other) ((N).ownPlay other trace) := by
    apply Finset.prod_congr rfl
    intro other member
    rw [off other (Finset.mem_erase.mp member).1]
  have ownP : (N).ownPlayReachProbability (profile focal) ((N).ownPlay focal trace) = ownFactor :=
    ((N).playerReachProbability_eq_ownPlayReachProbability profile focal trace).symm.trans
      originalOwn
  have ownQ : (N).ownPlayReachProbability (selected focal) ((N).ownPlay focal trace) = 1 :=
    ((N).playerReachProbability_eq_ownPlayReachProbability selected focal trace).symm.trans
      replayedOwn
  have cfScale : (N).counterfactualReachProbability profile owner trace =
      ownFactor * (N).counterfactualReachProbability selected owner trace := by
    rw [cf profile, cf selected]
    rw [← Finset.mul_prod_erase (Finset.univ.erase owner)
      (fun other => (N).ownPlayReachProbability (profile other) ((N).ownPlay other trace))
        focalPresent,
      ← Finset.mul_prod_erase (Finset.univ.erase owner)
        (fun other => (N).ownPlayReachProbability (selected other) ((N).ownPlay other trace))
          focalPresent, ownP, ownQ, common]
    ring
  unfold phaseRawBindingPositionWeight
  split_ifs
  · dsimp only [phaseMarkedHistoryWeight]
    rw [off owner foreign, cfScale]
    ring
  · simp only [mul_zero]

variable [nature : (phaseApplication runtime leaks).FiniteNature
  (setup.initialLaw.map (fun draw => PhaseRuntimeState.initial runtimePlan (encodeInputs draw)))
    scheduler]

local instance phaseRawBindingReplayHistoryFinite : Finite (E).History :=
  @ReactiveApplication.ResponseMenu.finite_history Player inferInstance
    (phaseApplication runtime leaks)
    (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler inferInstance nature

local instance phaseRawBindingReplayFiberFintype (focal : Player)
    (site : (N).InformationSite focal) : Fintype ((N).InformationHistory focal site.1) :=
  Fintype.ofFinite _

open Classical in
/-- Literal focal recall replay preserves the normalized total of FOREIGN
RAW binding-send contributions on the SAME complete native information fiber.
The original own-reach factor cancels from numerator and denominator; no entry
prior, observed action or source explanation is replaced. -/
theorem phase_raw_binding_share_eq_recallReplay
    (profile : ∀ who, (N).BehavioralPolicy who) (focal : Player)
    (site : (N).InformationSite focal) (positive : 0 < (N).informationMass profile focal site)
    (reference : (N).InformationHistory focal site.1)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view)) (noise : ℝ) :
    let selected := Function.update profile focal
      ((menu).recallReplayPolicy initial horizon scheduler focal past (profile focal))
    phaseOpponentRawBindingShare setup mode runtime leaks bounds runtimePlan horizon scheduler
        noise focal profile site =
      phaseOpponentRawBindingShare setup mode runtime leaks bounds runtimePlan horizon scheduler
        noise focal selected site := by
  intro selected
  obtain ⟨_selectedPositive, _sameBelief, replayedOwn⟩ :=
    (menu).bayesBelief_eq_recallReplay initial horizon scheduler profile focal site positive
      reference past view observed
  obtain ⟨ownFactor, commonOwn⟩ :=
    (menu).commonPlayerReachAt initial horizon scheduler profile focal site
  have off (other) (different : other ≠ focal) : profile other = selected other :=
    (Function.update_of_ne different _ _).symm
  have weights (history : (N).InformationHistory focal site.1) :
      ((N).historyReachWeight profile history.1).toReal =
        ownFactor * ((N).historyReachWeight selected history.1).toReal := by
    rw [(N).historyReachProbability_eq_player_mul_counterfactual,
      (N).historyReachProbability_eq_player_mul_counterfactual,
      commonOwn history, replayedOwn history, one_mul,
      ← (N).counterfactualReachProbability_eq_of_eq_off off history.1.trace]
  have factorPositive : 0 < ownFactor := by
    obtain ⟨history, reached⟩ := (InformationModel.informationMass_pos_iff
      (N) profile focal site).mp positive
    have realReached := ENNReal.toReal_pos reached.ne' (PMF.apply_ne_top _ _)
    rw [(N).historyReachProbability_eq_player_mul_counterfactual, commonOwn history] at realReached
    exact pos_of_mul_pos_left realReached
      ((N).counterfactualReachProbability_nonneg profile focal history.1.trace)
  have marked (history : (N).InformationHistory focal site.1) (owner : Player)
      (foreign : owner ≠ focal) (index : Nat) :
      phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan horizon scheduler
          noise owner profile history.1 index =
        ownFactor * phaseRawBindingPositionWeight setup mode runtime leaks bounds runtimePlan
          horizon scheduler noise owner selected history.1 index := by
    rcases history with ⟨⟨state, trace⟩, seen⟩
    have acting := InformationSite.active (N) site ⟨⟨state, trace⟩, seen⟩
    cases state with
    | none =>
      change none = some focal at acting
      cases acting
    | some control =>
      exact foreign_position_replay_factor setup mode runtime leaks bounds runtimePlan horizon
        scheduler profile selected focal owner foreign off control trace ownFactor
          (commonOwn ⟨⟨some control, trace⟩, seen⟩)
          (replayedOwn ⟨⟨some control, trace⟩, seen⟩) noise index
  have realMass (players : ∀ who, (N).BehavioralPolicy who) :
      ((N).informationMass players focal site).toReal =
        ∑ history : (N).InformationHistory focal site.1,
          ((N).historyReachWeight players history.1).toReal := by
    unfold InformationModel.informationMass
    rw [tsum_fintype]
    exact ENNReal.toReal_sum (f := fun history : (N).InformationHistory focal site.1 =>
      (N).historyReachWeight players history.1) (fun _ _ => PMF.apply_ne_top _ _)
  have mass : ((N).informationMass profile focal site).toReal =
      ownFactor * ((N).informationMass selected focal site).toReal := by
    rw [realMass, realMass, Finset.mul_sum]
    exact Finset.sum_congr rfl fun history _ => weights history
  have markedMass : phaseOpponentRawBindingMass setup mode runtime leaks bounds runtimePlan
      horizon scheduler noise focal profile site =
      ownFactor * phaseOpponentRawBindingMass setup mode runtime leaks bounds runtimePlan
        horizon scheduler noise focal selected site := by
    unfold phaseOpponentRawBindingMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro owner ownerMember
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _inside
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun history _ =>
      marked history owner (Finset.mem_erase.mp ownerMember).1 index
  unfold phaseOpponentRawBindingShare
  rw [markedMass, mass]
  exact mul_div_mul_left _ _ factorPositive.ne'

end Vegas
