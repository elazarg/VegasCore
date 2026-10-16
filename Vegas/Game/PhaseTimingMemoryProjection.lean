/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingAnchoredSourceReference
import Interaction.ReactiveAnchoredOwner
import Vegas.Source.CommitPrefixFocalViewMarginal
import Interaction.ReactiveAnchoredStopped
import Interaction.ReactiveRecallReplay
import Vegas.Source.CommitPrefixProduct
import GameTheory.Math.Probability.ConditionalObservation

/-! # Physical projection of anchored immutable word members -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
      scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
        scheduler).InfoState who)]

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler

local notation "Pool" => FreeKeyedPool
  (fun agent : (N).InformationAgent (N).playedInformation =>
    PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent)))
  (fun agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
  (fun agent => phaseTimingKey runtime leaks (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

open Classical in
/-- Foreign anchor replay can be erased from the same stopped physical word-member
law while the focal finite intervention remains literal. -/
theorem phaseTimingOwnerWordProfile_memory_projection
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    {Γ Ξ : SourceCtx Player L} {O Q : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Ξ Q) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : Player → (p : Pool) → Parts p) (words : (owner : Player) → DecisionView owner Ξ)
    (certificate : (E).WellFoundedHistories) (focal : Player)
    (intervention : (N).BehavioralPolicy focal) (stopped : (E).History → Prop)
    (anchor : (app).Control) (start : (E).History) (starts : start.state = some anchor) :
    let focalPolicy := (app).decodePolicy ((menu).embedPolicy initial horizon scheduler focal
      intervention)
    let players := fun owner => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed source block low generation slotWeight
        slotNonnegative slotBounded (parts owner) owner (words owner)
    let members := fun owner => if owner = focal then focalPolicy else
      ReactiveApplication.anchoredPolicy anchor.execution (fun _ => players owner) owner
    (N).runBehavioralUntil certificate (fun who =>
      (menu).restrictPolicy initial horizon scheduler who (members who)) stopped
        start =
    (N).runBehavioralUntil certificate
      (GameTheory.Profile.update (sig := (N).behavioralSignature)
        (phaseTimingOwnerWordProfile setup mode runtime leaks bounds plan horizon scheduler bound
          fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded
            parts words) focal intervention) stopped start := by
  rcases start with ⟨state, anchorTrace⟩
  dsimp only at starts
  subst state
  intro focalPolicy players members
  let raw := Function.update players focal focalPolicy
  have anchored := (menu).runUntil_foreign_anchored initial horizon scheduler certificate raw focal
    anchor anchorTrace stopped
  have rawFocal : raw focal = focalPolicy := Function.update_self ..
  rw [rawFocal] at anchored
  have familyEq : Function.update (ReactiveApplication.anchoredPolicy anchor.execution raw)
      focal focalPolicy = members := by
    funext owner
    by_cases own : owner = focal
    · subst owner
      simp only [Function.update_self, members, ite_true]
    · simp only [Function.update_of_ne own, members, ite_eq_right own]
      apply ReactiveApplication.anchoredPolicy_owner_congr
      exact Function.update_of_ne own ..
  rw [familyEq] at anchored
  have policies : (fun who => (menu).restrictPolicy initial horizon scheduler who (raw who)) =
      GameTheory.Profile.update (sig := (N).behavioralSignature)
        (phaseTimingOwnerWordProfile setup mode runtime leaks bounds plan horizon scheduler bound
          fallback wellFormed source block low generation slotWeight slotNonnegative slotBounded
            parts words) focal intervention := by
    funext who info
    by_cases own : who = focal
    · subst who
      simp only [raw, Function.update_self, GameTheory.Profile.update_same]
      exact congrFun ((menu).restrict_decode_embedPolicy initial horizon scheduler focal
        intervention) info
    · simp only [raw, Function.update_of_ne own, GameTheory.Profile.update,
        phaseTimingOwnerWordProfile, players]
  rw [policies] at anchored
  exact anchored

end Vegas
