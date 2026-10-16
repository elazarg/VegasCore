/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingOwnerWordChannel
import Vegas.Source.CommitPrefixFocalViewMarginal
import Interaction.ReactiveAnchoredStopped
import Interaction.ReactiveRecallReplay
import Vegas.Source.CommitPrefixProduct
import GameTheory.Math.Probability.ConditionalObservation

/-! # Accepted-view source references retain the same stopped physical marginal -/

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
/-- Conditioning the ORIGINAL source Config by its current focal view changes
no physical stopped-history probability when the focal policy is fixed. Every
foreign word and full owner plan remains in the same original execution law. -/
theorem phaseTimingOwnerWordProfile_focal_view_marginal
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix Δ P Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (sourceProfile : BehavioralProfile (earlier.prepend (later.prepend suffix)))
    (sourceEntry : SourceProgram.Config Player L Γ)
    (low generation : Nat) (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight)
    (slotBounded : slotWeight ≤ 1) (parts : Player → (p : Pool) → Parts p)
    (certificate : (E).WellFoundedHistories) (focal : Player)
    (intervention : (N).BehavioralPolicy focal) (stopped : (E).History → Prop)
    (entry : (E).History) (observed : DecisionView focal Δ)
    (present : observed ∈ ((earlier.prefixLaw (later.prepend suffix) sourceProfile sourceEntry).map
      (SourceProgram.Config.view focal)).support) :
    let current := earlier.tailProfile (later.prepend suffix) sourceProfile
    let complete := (earlier.prefixLaw (later.prepend suffix) sourceProfile sourceEntry).bind
      (later.prefixLaw suffix current)
    let reference := fiberPosterior complete
      (fun final => later.entryView focal (final.view focal)) observed
    let evaluate := fun final : SourceProgram.Config Player L Ξ =>
      (N).runBehavioralUntil certificate
        (GameTheory.Profile.update (sig := (N).behavioralSignature)
          (phaseTimingOwnerWordProfile setup mode runtime leaks bounds plan horizon scheduler bound
            fallback wellFormed source (earlier.append later) low generation slotWeight
              slotNonnegative slotBounded parts (fun who => final.view who)) focal intervention)
                stopped entry
    reference.bind evaluate = complete.bind evaluate := by
  intro current complete reference evaluate
  let foreign := fun final : SourceProgram.Config Player L Ξ =>
    fun other : {other : Player // other ≠ focal} => final.view other.val
  let focalWord := complete.support_nonempty.choose.view focal
  let join := (Equiv.piSplitAt focal (fun who => DecisionView who Ξ)).symm
  let kernel := fun words => (N).runBehavioralUntil certificate
    (GameTheory.Profile.update (sig := (N).behavioralSignature)
      (phaseTimingOwnerWordProfile setup mode runtime leaks bounds plan horizon scheduler bound
        fallback wellFormed source (earlier.append later) low generation slotWeight slotNonnegative
          slotBounded parts (join (focalWord, words))) focal intervention) stopped entry
  have erased (final : SourceProgram.Config Player L Ξ) :
      evaluate final = kernel (foreign final) := by
    apply congrArg (fun players => (N).runBehavioralUntil certificate players stopped entry)
    funext who info
    by_cases own : who = focal
    · subst who
      rw [GameTheory.Profile.update_same, GameTheory.Profile.update_same]
    · simp only [GameTheory.Profile.update, Function.update_of_ne own,
        phaseTimingOwnerWordProfile]
      have same : join (focalWord, foreign final) who = final.view who := by
        simp [join, foreign, Equiv.piSplitAt, own]
      rw [same]
  have marginal := earlier.prefixLaw_foreign_focal_view later suffix sourceProfile sourceEntry
    focal observed present
  change reference.map foreign = complete.map foreign at marginal
  calc
    reference.bind evaluate = (reference.map foreign).bind kernel := by
      rw [PMF.bind_map]
      apply bind_congr_on_support
      intro final _
      exact erased final
    _ = (complete.map foreign).bind kernel := congrArg (fun law => law.bind kernel) marginal
    _ = complete.bind evaluate := by
      rw [PMF.bind_map]
      apply bind_congr_on_support
      intro final _
      exact (erased final).symm

end Vegas
