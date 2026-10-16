/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingAnchoredSourceReference
import Vegas.Source.CommitPrefixFocalViewMarginal
import Interaction.ReactiveAnchoredStopped
import Interaction.ReactiveRecallReplay
import Vegas.Source.CommitPrefixProduct
import GameTheory.Math.Probability.ConditionalObservation

/-! # Accepted-view source references at authentic full anchored executions -/

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
/-- At the actual full anchor, replacing the original Config prior by its
current focal-view fiber preserves the entire stopped physical history law.
Old RAW aliases are replayed, the focal policy is fixed, and no old recall is
reset or required to have a source origin. -/
theorem phaseTimingOwnerWordProfile_memory_focal_view_marginal
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
    (anchor : (app).Control) (anchorTrace : (E).Trace (some anchor))
    (observed : DecisionView focal Δ)
    (present : observed ∈ ((earlier.prefixLaw (later.prepend suffix) sourceProfile sourceEntry).map
      (SourceProgram.Config.view focal)).support) :
    let current := earlier.tailProfile (later.prepend suffix) sourceProfile
    let complete := (earlier.prefixLaw (later.prepend suffix) sourceProfile sourceEntry).bind
      (later.prefixLaw suffix current)
    let reference := fiberPosterior complete
      (fun final => later.entryView focal (final.view focal)) observed
    let focalPolicy := (app).decodePolicy ((menu).embedPolicy initial horizon scheduler focal
      intervention)
    let members := fun final : SourceProgram.Config Player L Ξ => fun owner =>
      if owner = focal then focalPolicy else
        ReactiveApplication.anchoredPolicy anchor.execution (fun _ =>
          phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
            fallback wellFormed source (earlier.append later) low generation slotWeight
              slotNonnegative slotBounded (parts owner) owner (final.view owner)) owner
    let evaluate := fun final => (N).runBehavioralUntil certificate (fun who =>
      (menu).restrictPolicy initial horizon scheduler who (members final who)) stopped
        ⟨some anchor, anchorTrace⟩
    reference.bind evaluate = complete.bind evaluate := by
  intro current complete reference focalPolicy members evaluate
  have compared := phaseTimingOwnerWordProfile_anchored_focal_view_marginal setup mode runtime
    leaks bounds plan horizon scheduler bound fallback wellFormed source earlier later suffix
      sourceProfile sourceEntry low generation slotWeight slotNonnegative slotBounded parts
        certificate focal intervention stopped anchor anchorTrace observed present
  dsimp only at compared
  let rawPlayers := fun final : SourceProgram.Config Player L Ξ =>
    Function.update (ReactiveApplication.anchoredPolicy anchor.execution
      (Function.update (fun owner => phaseTimingWordPlanPolicy setup mode runtime leaks bounds
        initial horizon scheduler bound fallback wellFormed source (earlier.append later) low
          generation slotWeight slotNonnegative slotBounded (parts owner) owner (final.view owner))
            focal focalPolicy)) focal focalPolicy
  have policies (final : SourceProgram.Config Player L Ξ) : rawPlayers final = members final := by
    dsimp only [rawPlayers, members]
    funext owner past view
    by_cases own : owner = focal
    · subst owner
      simp only [Function.update_self, ite_true]
    · simp only [Function.update_of_ne own, ite_eq_right own]
      unfold ReactiveApplication.anchoredPolicy
      rw [Function.update_of_ne own]
  let original := fun final : SourceProgram.Config Player L Ξ =>
    (N).runBehavioralUntil certificate (fun who =>
      (menu).restrictPolicy initial horizon scheduler who (rawPlayers final who)) stopped
        ⟨some anchor, anchorTrace⟩
  change reference.bind original = complete.bind original at compared
  have originalEq (final : SourceProgram.Config Player L Ξ) : original final = evaluate final :=
    congrArg (fun players : Player → (app).Policy => (N).runBehavioralUntil certificate (fun who =>
      (menu).restrictPolicy initial horizon scheduler who (players who)) stopped
        ⟨some anchor, anchorTrace⟩) (policies final)
  calc
    _ = reference.bind original := bind_congr_on_support _
      (fun final _ => (originalEq final).symm)
    _ = complete.bind original := compared
    _ = _ := bind_congr_on_support _ (fun final _ => originalEq final)

end Vegas
