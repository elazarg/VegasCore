/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourcePhaseGame
import Vegas.Game.RevealService
import Vegas.Pending.PhaseCountMenu
import GameTheory.Protocol.SingleMover

/-! # The original setup draw couples source and raw phase initialization

Both actual evaluators use the same original input draw before any player
acts. The coupling retains the genuine extended histories, not just their
states, and holds for arbitrary source and raw native behavioral profiles.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun input =>
  PhaseRuntimeState.initial plan (encodeInputs input)
local notation "nativeProtocol" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.rawMenu runtime leaks bounds) initial horizon scheduler
local notation "nativeModel" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.rawMenu runtime leaks bounds) initial horizon scheduler

/-- Actual one-step initialization preserves the original common draw for all
policies, including arbitrary raw deviations. No source law is supplied. -/
theorem sourcePhase_initial_coupling
    (sourceProfile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (nativeProfile : ∀ who, (nativeModel).BehavioralPolicy who) :
    ∃ joint : PMF (setup.commitRecoveryProtocol.History × (nativeProtocol).History),
      joint.map Prod.fst = setup.commitRecoveryModel.runBehavioralFrom sourceProfile 1
        setup.commitRecoveryProtocol.initHistory ∧
      joint.map Prod.snd = (nativeModel).runBehavioralFrom nativeProfile 1
        (nativeProtocol).initHistory ∧
      ∀ pair ∈ joint.support, ∃ input ∈ setup.initialLaw.support,
        pair.1.state = some (CommitRecoveryState.atPoint
          (ProtocolState.entry setup.program (setup.initialConfig input)) ∅ 0) ∧
        pair.2.state = some (⟨horizon, none, .initial (app)
          (PhaseRuntimeState.initial plan (encodeInputs input))⟩ : (app).Control) := by
  let sourceStart := setup.commitRecoveryProtocol.initHistory
  let nativeStart := (nativeProtocol).initHistory
  let sourceState := fun input => some (CommitRecoveryState.atPoint
    (ProtocolState.entry setup.program (setup.initialConfig input)) ∅ 0)
  let nativeState := fun input => some (⟨horizon, none, .initial (app)
    (PhaseRuntimeState.initial plan (encodeInputs input))⟩ : (app).Control)
  have sourceRunning : ¬ setup.commitRecoveryProtocol.terminal sourceStart.state :=
    fun impossible => impossible
  have nativeRunning : ¬ (nativeProtocol).terminal nativeStart.state :=
    fun impossible => impossible
  have sourceInactive : ∀ who, ¬ setup.commitRecoveryProtocol.active sourceStart.state who :=
    fun _ impossible => impossible
  have nativeInactive : ∀ who, ¬ (nativeProtocol).active nativeStart.state who := by
    intro who
    change ¬ (none : Option Player) = some who
    simp
  let sourceLegal : setup.commitRecoveryProtocol.Legal sourceStart.state (fun _ => none) :=
    setup.commitRecoveryProtocol.legal_of_legalOption sourceRunning sourceInactive
  let nativeLegal : (nativeProtocol).Legal nativeStart.state (fun _ => none) :=
    (nativeProtocol).legal_of_legalOption nativeRunning nativeInactive
  have sourceStep : setup.commitRecoveryProtocol.step sourceStart.state
      ⟨fun _ => none, sourceLegal⟩ = setup.initialLaw.map sourceState := rfl
  have nativeStep : (nativeProtocol).step nativeStart.state
      ⟨fun _ => none, nativeLegal⟩ = setup.initialLaw.map nativeState := by
    change ((setup.initialLaw.map _).map _) = _
    rw [PMF.map_comp]
    rfl
  let sourceImage : ∀ input ∈ setup.initialLaw.support,
      setup.commitRecoveryProtocol.History := fun input supported =>
    sourceStart.extend sourceLegal (by
      rw [sourceStep]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨input, supported, rfl⟩)
  let nativeImage : ∀ input ∈ setup.initialLaw.support,
      (nativeProtocol).History := fun input supported =>
    nativeStart.extend nativeLegal (by
      rw [nativeStep]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨input, supported, rfl⟩)
  let joint := setup.initialLaw.bindOnSupport fun input supported =>
    PMF.pure (sourceImage input supported, nativeImage input supported)
  have sourceLaw : setup.commitRecoveryModel.runBehavioralFrom sourceProfile 1 sourceStart =
      setup.initialLaw.bindOnSupport
        (fun input supported => PMF.pure (sourceImage input supported)) := by
    rw [setup.commitRecoveryModel.runBehavioralFrom_succ_of_not_terminal sourceProfile 0
        sourceRunning,
      setup.commitRecoveryModel.behavioralJoint_eq_pure_of_no_active sourceProfile
        sourceStart.trace sourceRunning sourceInactive, PMF.pure_bind]
    change (setup.commitRecoveryProtocol.step sourceStart.state
      ⟨fun _ => none, sourceLegal⟩).bindOnSupport
        (fun target supported => PMF.pure (sourceStart.extend sourceLegal supported)) = _
    calc
      _ = (setup.initialLaw.map sourceState).bindOnSupport (fun target supported => PMF.pure
          (sourceStart.extend sourceLegal (by rw [sourceStep]; exact supported))) := by
        apply bindOnSupport_congr_measure sourceStep
        intro target first second
        rfl
      _ = _ := by rw [bindOnSupport_map]
  have nativeLaw : (nativeModel).runBehavioralFrom nativeProfile 1 nativeStart =
      setup.initialLaw.bindOnSupport
        (fun input supported => PMF.pure (nativeImage input supported)) := by
    rw [(nativeModel).runBehavioralFrom_succ_of_not_terminal nativeProfile 0 nativeRunning,
      (nativeModel).behavioralJoint_eq_pure_of_no_active nativeProfile nativeStart.trace
        nativeRunning nativeInactive, PMF.pure_bind]
    change ((nativeProtocol).step nativeStart.state
      ⟨fun _ => none, nativeLegal⟩).bindOnSupport
        (fun target supported => PMF.pure (nativeStart.extend nativeLegal supported)) = _
    calc
      _ = (setup.initialLaw.map nativeState).bindOnSupport (fun target supported => PMF.pure
          (nativeStart.extend nativeLegal (by rw [nativeStep]; exact supported))) := by
        apply bindOnSupport_congr_measure nativeStep
        intro target first second
        rfl
      _ = _ := by rw [bindOnSupport_map]
  refine ⟨joint, ?_, ?_, ?_⟩
  · change (setup.initialLaw.bindOnSupport _).map Prod.fst = _
    rw [map_bindOnSupport]
    simpa only [PMF.pure_map] using sourceLaw.symm
  · change (setup.initialLaw.bindOnSupport _).map Prod.snd = _
    rw [map_bindOnSupport]
    simpa only [PMF.pure_map] using nativeLaw.symm
  · intro pair supported
    obtain ⟨input, member, landed⟩ := (PMF.mem_support_bindOnSupport_iff _ _).mp supported
    cases (PMF.mem_support_pure_iff _ _).mp landed
    exact ⟨input, member, rfl, rfl⟩

end Vegas
