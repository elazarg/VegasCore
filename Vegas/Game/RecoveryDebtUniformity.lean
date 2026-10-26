/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryOnePacketComponents
import Vegas.Game.RecoveryIndifference
import Vegas.Game.OnePacketProjectedDecision

/-! # Own source debt is uniform over actual recovery information

The native projected view determines source debt. Actual recovery source
provenance supplies a decoder at every initialized history, including histories
after automatic service. An existential owing witness therefore determines
source debt throughout its complete information fiber.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "N" => model setup runtime leaks bounds Initial horizon scheduler
local notation "menu" => Recovery.onePacketMenu runtime leaks bounds
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler

/-- A decoded point of an actual recovery history supplies the corresponding
persistent source property for every source behavioral profile. -/
theorem decodedState_of_nativeDecodedState (profile : BehavioralProfile setup.program)
    {property : ProtocolState setup.program → Prop} (history : (E).History)
    {point : ProtocolState setup.program}
    (decoded : nativeDecodedState setup runtime leaks
      (RecoveryProjection.protocolState runtime leaks history.state) = some point)
    (holds : property point) :
    RecoveryDecodedState (runtime := runtime) (leaks := leaks) profile property history.state := by
  cases current : history.state with
  | none => rw [current] at decoded; cases decoded
  | some control =>
      have trace := current ▸ (menu).toRawTrace Initial horizon scheduler history.trace
      have source := recoveryFailureRecord_history (runtime := runtime) profile leaks horizon
        scheduler control trace
      rw [current] at decoded
      change decodedPoint setup control.execution.application.native.config = some point at decoded
      exact RecoveryDecoded.of_decodedPoint source.source decoded holds

/-- Every initialized actual recovery history has a decoded source point. -/
theorem nativeDecodedState_isSome (history : (E).History)
    {control : (recoveryApplication runtime leaks).Control}
    (current : history.state = some control) :
    ∃ point, nativeDecodedState setup runtime leaks
      (RecoveryProjection.protocolState runtime leaks history.state) = some point := by
  have trace := current ▸ (menu).toRawTrace Initial horizon scheduler history.trace
  have source := recoveryFailureRecord_history (runtime := runtime) (failureProfile setup.program)
    leaks horizon
    scheduler control trace
  obtain ⟨rank, ⟨residual⟩, _⟩ := source.source
  rw [current]
  exact ⟨_, decodedPoint_eq residual⟩

private theorem control_of_infoOf {who : Player}
    {past : List (recoveryApplication runtime leaks).PlayerEntry}
    {view : (recoveryApplication runtime leaks).PlayerView}
    (history : (N).InformationHistory who (some (past, view))) :
    ∃ control : (recoveryApplication runtime leaks).Control,
      history.1.state = some control ∧
        control.execution.observe (recoveryApplication runtime leaks) who = view := by
  have observed := ((menu).info Initial horizon scheduler who history.1.trace).symm.trans history.2
  cases current : history.1.state with
  | none => rw [current] at observed; cases observed
  | some control =>
      rw [current] at observed
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        exact ⟨control, rfl, (Prod.mk.inj (Option.some.inj observed)).2⟩
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        cases observed

/-- Two histories of the same recovery decision input agree on own source debt.
The projected-view theorem applies to their actual native executions directly. -/
theorem owesFailure_iff_of_infoOf {who : Player}
    {past : List (recoveryApplication runtime leaks).PlayerEntry}
    {view : (recoveryApplication runtime leaks).PlayerView}
    (first second : (N).InformationHistory who (some (past, view)))
    {firstPoint secondPoint : ProtocolState setup.program}
    (firstDecoded : nativeDecodedState setup runtime leaks
      (RecoveryProjection.protocolState runtime leaks first.1.state) = some firstPoint)
    (secondDecoded : nativeDecodedState setup runtime leaks
      (RecoveryProjection.protocolState runtime leaks second.1.state) = some secondPoint) :
    ProtocolState.OwesFailure who setup.program firstPoint ↔
      ProtocolState.OwesFailure who setup.program secondPoint := by
  obtain ⟨firstControl, firstState, firstView⟩ := control_of_infoOf setup runtime leaks bounds
    horizon
    scheduler first
  obtain ⟨secondControl, secondState, secondView⟩ := control_of_infoOf setup runtime leaks bounds
    horizon
    scheduler second
  rw [firstState] at firstDecoded
  rw [secondState] at secondDecoded
  refine Vegas.owesFailure_iff_of_projectView_eq (runtime := runtime)
    (first := RecoveryProjection.execution runtime leaks firstControl.execution)
    (second := RecoveryProjection.execution runtime leaks secondControl.execution)
    (firstPast := past.map (RecoveryProjection.playerEntry runtime leaks))
    (secondPast := past.map (RecoveryProjection.playerEntry runtime leaks)) who
    firstDecoded secondDecoded ?_
  simp only [RecoveryProjection.observe, firstView, secondView]

/-- One own-debt witness fixes the decoded source debt at every history of the
actual recovery decision input, for every source behavioral profile. -/
theorem decodedState_owesFailure_of_infoOf (profile : BehavioralProfile setup.program)
    {who : Player} {past : List (recoveryApplication runtime leaks).PlayerEntry}
    {view : (recoveryApplication runtime leaks).PlayerView}
    (owing : (N).InformationHistory who (some (past, view)))
    {point : ProtocolState setup.program}
    (decoded : nativeDecodedState setup runtime leaks
      (RecoveryProjection.protocolState runtime leaks owing.1.state) = some point)
    (owes : ProtocolState.OwesFailure who setup.program point)
    (history : (N).InformationHistory who (some (past, view))) :
    RecoveryDecodedState (runtime := runtime) (leaks := leaks) profile (ProtocolState.OwesFailure
      who setup.program)
      history.1.state := by
  obtain ⟨control, current, _view⟩ := control_of_infoOf setup runtime leaks bounds horizon
    scheduler history
  obtain ⟨other, otherDecoded⟩ := nativeDecodedState_isSome setup runtime leaks bounds horizon
    scheduler
    history.1 current
  exact decodedState_of_nativeDecodedState setup runtime leaks bounds horizon scheduler profile
    history.1
    otherDecoded ((owesFailure_iff_of_infoOf setup runtime leaks bounds horizon scheduler owing
      history
      decoded otherDecoded).mp owes)

/-- An owing agent owes throughout its complete actual recovery information
fiber. Public exclusion is not required: latent own binding debt is included. -/
theorem owingAgent_allHistories [recoveryHistoryFintype : Fintype (E).History]
    [recoveryInfoDecidable : ∀ who,
      DecidableEq ((model setup runtime leaks bounds Initial horizon scheduler).InfoState who)]
    (profile : BehavioralProfile setup.program) {who : Player}
    (site : (N).InformationSite who)
    (owing : OwingAgent setup runtime leaks bounds Initial horizon scheduler ((N).agentAt site))
    (history : (N).InformationHistory who site.1) :
    RecoveryDecodedState (runtime := runtime) (leaks := leaks) profile (ProtocolState.OwesFailure
      who setup.program)
      history.1.state := by
  obtain ⟨first, point, decoded, owes⟩ := owing
  let rawSite := (menu).rawSite Initial horizon scheduler who site
  obtain ⟨_witness, _running, response, permitted⟩ := rawSite.2
  have someInfo : site.1.isSome = true := by
    change (some response).isSome = site.1.isSome at permitted
    exact permitted.symm
  obtain ⟨data, input⟩ := Option.isSome_iff_exists.mp someInfo
  exact decodedState_owesFailure_of_infoOf setup runtime leaks bounds horizon scheduler profile
    ⟨first.1, first.2.trans input⟩ decoded owes ⟨history.1, history.2.trans input⟩

end Vegas.RecoveryOnePacket
