/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalEmissionRecords
import Vegas.Game.PhaseProposalBindingFrontierReady
import Vegas.Pending.PhaseBindingMenuShape

/-! # Actual counted binding responses extend the same emitted assignments -/

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
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- A genuine nonsilent counted binding step adds exactly its original
prepared value to the same trace frontier. Every older signed packet keeps
its immutable meaning. The preparation can be unusable or wrongly typed. -/
theorem phaseProposalEmissionFrontier_binding_step
    (anchor : (app).Execution) (phase : RuntimePhase (graph)) (anchorLength : Nat)
    (initialFrontier : (graph).Config) (remaining : Nat) (who : Player)
    (execution : (app).Execution)
    (prior : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (joint : Player → Option (app).Action)
    (legal : ((menu).protocol initial horizon scheduler).Legal
      (some ⟨remaining, some who, execution⟩) joint)
    (response : (app).Action) (selected : joint who = some response)
    (realized : some ⟨remaining, none, execution.respond (app) who response⟩ ∈
      (((menu).protocol initial horizon scheduler).step
        (some ⟨remaining, some who, execution⟩) ⟨joint, legal⟩).support)
    (material : WitnessedSubmission (graph)) (transmitted : response.transmission = some material)
    (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (code : cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) =
      .bind who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (inside : event ∈ phase.events)
    (attempt : execution.application.attempt = anchor.application.attempt)
    (later : anchorLength ≤ prior.length) :
    let frontier := phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength
      initialFrontier initial horizon scheduler ((menu).toRawTrace initial horizon scheduler prior)
    PhaseProposalEmittedBindings runtime leaks execution phase frontier →
    frontier.cut.Ready event →
    PhaseProposalEmittedBindings runtime leaks (execution.respond (app) who response) phase
      (phaseProposalEmissionFrontier setup mode runtime leaks anchor phase anchorLength
        initialFrontier initial horizon scheduler
          ((menu).toRawTrace initial horizon scheduler (prior.extend joint legal realized))) ∧
      ∀ final : (graph).Config,
        PhaseProposalEmittedBindings runtime leaks (execution.respond (app) who response)
            phase final ↔
          PhaseProposalEmittedBindings runtime leaks execution phase final ∧
            (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding who payload)).get?
                final.store = some (((response.transmission.bind
                  PhaseProposal.bindingPreparation).bind (fun raw => raw.as? payload)).elim
                    PublicationResult.failure PublicationResult.success) := by
  intro frontier emissions ready
  let rawPrior := (menu).toRawTrace initial horizon scheduler prior
  let postTrace := prior.extend joint legal realized
  let after := execution.respond (app) who response
  let afterFrontier := phaseProposalEmissionFrontier setup mode runtime leaks anchor phase
    anchorLength initialFrontier initial horizon scheduler
      ((menu).toRawTrace initial horizon scheduler postTrace)
  have responseEq : response = ⟨some material⟩ := by
    cases response
    cases transmitted
    rfl
  have allowed : response ∈ PhaseCount.onePacketActions runtime leaks bounds who
      (execution.recall who) (execution.observe (app) who) := by
    have chosen := legal.2 who
    rw [selected] at chosen
    exact chosen.2
  have offered : (⟨some material⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds who (execution.recall who)
        (execution.observe (app) who) := responseEq ▸ allowed
  obtain ⟨serial, opening, evidence, materialEq, _bounded, fresh⟩ :=
    PhaseCount.onePacket_binding_shape runtime leaks bounds plan
      (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who
        execution prior event payload binding request material offered
  let message : Message Player (app).Payload :=
    ⟨(who, execution.network.nextSerial who), (app).packet
      ((app).submit execution.application who material) who (execution.network.known who) material⟩
  have inputWord : after.network.inputs = execution.network.inputs ++ [message] := by
    dsimp only [after]
    rw [responseEq]
    rfl
  have packet : message.payload.packet.call = .commitment event (who, .prepared serial) := by
    change ((execution.application.submit who material).emit who
      (execution.network.known who) material).packet.call = _
    rw [phase_emit_call, materialEq]
  have declaredPacket : material.call.packet = .commitment event (who, .prepared serial) := by
    rw [materialEq]
  have rawLater : anchorLength ≤ rawPrior.length := by
    rw [(menu).toRawTrace_length]
    exact later
  have kept : ∀ field value, frontier.store field = some value →
      afterFrontier.store field = some value := by
    intro field value stored
    exact phaseProposalEmissionFrontier_prefix_preserves setup mode runtime leaks anchor phase
      anchorLength initialFrontier initial horizon scheduler field value stored
        (.extend .refl joint ((menu).legal_raw initial horizon scheduler legal) realized)
  have written := phaseProposalEmissionFrontier_binding_recorded setup mode runtime leaks anchor
    phase anchorLength initialFrontier initial horizon scheduler remaining who execution rawPrior
      joint ((menu).legal_raw initial horizon scheduler legal) _ realized response selected material
        transmitted event (who, .prepared serial) declaredPacket payload binding code attempt inside
          rawLater ready _ TracePrefix.refl
  change (⟨.inr event, binding⟩ : FieldRef (graph).layout (.binding who payload)).get?
    afterFrontier.store = _ at written
  simp only [transmitted, Option.bind_some, materialEq, PhaseProposal.bindingPreparation,
    binding] at written
  let entry : (app).PlayerEntry := ⟨execution.observe (app) who, response, some message⟩
  have recorded : entry ∈ after.recall who := by
    simp [after, entry, responseEq, ReactiveApplication.Execution.respond, MessageNetwork.submit,
      message]
  have declared : entry.action =
      ⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, evidence⟩⟩ := by
    change response = _
    rw [responseEq, materialEq]
  have meaning := phase_recorded_material_binding_result runtime leaks (menu) initial horizon
    scheduler ⟨remaining, none, after⟩ postTrace who event payload serial opening evidence entry
      recorded declared fresh
  constructor
  · intro other member current query queryInside candidate named owner ty kind
    rw [inputWord] at member
    rcases List.mem_append.mp member with previous | newest
    · exact phaseProposalEmittedBinding_kept runtime leaks execution after phase frontier
        afterFrontier
        emissions other previous query queryInside candidate named current (by
          dsimp only [after]
          rw [responseEq]
          rfl)
          (phaseProposal_input_binding_fixed runtime leaks bounds plan inputs horizon scheduler
            ⟨remaining, some who, execution⟩ prior other previous query candidate named)
          ((phaseApplication_preservesFixedCandidates runtime leaks).respond execution who response)
          kept owner ty kind
    · cases List.mem_singleton.mp newest
      have coordinates := Payload.commitment.inj (packet.symm.trans named)
      rcases coordinates with ⟨rfl, rfl⟩
      have kinds := EventField.binding.inj (binding.symm.trans kind)
      rcases kinds with ⟨rfl, rfl⟩
      rw [meaning]
      cases decoded : opening.bind (fun raw => raw.as? payload) <;>
        simpa only [decoded, Option.map_none, Option.bind_none, Option.map_some, Option.bind_some,
          Raw.as?_mk] using written
  · intro final
    have sameAttempt : after.application.attempt = execution.application.attempt := by
      dsimp only [after]
      rw [responseEq]
      rfl
    have actualAttempt : message.payload.attempt = after.application.attempt := by
      dsimp only [message, after]
      rw [responseEq]
      rfl
    have actualResult : after.application.current.native.bindingResult
        (who, .prepared serial) payload =
        (((response.transmission.bind PhaseProposal.bindingPreparation).bind
          (fun raw => raw.as? payload)).elim PublicationResult.failure
            PublicationResult.success) := by
      rw [meaning]
      simp only [transmitted, Option.bind_some, materialEq, PhaseProposal.bindingPreparation,
        binding]
      cases opening.bind (fun raw => raw.as? payload) <;>
        simp only [Option.map_none, Option.bind_none, Option.map_some, Option.bind_some,
          Raw.as?_mk, Option.elim_none, Option.elim_some]
    have fixed := (phaseApplication_preservesFixedCandidates runtime leaks).respond
      execution who response
    constructor
    · intro emissions
      constructor
      · intro other member current query queryInside candidate named owner ty kind
        have newer : other ∈ after.network.inputs := by
          rw [inputWord]
          exact List.mem_append_left _ member
        have stored := emissions other newer (current.trans sameAttempt.symm) query queryInside
          candidate named owner ty kind
        have lookup := fixed candidate
          (phaseProposal_input_binding_fixed runtime leaks bounds plan inputs horizon scheduler
            ⟨remaining, some who, execution⟩ prior other member query candidate named)
        simpa only [State.bindingResult, lookup] using stored
      · have member : message ∈ after.network.inputs := by
          rw [inputWord]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        exact (emissions message member actualAttempt event inside (who, .prepared serial) packet
          who payload binding).trans (congrArg some actualResult)
    · rintro ⟨emissions, written⟩ other member current query queryInside candidate named
        owner ty kind
      change other ∈ after.network.inputs at member
      rw [inputWord] at member
      rcases List.mem_append.mp member with previous | newest
      · exact phaseProposalEmittedBinding_kept runtime leaks execution after phase final final
          emissions other previous query queryInside candidate named current sameAttempt.symm
          (phaseProposal_input_binding_fixed runtime leaks bounds plan inputs horizon scheduler
            ⟨remaining, some who, execution⟩ prior other previous query candidate named)
          fixed (fun _ _ stored => stored) owner ty kind
      · cases List.mem_singleton.mp newest
        have coordinates := Payload.commitment.inj (packet.symm.trans named)
        rcases coordinates with ⟨rfl, rfl⟩
        have kinds := EventField.binding.inj (binding.symm.trans kind)
        rcases kinds with ⟨rfl, rfl⟩
        exact written.trans (congrArg some actualResult.symm)

end Vegas
