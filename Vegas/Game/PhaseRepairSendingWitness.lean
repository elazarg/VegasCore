/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingResponseWitness
import Vegas.Game.PhaseRepairOwnPlay

/-! # Actual raw binding repairs supply chronological sending witnesses -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds)
  initial horizon scheduler

/-- An actual legal source binding, including arbitrary preparation and
evidence, supplies the repaired callback's legal same-slot raw material.
Unsentness is derived from actual nonsilent menu membership on that callback.
No source-choice support, atom comparison or image-evidence legality is assumed. -/
theorem phase_binding_sending_pair
    (covered : bounds.CoversOutputValues) (who : Player) (remaining : Nat)
    (original repaired : (app).Execution)
    (memory : BindingMemory runtime (PhaseBindingRepair.nativeLeaks
      (graph := serviceGraph setup mode)))
    (frame : PhaseBindingRepair.Frame runtime leaks memory who original repaired)
    (left : (E).Trace (some ⟨remaining, some who, original⟩))
    (right : (E).Trace (some ⟨remaining, some who, repaired⟩))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Nat) (preparation : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup mode))
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .bind who payload)
    (node : nodeView (serviceGraph setup mode) event = .bind who payload outputEq codeEq)
    (request : original.application.SeedRequest who ⟨original.application.attempt, event⟩)
    (member : (⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds who
        (original.recall who) (original.observe app who)) :
    phaseBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler who
      (some (original.recall who, original.observe app who),
        ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩)
      (some (repaired.recall who, repaired.observe app who),
        PhaseBindingRepair.Frame.responseImage (runtime := runtime) (leaks := leaks) who who
          ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩) := by
  obtain ⟨value, responseEq⟩ := PhaseBindingRepair.Frame.responseImage_binding
    (runtime := runtime) (leaks := leaks) event payload outputEq codeEq node serial
      preparation evidence
  rw [responseEq]
  let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
  have leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some who, original⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact left
  have rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some who, repaired⟩) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact right
  have rawLeft := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ leftTrace
  have rawRight := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ rightTrace
  have fresh := PhaseCount.onePacket_binding_fresh runtime leaks bounds plan inputs horizon
    scheduler leftTrace who event serial preparation evidence member
  have canonical := frame.canonical_binding_member bounds
    (PhaseCount.countRecall_history runtime leaks rawLeft)
    (PhaseCount.countRecall_history runtime leaks rawRight) event serial preparation evidence
      fresh member
  have imageRequest := (frame.seedRequest_iff who
    ⟨original.application.attempt, event⟩).mp request
  have attemptEq : original.application.attempt = repaired.application.attempt := by
    simp only [PhaseRuntimeState.attempt, frame.phases, frame.generation]
  rw [attemptEq] at imageRequest
  have unsent := PhaseCount.unsent_of_nonsilent runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who repaired
      rightTrace ⟨repaired.application.attempt, event⟩ imageRequest
        ⟨⟨.commitment event (who, .prepared serial), preparation⟩, .none⟩ canonical
  have values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values := by
    have allValues := covered event
    rwa [outputEq] at allValues
  exact ⟨⟨remaining, some who, original⟩, ⟨remaining, some who, repaired⟩,
    left, right, event, payload, outputEq, serial, preparation, .none, .success value,
    ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩,
    rfl, rfl, imageRequest, unsent, values, frame.clearRepaired, member, canonical, rfl, rfl⟩

end Vegas
