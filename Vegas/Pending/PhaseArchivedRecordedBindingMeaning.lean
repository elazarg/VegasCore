/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseArchivedBindingInputOrigin
import Vegas.Pending.PhaseRecordedBindingMeaning
import Interaction.ReactiveRecordedResponse

/-! # Original typed declarations in completed archived attempts -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)

/-- A surviving owner's archived graph action is its original fresh typed
declaration in that exact attempt. Actual callback legality derives freshness;
archive provenance derives association and the immutable catalogue gives the
meaning, including accepted failure, without a clear endpoint or receipt. -/
theorem archived_recorded_binding_action
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (record : RetiredCommitAttempt graph) (retired : record ∈ control.execution.application.retired)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (lower : record.attempt.phase ≤ event.val)
    (completed : event ∈ record.state.config.cut.completed)
    (surviving : owner ∉ control.execution.application.current.excluded)
    (result : PublicationResult (L.Val payload)) (serial : Nat) (entry : (app).PlayerEntry)
    (recorded : entry ∈ control.execution.recall owner)
    (declared : entry.action = phaseBindingResponse runtime leaks owner event payload result serial)
    (sameAttempt : entry.beforeView.application.2.attempt = record.attempt) :
    ∃ original : graph.Action event, ⟨event, original⟩ ∈ record.state.config.history ∧
      cast (congrArg EventField.Action binding) original = result := by
  obtain ⟨before, prior, _prefix, _acting, viewed, offered, _recalled⟩ :=
    (menu).recorded_response_prefix initial horizon scheduler control trace owner entry recorded
  rw [declared] at offered
  have fresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh := by
    cases result with
    | failure =>
        exact viewed ▸ onePacket_binding_fresh runtime leaks bounds plan inputs horizon scheduler
          prior owner event serial none .none offered
    | success value =>
        exact viewed ▸ onePacket_binding_fresh runtime leaks bounds plan inputs horizon scheduler
          prior owner event serial (some ⟨payload, value⟩) .none offered
  obtain ⟨material, sent⟩ : ∃ material, entry.action.transmission = some material := by
    rw [declared]
    exact ⟨_, rfl⟩
  have exactMaterial : (phaseBindingResponse runtime leaks owner event payload result
      serial).transmission = some material := declared ▸ sent
  have named : material.call.packet = .commitment event (owner, .prepared serial) :=
    (congrArg (fun material : WitnessedSubmission graph => material.call.packet)
      (Option.some.inj exactMaterial)).symm
  have associated := archived_recorded_binding_accepted runtime leaks bounds plan inputs horizon
    scheduler trace record retired owner event payload binding lower completed surviving entry
      recorded material sent (owner, .prepared serial) named sameAttempt
  have raw := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨valid, ⟨draw, native⟩, refinement⟩ :=
    phaseRetiredBindings_history runtime leaks plan inputs horizon scheduler raw record retired
  have permanent := phase_recorded_binding_result runtime leaks initial horizon scheduler raw
    owner event payload result serial entry recorded declared fresh
  have sameMeaning := refinement (owner, .prepared serial)
    (valid.accepted_fixed (.inr event) (owner, .prepared serial) associated)
  have archivedMeaning : record.state.bindingResult (owner, .prepared serial) payload = result := by
    unfold State.bindingResult at permanent ⊢
    rwa [sameMeaning] at permanent
  obtain ⟨original, retained, meaning⟩ := valid.completed_binding_action native.reachable event
    owner payload binding completed
  rw [associated, Option.elim_some] at meaning
  exact ⟨original, retained, meaning.trans archivedMeaning⟩

end Vegas.EventGraphRuntime.PhaseCount
