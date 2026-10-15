/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAsyncTimeliness
import Vegas.Pending.PhaseNativeResponse
import Vegas.Pending.PhaseBindingFreshness
import Vegas.Pending.PhaseBindingInvariant

/-! # Actual phased binding responses satisfy native protected-call conformance -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "R" => serviceRuntime setup mode deadline
local notation "P" => phaseApplication R leaks
local notation "N" => serviceApplication setup mode deadline
  (PhaseNativeProjection.nativeLeaks leaks plan)

/-- A permitted actual binding response yields its original emitted native
record and an acceptable fresh-call certificate. Freshness is global across
all retired attempts and is derived from the actual counted menu. The timing
premise is the protected window supplied by owner opportunity and timeliness. -/
theorem phaseBindingResponse_native_freshCall
    (bounds : MessageBounds (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (P).Scheduler) (control : (P).Control)
    (trace : ((PhaseCount.onePacketMenu R leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, event⟩)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (fitting : control.execution.application.current.native.publicView.InclusionFitsDeadline
      R bound event)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (permitted : phaseBindingResponse R leaks owner event payload result serial ∈
      PhaseCount.onePacketActions R leaks bounds owner (control.execution.recall owner)
        (control.execution.observe P owner)) :
    let before := PhaseNativeProjection.execution R leaks plan control.execution
    let response := phaseBindingResponse R leaks owner event payload result serial
    ∃ (entry : (N).PlayerEntry)
      (message : Message Player (WitnessedPacket (serviceGraph setup mode))),
      (PhaseNativeProjection.execution R leaks plan
        (control.execution.respond P owner response)).recall owner =
          before.recall owner ++ [entry] ∧
      FreshCall setup (PhaseNativeProjection.nativeLeaks leaks plan) owner event bound
        entry message := by
  intro before response
  let material : WitnessedSubmission (serviceGraph setup mode) :=
    ⟨⟨.commitment event (owner, .prepared serial), match result with
      | .failure => none
      | .success value => some ⟨payload, value⟩⟩, .none⟩
  let nativeResponse := (R).reactiveBinding (PhaseNativeProjection.nativeLeaks leaks plan)
    owner event payload result serial
  have represented : response = (⟨some material⟩ : (P).Action) := by
    cases result <;> rfl
  have nativeRepresented : nativeResponse = (⟨some material⟩ : (N).Action) := by
    cases result <;> rfl
  let message : Message Player (WitnessedPacket (serviceGraph setup mode)) :=
    ⟨(owner, before.network.nextSerial owner), (N).packet
      ((N).submit before.application owner material) owner (before.network.known owner) material⟩
  let entry : (N).PlayerEntry := ⟨before.observe N owner, nativeResponse, some message⟩
  have raw := (PhaseCount.onePacketMenu R leaks bounds).toRawTrace _ horizon scheduler trace
  have valid := (phaseBindingRecord_history R leaks plan inputs horizon scheduler raw).active
  have allowed : (⟨some material⟩ : (P).Action) ∈ PhaseCount.onePacketActions R leaks bounds
      owner (control.execution.recall owner) (control.execution.observe P owner) := by
    rw [← represented]
    exact permitted
  have fresh := PhaseCount.onePacket_binding_fresh R leaks bounds plan inputs horizon scheduler
    trace owner event serial material.call.opening .none allowed
  have ready : before.application.config.cut.Ready event := request.2.2.1
  have readyView := (before.application.publicView_eventReady event).mpr ready
  have vacant : before.application.accepted (.inr event) = none := by
    cases accepted : before.application.accepted (.inr event) with
    | none => rfl
    | some candidate =>
        exact (ready.1 (valid.toAssociationInvariant.accepted_complete event candidate
          accepted)).elim
  have unused : before.application.HandleUnused (owner, .prepared serial) :=
    fun field accepted => valid.accepted_fixed field _ accepted fresh
  have shape : message.payload =
      ⟨.commitment event (owner, .prepared serial), none, some ⟨event⟩⟩ := by
    dsimp only [message, material]
    rw [reactiveApplication_packet_none,
      before.application.publicView_tokenFor_of_ready _ event rfl ready]
  refine ⟨entry, message, ?_, ?_⟩
  · have same := PhaseNativeProjection.respond_of_onePacket R leaks plan bounds
      control.execution (PhaseCount.countRecall_history R leaks raw) owner response permitted
    rw [same]
    change (before.respond N owner nativeResponse).recall owner = _
    dsimp only [entry]
    rw [nativeRepresented]
    simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
    rfl
  · refine ⟨?_, rfl, rfl, ?_, readyView, fitting, ?_⟩
    · change ∃ supplied, nativeResponse.transmission = some supplied
      rw [nativeRepresented]
      exact ⟨material, rfl⟩
    · rw [shape]
      rfl
    · change (R).freshServiceAcceptable before.application.publicView message
      have concrete : message = ⟨(owner, before.network.nextSerial owner),
          ⟨.commitment event (owner, .prepared serial), none, some ⟨event⟩⟩⟩ := by
        change Message.mk (owner, before.network.nextSerial owner) message.payload = _
        exact congrArg (Message.mk _) shape
      rw [concrete]
      change before.application.publicView.BindingIncludable R
        ⟨(owner, before.network.nextSerial owner), .commitment event (owner, .prepared serial)⟩ ∧ _
      refine ⟨?_, rfl⟩
      cases node : nodeView (serviceGraph setup mode) event with
      | bind actor actual outputEq _codeEq =>
          obtain ⟨rfl, rfl⟩ := EventField.binding.inj (outputEq.symm.trans binding)
          simp only [PublicView.BindingIncludable, node]
          exact ⟨readyView, fitting.withinDeadline, by trivial, by trivial, vacant, unused⟩
      | resolve _ _ _ _ outputEq _codeEq => cases outputEq.symm.trans binding
      | sample _ _ outputEq _codeEq => cases outputEq.symm.trans binding

end Vegas
