/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingFreshCall
import Vegas.Pending.PhaseNativeTrace
import Vegas.Pending.ReactiveEmissionTokens

/-! # Exact remembered binding emissions satisfy protected-call conformance -/

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
local notation "NL" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "N" => serviceApplication setup mode deadline NL

/-- A real retained canonical binding response supplies the original fresh-call
certificate for its actual emitted packet. Token, sender, global handle
freshness and binding provenance are derived, including for typed failure. -/
theorem phase_recalled_binding_freshCall
    (bounds : MessageBounds (serviceGraph setup mode))
    (ordered : (serviceGraph setup mode).RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    (current before : (P).Control)
    (trace : ((PhaseCount.onePacketMenu R leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (prior : ((PhaseCount.onePacketMenu R leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
    (clear : current.execution.application.current.excluded = ∅)
    (owner : Player) (entry : (P).PlayerEntry) (recorded : entry ∈ current.execution.recall owner)
    (viewed : entry.beforeView = before.execution.observe P owner)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (request : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, event⟩)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (fitting : before.execution.application.current.native.publicView.InclusionFitsDeadline R
      bound event)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (response : entry.action = phaseBindingResponse R leaks owner event payload result serial)
    (permitted : entry.action ∈ PhaseCount.onePacketActions R leaks bounds owner
      (before.execution.recall owner) (before.execution.observe P owner)) :
    ∃ message, FreshCall setup NL owner event bound
      (PhaseNativeProjection.playerEntry R leaks plan entry) message := by
  let nativeEntry := PhaseNativeProjection.playerEntry R leaks plan entry
  let material : WitnessedSubmission (serviceGraph setup mode) :=
    ⟨⟨.commitment event (owner, .prepared serial), match result with
      | .failure => none
      | .success value => some ⟨payload, value⟩⟩, .none⟩
  have transmitted : nativeEntry.action.transmission = some material := by
    change entry.action.transmission = some material
    rw [response]
    cases result <;> rfl
  have nativePrior := PhaseNativeProjection.nativeTrace R leaks plan bounds ordered maximal inputs
    horizon scheduler trace (fun _ same => by cases same; exact clear)
  have nativeRecorded : nativeEntry ∈
      (PhaseNativeProjection.execution R leaks plan current.execution).recall owner :=
    List.mem_map.mpr ⟨entry, recorded, rfl⟩
  obtain ⟨message, emitted, call⟩ :=
    (reactiveEmission_history R NL (inputs.map State.initial) horizon
      (PhaseNativeProjection.nativeScheduler R leaks plan scheduler)
      (PhaseNativeProjection.control R leaks plan current) nativePrior owner).2
        nativeEntry nativeRecorded material transmitted
  have callEq : message.payload.call = .commitment event (owner, .prepared serial) := call
  have token := history_emissionTokens R NL (inputs.map State.initial) horizon
    (PhaseNativeProjection.nativeScheduler R leaks plan scheduler) nativePrior owner nativeEntry
      nativeRecorded message emitted
  have nativeViewed : nativeEntry.beforeView.application =
      before.execution.application.current.native.playerView owner := by
    change entry.beforeView.application.1 = _
    rw [viewed]
    rfl
  have ready := request.2.2.1
  have readyView := (before.execution.application.current.native.publicView_eventReady event).mpr
    ready
  have attached : message.payload.token = some ⟨event⟩ := by
    rw [token, callEq, nativeViewed]
    exact before.execution.application.current.native.publicView_tokenFor_of_ready _ event rfl ready
  have recalled := (N).history_inputRecall (inputs.map State.initial) horizon
    (PhaseNativeProjection.nativeScheduler R leaks plan scheduler) nativePrior
  change (PhaseNativeProjection.execution R leaks plan current.execution).InputRecall N at recalled
  have output : message ∈ (N).outputs
      ((PhaseNativeProjection.execution R leaks plan current.execution).recall owner) :=
    List.mem_filterMap.mpr ⟨nativeEntry, nativeRecorded, emitted⟩
  rw [← recalled owner] at output
  have authored : message.sender = owner := of_decide_eq_true (List.mem_filter.mp output).2
  have raw := (PhaseCount.onePacketMenu R leaks bounds).toRawTrace _ horizon scheduler prior
  have valid := (phaseBindingRecord_history R leaks plan inputs horizon scheduler raw).active
  have offered : (⟨some material⟩ : (P).Action) ∈ PhaseCount.onePacketActions R leaks bounds owner
      (before.execution.recall owner) (before.execution.observe P owner) := by
    have represented : phaseBindingResponse R leaks owner event payload result serial =
        (⟨some material⟩ : (P).Action) := by cases result <;> rfl
    rw [response, represented] at permitted
    exact permitted
  have fresh := PhaseCount.onePacket_binding_fresh R leaks bounds plan inputs horizon scheduler
    prior owner event serial material.call.opening .none offered
  have vacant : before.execution.application.current.native.accepted (.inr event) = none := by
    cases accepted : before.execution.application.current.native.accepted (.inr event) with
    | none => rfl
    | some candidate =>
        exact (ready.1 (valid.toAssociationInvariant.accepted_complete event candidate
          accepted)).elim
  have unused : before.execution.application.current.native.HandleUnused
      (owner, .prepared serial) := fun field accepted => valid.accepted_fixed field _ accepted fresh
  refine ⟨message, ⟨⟨material, transmitted⟩, emitted, authored, ?_, ?_, ?_, ?_⟩⟩
  · rw [callEq]
    rfl
  · rw [nativeViewed]
    exact readyView
  · rw [nativeViewed]
    exact fitting
  · change (R).freshServiceAcceptable nativeEntry.beforeView.application.publicView message
    simp only [freshServiceAcceptable, callEq]
    refine ⟨?_, attached⟩
    rw [nativeViewed]
    cases node : nodeView (serviceGraph setup mode) event with
    | bind actor actual outputEq _codeEq =>
        obtain ⟨rfl, rfl⟩ := EventField.binding.inj (outputEq.symm.trans binding)
        simp only [PublicView.BindingIncludable, node]
        exact ⟨readyView, fitting.withinDeadline, authored, by trivial, vacant, unused⟩
    | resolve _ _ _ _ outputEq _codeEq => cases outputEq.symm.trans binding
    | sample _ _ outputEq _codeEq => cases outputEq.symm.trans binding

end Vegas
