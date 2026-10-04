/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingOpeningStep
import Vegas.Pending.ReactiveBindingFrameForeign
import Vegas.Pending.ReactiveCommitmentProtection

/-! # Actual commitment inclusion after a private binding completes

Previously emitted owner commitments are inert when their addressed events
have completed. Foreign commitments use the same fixed candidate meaning.
Both conclusions concern the full inclusion frame and its real receipt.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Actual old owner commitments cannot change completed decisions. Foreign
packets retain their genuine immutable candidate meaning; malformed tokens
and publicly rejected calls are consumed with the same false receipt. -/
theorem commitment_step_completed_owner
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (fixed : runtime.ReactiveCommitmentsFixed leaks original)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (evidence : Option (OpeningFact graph)) (token : Option (ReadinessToken graph))
    (found : original.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩)
    (ownerCompleted : id.1 = owner →
      (WitnessedPacket.mk (.commitment event candidate) evidence token).tokenValid = true →
        event ∈ original.application.config.cut.completed) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  let packet : WitnessedPacket graph := ⟨.commitment event candidate, evidence, token⟩
  by_cases valid : packet.tokenValid = true
  swap
  · exact frame.include_rejected id packet found
      (reactiveApplication_handle_of_not_tokenValid runtime leaks original.application _
        (Bool.eq_false_iff.mpr valid))
      (reactiveApplication_handle_of_not_tokenValid runtime leaks repaired.application _
        (Bool.eq_false_iff.mpr valid))
  by_cases allowed : original.application.publicView.BindingIncludable runtime
      ⟨id, .commitment event candidate⟩
  swap
  · have rejected (state : State graph)
        (same : state.publicView = original.application.publicView) :
        handle runtime state ⟨id, .commitment event candidate⟩ = none := by
      cases handled : handle runtime state ⟨id, .commitment event candidate⟩ with
      | none => rfl
      | some next =>
          have includable := (State.publicView_bindingIncludable runtime state id event
            candidate).mpr (by simp only [handled, Option.isSome_some])
          exact False.elim (allowed (same ▸ includable))
    exact frame.include_rejected id packet found
      (reactiveHandle_none (rejected original.application rfl))
      (reactiveHandle_none (rejected repaired.application frame.publicView.symm))
  obtain ⟨named, addressed, tokened⟩ := (WitnessedPacket.tokenValid_iff packet).mp valid
  have eventEq : named = event := (Option.some.inj addressed).symm
  subst named
  change token = some ⟨event⟩ at tokened
  subst token
  change original.application.publicView.EventReady event ∧
    original.application.WithinDeadline runtime event ∧ _ at allowed
  obtain ⟨publicReady, timely, checks⟩ := allowed
  have ready := (original.application.publicView_eventReady event).mp publicReady
  cases node : nodeView graph event with
  | resolve actor payload binding guards outputEq codeEq => simp only [node] at checks
  | sample payload law outputEq codeEq => simp only [node] at checks
  | bind actor payload outputEq codeEq =>
      simp only [node, Message.sender] at checks
      obtain ⟨sender, owned, vacant, unused⟩ := checks
      have foreign : actor ≠ owner := by
        intro same
        exact ready.1 (ownerCompleted (sender.trans same) valid)
      have immutable := fixed.lookup id _ found event candidate rfl (owned.trans sender.symm)
      exact frame.foreign_binding_inclusion onlyBindings id event candidate actor foreign payload
        outputEq codeEq node ready timely sender owned vacant unused immutable evidence found

end Vegas.EventGraphRuntime.BindingMemory.Frame
