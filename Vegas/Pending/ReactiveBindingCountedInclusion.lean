/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveBindingSubmittedInclusion
import Vegas.Pending.ReactiveBindingRejectedInclusion
import Vegas.Pending.ReactiveBindingFrameForeign
import Vegas.Pending.ReactiveSignedCommitments

/-! # Complete count-admitted opaque inclusion cases -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Every retained count-admitted commitment has a concrete inclusion frame,
for either owner and whether the contract accepts or rejects it. Delayed own
acceptance obtains its original private result from recorded submission
provenance; foreign acceptance reads the unchanged foreign catalogue. -/
theorem counted_binding_inclusion (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (recorded : memory.RecordsSubmittedBindings runtime leaks owner original repaired)
    (clean : runtime.CountClean leaks original)
    (signed : runtime.SignedCommitments leaks original)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (evidence : Option (OpeningFact graph)) (token : Option (ReadinessToken graph))
    (found : original.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  have member := input_of_lookup clean.1 signed.provenance id _ found
  obtain ⟨valid, correct, _⟩ := (countPermits_eq_true_iff _ _).mp (clean.2 _ member)
  change bindingOwnedBy graph id.1 event = true ∧ evidence = none ∧
    candidate.1 = id.1 ∧ _ at correct
  obtain ⟨bindingOwned, rfl, candidateOwner, _⟩ := correct
  obtain ⟨tokenEvent, named, tokenEq⟩ := (WitnessedPacket.tokenValid_iff _).mp valid
  change some event = some tokenEvent at named
  cases Option.some.inj named
  change token = some ⟨event⟩ at tokenEq
  subst token
  by_cases includable : original.application.publicView.BindingIncludable runtime
      ⟨id, .commitment event candidate⟩
  · cases node : nodeView graph event with
    | sample payload law outputEq codeEq =>
        simp only [bindingOwnedBy, outputEq] at bindingOwned
        cases bindingOwned
    | resolve actor payload binding checks outputEq codeEq =>
        simp only [bindingOwnedBy, outputEq] at bindingOwned
        cases bindingOwned
    | bind actor payload outputEq codeEq =>
        have sender : id.1 = actor := by
          have same : actor = id.1 := by
            simpa only [bindingOwnedBy, outputEq, decide_eq_true_eq] using bindingOwned
          exact same.symm
        have owned : candidate.1 = actor := candidateOwner.trans sender
        simp only [PublicView.BindingIncludable, node] at includable
        change original.application.publicView.EventReady event ∧
          original.application.WithinDeadline runtime event ∧ _ at includable
        obtain ⟨readyPublic, timely, rest⟩ := includable
        have ready := (original.application.publicView_eventReady event).mp readyPublic
        change id.1 = actor ∧ candidate.1 = actor ∧
          original.application.accepted (.inr event) = none ∧
          original.application.HandleUnused candidate at rest
        obtain ⟨_, _, vacant, unused⟩ := rest
        by_cases sameOwner : actor = owner
        · cases sameOwner
          exact frame.recorded_binding_inclusion recorded clean.1 signed.provenance event payload
            outputEq codeEq node id candidate sender owned found ready timely vacant unused
        · have output : (⟨id, ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩ :
              Message Player (WitnessedPacket graph)) ∈
                (runtime.reactiveApplication leaks).outputs (original.recall actor) := by
            rw [← clean.1.1 actor]
            exact List.mem_filter.mpr ⟨member, by simpa [Message.sender] using sender⟩
          have candidateEq : candidate = (actor, candidate.2) := Prod.ext owned rfl
          have fixed : original.application.candidates.lookup candidate ≠ .fresh := by
            rw [candidateEq]
            apply signed.ownFixed actor _ output event candidate.2
            exact congrArg (Payload.commitment event) candidateEq
          exact frame.foreign_binding_inclusion onlyBindings id event candidate actor sameOwner
            payload outputEq codeEq node ready timely sender owned vacant unused fixed none found
  · have refused (state : State graph)
        (publicEq : state.publicView = original.application.publicView) :
        handle runtime state ⟨id, .commitment event candidate⟩ = none := by
      cases handled : handle runtime state ⟨id, .commitment event candidate⟩ with
      | none => rfl
      | some next =>
          apply False.elim
          apply includable
          rw [← publicEq]
          apply (state.publicView_bindingIncludable runtime id event candidate).mpr
          rw [handled]
          rfl
    exact frame.include_rejected id _ found
      (by simpa only [reactiveApplication_handle, WitnessedPacket.tokenValid_commitment,
        ite_true] using refused original.application rfl)
      (by simpa only [reactiveApplication_handle, WitnessedPacket.tokenValid_commitment,
        ite_true] using refused repaired.application frame.publicView.symm)

end Vegas.EventGraphRuntime.BindingMemory.Frame
