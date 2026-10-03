/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingCopiedSubmission
import Vegas.Pending.ReactiveBindingUsedCommitment

/-! # Copying a bare commitment to another player's handle

The immutable handle owner differs from the authenticated sender. Submission
cannot register or freeze that handle and changes no application state. Its
public handler rejection is permanent, independent of private candidate data.
These facts preserve the actual response and inclusion frame without an audit
verdict, candidate nonfreshness or an additional fine.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- This class inspects only the chosen bare response and its sender. The
addressed event and foreign candidate need not be ready, owned or fixed. -/
def ForeignHandleCommitmentResponse (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (response : (runtime.reactiveApplication leaks).Action) : Prop :=
  ∃ event candidate opening, candidate.1 ≠ owner ∧
    response = ⟨some ⟨⟨.commitment event candidate, opening⟩, .none⟩⟩

/-- Neither private registration nor commitment freezing may touch another
player's handle, including a fresh foreign prepared slot. -/
theorem reactiveApplication_submit_foreign_commitment
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (state : State graph) (who : Player) (event : graph.EventId)
    (candidate : Handle graph) (opening : Option (Raw L)) (request : EvidenceRequest graph)
    (foreign : candidate.1 ≠ who) :
    (runtime.reactiveApplication leaks).submit state who
      ⟨⟨.commitment event candidate, opening⟩, request⟩ = state := by
  rcases candidate with ⟨author, slot⟩
  change author ≠ who at foreign
  cases slot <;> cases opening <;>
    simp [reactiveApplication, Submission.register, submitStep, foreign]

/-- The copy engine leaves all private memory unchanged for a foreign handle;
no owned registration occurs even if that handle is fresh. -/
theorem BindingMemory.copyResponse_foreign
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (memory : BindingMemory runtime leaks)
    (actual : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (candidate : Handle graph) (opening : Option (Raw L))
    (request : EvidenceRequest graph) (foreign : candidate.1 ≠ owner) :
    memory.copyResponse runtime leaks owner actual
      ⟨some ⟨⟨.commitment event candidate, opening⟩, request⟩⟩ =
      (⟨some ⟨⟨.commitment event candidate, opening⟩, request⟩⟩, memory.shadow) := by
  rcases candidate with ⟨author, slot⟩
  change author ≠ owner at foreign
  simp only [copyResponse, foreign, false_and, ↓reduceIte]

omit [DecidableEq Player] in
/-- A public commitment inclusion requires candidate ownership by the
authenticated sender. A foreign handle therefore fails at every state. -/
theorem State.bindingIncludable_false_of_foreign_handle
    (runtime : EventGraphRuntime graph) (state : State graph)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (foreign : candidate.1 ≠ id.1) :
    ¬ state.publicView.BindingIncludable runtime ⟨id, .commitment event candidate⟩ := by
  intro allowed
  change state.publicView.EventReady event ∧ state.WithinDeadline runtime event ∧ _ at allowed
  obtain ⟨_ready, _timely, checks⟩ := allowed
  cases node : nodeView graph event with
  | resolve | sample => simp only [node] at checks
  | bind actor payload outputEq codeEq =>
      simp only [node, Message.sender] at checks
      obtain ⟨sender, owned, _vacant, _unused⟩ := checks
      exact foreign (owned.trans sender.symm)

end Vegas.EventGraphRuntime
