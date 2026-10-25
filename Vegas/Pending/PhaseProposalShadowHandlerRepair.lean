/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalShadowSourceAcceptance
import Vegas.Pending.PhaseProposalShadowForeignBinding
import Vegas.Pending.PhaseProposalShadowOpeningAcceptance

/-! # All actual accepting phase handlers in a designated-owner repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- An actual accepting original packet determines its repaired successor.
Both prefixes are genuine counted histories; persistent physical records are
used only for the designated owner's submitted bindings. Every guard-failed
opening is retained as its original authentic plaintext and public result. -/
theorem PhaseStateFrame.handler_repair
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (left right : (app).Control)
    (leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some left))
    (rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some right))
    {memory : BindingShadow graph} {owner : Player}
    (frame : PhaseStateFrame memory owner left.execution.application right.execution.application)
    (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (supported : memory.CompletedAt right.execution.application.current.native.config)
    (prepared : PreparedBindings runtime leaks owner left.execution right.execution)
    (entryRef : left.execution.application.entry.native.config.store.BindingRefines
      right.execution.application.entry.native.config.store)
    (currentRef : left.execution.application.current.native.config.store.BindingRefines
      right.execution.application.current.native.config.store)
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ left.execution.network.inputs)
    (next : PhaseRuntimeState graph)
    (accepted : left.execution.application.handle runtime message = some next) :
    ∃ (nextMemory : BindingShadow graph) (image : PhaseRuntimeState graph),
      right.execution.application.handle runtime message = some image ∧
      nextMemory.OwnBindings owner ∧
      (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
      PhaseStateFrame nextMemory owner next image ∧
      nextMemory.CompletedAt image.current.native.config ∧
      next.entry.native.config.store.BindingRefines image.entry.native.config.store ∧
      next.current.native.config.store.BindingRefines image.current.native.config.store := by
  classical
  cases call : message.payload.packet.call with
  | malformed raw =>
      unfold PhaseRuntimeState.handle at accepted
      split at accepted
      · simp only [call, handle, Option.map_none] at accepted
        cases accepted
      · cases accepted
  | opening event candidate raw =>
      obtain ⟨nextMemory, image, handled, nextOwned, candidates, paired, nextSupport,
          nextEntryRef, nextCurrentRef⟩ :=
        frame.repair_opening_of_history runtime leaks bounds plan inputs horizon scheduler left
          right leftTrace rightTrace owned supported entryRef currentRef message event candidate raw
            call next accepted
      refine ⟨nextMemory, image, handled, nextOwned, ?_, paired, nextSupport, nextEntryRef,
        nextCurrentRef⟩
      intro slot
      rw [candidates]
      exact valid slot
  | commitment event candidate =>
      have nativeAccepted : ∃ native, handle runtime left.execution.application.current.native
          ⟨message.id, .commitment event candidate⟩ = some native := by
        unfold PhaseRuntimeState.handle at accepted
        split at accepted
        · simp only [call, Option.map_eq_some_iff] at accepted
          obtain ⟨native, handled, _⟩ := accepted
          exact ⟨native, handled⟩
        · cases accepted
      obtain ⟨native, handled⟩ := nativeAccepted
      obtain ⟨_ready, _timely, actor, payload, outputEq, codeEq, node, sender, candidateOwner,
          _vacant, _unused, _⟩ :=
            (handle_commitment_iff runtime _ native message.id event candidate).mp handled
      by_cases same : actor = owner
      · subst same
        let owner := actor
        obtain ⟨nextMemory, image, handled, nextOwned, _candidates, nextValid, paired,
            nextSupport, refinement⟩ :=
          frame.repair_owned_binding_of_history runtime leaks bounds plan inputs horizon scheduler
            left right leftTrace rightTrace owned valid supported message member event payload
              outputEq candidate call next accepted
        have typed :=
          prepared message member sender event candidate call payload outputEq codeEq node
        exact ⟨nextMemory, image, handled, nextOwned, nextValid, paired, nextSupport,
          (refinement entryRef currentRef typed).1, (refinement entryRef currentRef typed).2⟩
      · have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler leftTrace
        have count := PhaseCount.countRecall_history runtime leaks rawTrace
        have output : message ∈ (app).outputs (left.execution.recall actor) := by
          rw [← count.1 actor]
          exact List.mem_filter.mpr ⟨member, by simp only [Message.sender, sender, decide_true]⟩
        have signed := phaseOwnCommitmentsFixed_history runtime leaks
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler rawTrace
        have fixed : left.execution.application.current.native.candidates.lookup candidate ≠
            .fresh := by
          have candidateEq : candidate = (actor, candidate.2) := Prod.ext candidateOwner rfl
          rw [candidateEq]
          exact signed actor message output event candidate.2 (by rwa [← candidateEq])
        obtain ⟨nextMemory, image, handled, nextOwned, candidates, paired, nextSupport,
            refinement⟩ := frame.repair_foreign_binding owned supported runtime actor same event
              payload outputEq message candidate call fixed next accepted
        refine ⟨nextMemory, image, handled, nextOwned, ?_, paired, nextSupport,
          (refinement entryRef currentRef).1, (refinement entryRef currentRef).2⟩
        intro slot
        rw [candidates]
        exact valid slot

end Vegas.EventGraphRuntime.BindingShadow
