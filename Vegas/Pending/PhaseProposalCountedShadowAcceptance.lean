/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowAcceptance
import Vegas.Pending.PhaseBindingMemoryFreshness
import Vegas.Pending.PhaseBindingCheckpointSubmission
import Vegas.Pending.PhaseLatestBindingHistory
import Vegas.Pending.PhaseOwnCommitments

/-! # General shadow acceptance from actual counted provenance

Actual packet inclusion determines its native handler conditions and its
absence from the saved checkpoint. The normalized image is then constructed
with a dynamically masked shadow, without a clear-attempt assumption.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every actual accepted owned commitment has a constructed actual handler
image after general recovery, with original immutable inputs left literal. -/
theorem PhaseStateFrame.handle_owned_binding_of_history
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    {memory : BindingShadow graph} {owner : Player} {original : PhaseRuntimeState graph}
    (frame : PhaseStateFrame memory owner original control.execution.application)
    (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (supported : memory.CompletedAt control.execution.application.current.native.config)
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ control.execution.network.inputs)
    (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (next : PhaseRuntimeState graph)
    (accepted : control.execution.application.handle runtime message = some next) :
    ∃ (nextMemory : BindingShadow graph) (image : PhaseRuntimeState graph),
      original.handle runtime message = some image ∧ nextMemory.OwnBindings owner ∧
      nextMemory.candidates = memory.candidates ∧
      (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
      PhaseStateFrame nextMemory owner image next ∧
      nextMemory.CompletedAt next.current.native.config := by
  classical
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  have admitted : (message.payload.tokenValid control.execution.application.attempt &&
      control.execution.application.allows message.payload.packet.call &&
      !control.execution.application.current.excludedCall message.payload.packet.call) = true := by
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · assumption
    · cases accepted
  have nativeAccepted : ∃ native, handle runtime control.execution.application.current.native
      ⟨message.id, .commitment event candidate⟩ = some native := by
    unfold PhaseRuntimeState.handle at accepted
    rw [admitted] at accepted
    simp only [↓reduceIte, call, Option.map_eq_some_iff] at accepted
    obtain ⟨native, handled, _⟩ := accepted
    exact ⟨native, handled⟩
  obtain ⟨native, handled⟩ := nativeAccepted
  obtain ⟨ready, timely, actor, ty, outputEq, codeEq, node, sender, candidateOwner,
      vacant, unused⟩ := handle_commitment_conditions runtime _ native message.id event candidate
        handled
  obtain ⟨actorEq, typeEq⟩ := EventField.binding.inj (outputEq.symm.trans binding)
  subst actorEq
  subst typeEq
  let owner := actor
  let payload := ty
  have count := PhaseCount.countRecall_history runtime leaks rawTrace
  have output : message ∈ (app).outputs (control.execution.recall owner) := by
    rw [← count.1 owner]
    exact List.mem_filter.mpr ⟨member, by simp only [Message.sender, sender, owner, decide_true]⟩
  have signed := phaseOwnCommitmentsFixed_history runtime leaks
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler rawTrace
  change PhaseOwnCommitmentsFixed runtime leaks control.execution at signed
  have fixed : control.execution.application.current.native.candidates.lookup candidate ≠
      .fresh := by
    have candidateEq : candidate = (owner, candidate.2) := Prod.ext candidateOwner rfl
    rw [candidateEq]
    exact signed owner message output event candidate.2 (by rwa [← candidateEq])
  have originalFixed : (memory.native owner
      control.execution.application.current.native).candidates.lookup candidate ≠ .fresh := by
    intro fresh
    have candidateEq : candidate = (owner, candidate.2) := Prod.ext candidateOwner rfl
    rw [candidateEq] at fresh fixed
    simp only [BindingShadow.native, CommitmentCandidates.lookup, ite_true] at fresh
    exact fixed ((candidate_fresh_iff memory valid candidate.2 _).mp fresh)
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler rawTrace
  have savedMissing := PhaseBindingRepair.saved_uncompleted_of_ready
    control.execution.application stored event ready
  obtain ⟨nextMemory, image, second, imageHandled, secondHandled, nextOwned, candidates,
      nextFrame, nextSupport⟩ := frame.handle_binding owned supported runtime event payload outputEq
        codeEq node message candidate call admitted sender candidateOwner ready timely vacant unused
        fixed originalFixed savedMissing
  have secondEq : second = next := Option.some.inj (secondHandled.symm.trans accepted)
  subst second
  refine ⟨nextMemory, image, imageHandled, nextOwned, candidates, ?_, nextFrame, nextSupport⟩
  intro slot
  rw [candidates]
  exact valid slot

end Vegas.EventGraphRuntime.BindingShadow
