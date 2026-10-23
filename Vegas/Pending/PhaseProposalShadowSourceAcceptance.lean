/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalShadowAcceptance
import Vegas.Pending.PhaseBindingCheckpointSubmission
import Vegas.Pending.PhaseStoredCheckpoint

/-! # Constructing repaired binding acceptance from the original history

The original accepted packet supplies native admission conditions. Its
counterpart is derived at the actual repaired prefix; no repaired handler
outcome is assumed. Both prefixes may contain exclusions and retired attempts.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Original counted acceptance constructs the actual repaired accepting
handler and its dynamically normalized shadow. -/
theorem PhaseStateFrame.repair_owned_binding_of_history
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
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ left.execution.network.inputs)
    (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) (candidate : Handle graph)
    (call : message.payload.packet.call = .commitment event candidate)
    (next : PhaseRuntimeState graph)
    (accepted : left.execution.application.handle runtime message = some next) :
    ∃ (nextMemory : BindingShadow graph) (image : PhaseRuntimeState graph),
      right.execution.application.handle runtime message = some image ∧
      nextMemory.OwnBindings owner ∧ nextMemory.candidates = memory.candidates ∧
      (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
      PhaseStateFrame nextMemory owner next image ∧
      nextMemory.CompletedAt image.current.native.config ∧
      (left.execution.application.entry.native.config.store.BindingRefines
          right.execution.application.entry.native.config.store →
        left.execution.application.current.native.config.store.BindingRefines
          right.execution.application.current.native.config.store →
        PreparedBindingResult left.execution.application.current.native
          right.execution.application.current.native candidate payload →
        next.entry.native.config.store.BindingRefines image.entry.native.config.store ∧
        next.current.native.config.store.BindingRefines image.current.native.config.store) := by
  classical
  have rawLeft := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler leftTrace
  have rawRight := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler rightTrace
  have admitted : (message.payload.tokenValid left.execution.application.attempt &&
      left.execution.application.allows message.payload.packet.call &&
      !left.execution.application.current.excludedCall message.payload.packet.call) = true := by
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · assumption
    · cases accepted
  have nativeAccepted : ∃ native, handle runtime left.execution.application.current.native
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
  have count := PhaseCount.countRecall_history runtime leaks rawLeft
  have output : message ∈ (app).outputs (left.execution.recall owner) := by
    rw [← count.1 owner]
    exact List.mem_filter.mpr ⟨member, by simp only [Message.sender, sender, owner, decide_true]⟩
  have signed := phaseOwnCommitmentsFixed_history runtime leaks
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler rawLeft
  change PhaseOwnCommitmentsFixed runtime leaks left.execution at signed
  have originalFixed : left.execution.application.current.native.candidates.lookup candidate ≠
      .fresh := by
    have candidateEq : candidate = (owner, candidate.2) := Prod.ext candidateOwner rfl
    rw [candidateEq]
    exact signed owner message output event candidate.2 (by rwa [← candidateEq])
  have firstNative : left.execution.application.current.native =
      memory.native owner right.execution.application.current.native :=
    congrArg RecoveryState.native frame.current
  have originalFixed' : (memory.native owner
      right.execution.application.current.native).candidates.lookup candidate ≠ .fresh := by
    rw [← firstNative]
    exact originalFixed
  have fixed : right.execution.application.current.native.candidates.lookup candidate ≠
      .fresh := by
    intro fresh
    have candidateEq : candidate = (owner, candidate.2) := Prod.ext candidateOwner rfl
    rw [candidateEq] at originalFixed' fresh
    simp only [BindingShadow.native, CommitmentCandidates.lookup, ite_true] at originalFixed'
    exact originalFixed' ((candidate_fresh_iff memory valid candidate.2 _).mpr fresh)
  have rightReady : right.execution.application.current.native.config.cut.Ready event := by
    rw [frame.current] at ready
    exact ready
  have rightTimely : right.execution.application.current.native.WithinDeadline runtime event := by
    rw [frame.current] at timely
    exact timely
  have rightVacant : right.execution.application.current.native.accepted (.inr event) = none := by
    rw [frame.current] at vacant
    exact vacant
  have rightUnused : right.execution.application.current.native.HandleUnused candidate := by
    rw [frame.current] at unused
    exact unused
  have attempts : left.execution.application.attempt = right.execution.application.attempt := by
    simp only [PhaseRuntimeState.attempt, frame.phases, frame.generation]
  have allows : left.execution.application.allows message.payload.packet.call =
      right.execution.application.allows message.payload.packet.call := by
    simp only [PhaseRuntimeState.allows, frame.phases]
  have excluded : left.execution.application.current.excludedCall message.payload.packet.call =
      right.execution.application.current.excludedCall message.payload.packet.call := by
    rw [frame.current]
    rfl
  have rightAdmitted : (message.payload.tokenValid right.execution.application.attempt &&
      right.execution.application.allows message.payload.packet.call &&
      !right.execution.application.current.excludedCall message.payload.packet.call) = true := by
    rwa [attempts, allows, excluded] at admitted
  have stored := phaseStoredCheckpoint_history runtime leaks plan inputs horizon scheduler rawRight
  have savedMissing := PhaseBindingRepair.saved_uncompleted_of_ready
    right.execution.application stored event rightReady
  obtain ⟨nextMemory, first, image, firstHandled, imageHandled, nextOwned, candidates,
      nextFrame, nextSupport, refineStores⟩ :=
    frame.handle_binding owned supported runtime event payload outputEq codeEq node message
      candidate call rightAdmitted sender candidateOwner rightReady rightTimely rightVacant
        rightUnused fixed originalFixed' savedMissing
  have firstEq : first = next := Option.some.inj (firstHandled.symm.trans accepted)
  subst first
  refine ⟨nextMemory, image, imageHandled, nextOwned, candidates, ?_, nextFrame, nextSupport,
    refineStores⟩
  intro slot
  rw [candidates]
  exact valid slot

end Vegas.EventGraphRuntime.BindingShadow
