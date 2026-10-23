/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ReservedEpochPairedWord

/-! # Current binding packets share their actual physical acceptance condition -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem frontierQualification_sent_binding_iff {length : Nat}
    (tape : Tape Player length) (execution : (app).Execution) (owner : Player)
    (event : graph.EventId) (candidate : Handle graph) (material : WitnessedSubmission graph)
    (call : material.call.packet = .commitment event candidate) :
    frontierQualification runtime leaks tape (execution.respond app owner ⟨some material⟩)
        owner event ↔
      ∃ entered, execution.application.current.native.activatedAt event = some entered ∧
        ∃ epoch, tape.nextProcessingEpoch (execution.environmentRecall.length /
            cycleWidth (graph := graph) (packetCapacity runtime) + 1) = some epoch ∧
          epoch < completionCycles runtime ∧ epoch - entered < runtime.deadline event := by
  classical
  let sent := execution.respond app owner ⟨some material⟩
  let message : Message Player (app).Payload :=
    ⟨(owner, execution.network.nextSerial owner),
      (app).packet ((app).submit execution.application owner material) owner
        (execution.network.known owner) material⟩
  have pending : message ∈ sent.network.pending := by
    change message ∈ execution.network.pending ++ [message]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have emitted : message ∈ (app).outputs (sent.recall owner) := by
    simp [sent, ReactiveApplication.Execution.respond, MessageNetwork.submit,
      ReactiveApplication.outputs, message]
  have named : message.payload.packet.call = .commitment event candidate := by
    change (PhaseRuntimeState.emit (execution.application.submit owner material) owner
      (execution.network.known owner) material).packet.call = _
    rw [phase_emit_call, call]
  have addressed : message.payload.attempt = sent.application.attempt := rfl
  have notUnsent : ¬ ∀ packet ∈ (app).outputs (sent.recall owner),
      PhaseCount.event? packet.payload ≠ some ⟨sent.application.attempt, event⟩ := by
    intro absent
    apply absent message emitted
    simp only [PhaseCount.event?, named, Payload.event?, Option.map_some, addressed]
  have activated : sent.application.current.native.activatedAt =
      execution.application.current.native.activatedAt :=
    congrArg (fun view : PhasePublicView graph => view.native.activatedAt)
      (PhaseCount.submit_publicView execution.application owner material)
  change frontierQualification runtime leaks tape sent owner event ↔ _
  unfold frontierQualification
  dsimp only
  simp only [notUnsent, ↓reduceIte]
  constructor
  · rintro ⟨entered, stamp, _packet, _pending, _candidate, _sender, _call,
      _address, epoch, selected, bounded, timely⟩
    refine ⟨entered, (congrFun activated event).symm.trans stamp, epoch, ?_, bounded, timely⟩
    simpa only [sent, (app).respond_environmentRecall] using selected
  · rintro ⟨entered, stamp, epoch, selected, bounded, timely⟩
    refine ⟨entered, (congrFun activated event).trans stamp, message, pending, candidate,
      rfl, named, addressed, epoch, ?_, bounded, timely⟩
    simpa only [sent, (app).respond_environmentRecall] using selected

/-- Two current binding packets can carry different prepared results and still
have the same finite service condition. No equality of either catalogue or of
the later physical packet words is required. -/
theorem ownedAcceptanceWord_sent_binding_eq {length : Nat}
    (tape : Tape Player length) (ordered : graph.RevealRelaxedOrdered)
    (execution : (app).Execution) (owner : Player) (frontier : graph.EventId)
    (leftCandidate rightCandidate : Handle graph)
    (leftMaterial rightMaterial : WitnessedSubmission graph)
    (leftCall : leftMaterial.call.packet = .commitment frontier leftCandidate)
    (rightCall : rightMaterial.call.packet = .commitment frontier rightCandidate)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, frontier⟩) (event : graph.EventId) :
    ownedAcceptanceWord runtime leaks tape (execution.respond app owner ⟨some leftMaterial⟩)
        owner event ↔
      ownedAcceptanceWord runtime leaks tape (execution.respond app owner ⟨some rightMaterial⟩)
        owner event := by
  classical
  have leftRequest := respond_request runtime leaks execution owner ⟨some leftMaterial⟩ owner
    ⟨execution.application.attempt, frontier⟩ request
  have rightRequest := respond_request runtime leaks execution owner ⟨some rightMaterial⟩ owner
    ⟨execution.application.attempt, frontier⟩ request
  have leftActive : owner ∉
      (execution.respond app owner ⟨some leftMaterial⟩).application.current.excluded :=
    request.2.2.2.2
  have rightActive : owner ∉
      (execution.respond app owner ⟨some rightMaterial⟩).application.current.excluded :=
    request.2.2.2.2
  have frontierEq :
      frontierQualification runtime leaks tape
          (execution.respond app owner ⟨some leftMaterial⟩) owner frontier ↔
        frontierQualification runtime leaks tape
          (execution.respond app owner ⟨some rightMaterial⟩) owner frontier :=
    (frontierQualification_sent_binding_iff runtime leaks tape execution owner frontier
      leftCandidate leftMaterial leftCall).trans
        (frontierQualification_sent_binding_iff runtime leaks tape execution owner frontier
          rightCandidate rightMaterial rightCall).symm
  simp only [ownedAcceptanceWord, leftActive, rightActive, ↓reduceIte]
  constructor
  · intro survived other requested
    have same : other = frontier := ordered.ready_actor_unique _ rightRequest.2.2.1
      requested.2.2.1 rightRequest.2.2.2.1 requested.2.2.2.1
    subst other
    exact (survived frontier leftRequest).imp_right frontierEq.mp
  · intro survived other requested
    have same : other = frontier := ordered.ready_actor_unique _ leftRequest.2.2.1
      requested.2.2.1 leftRequest.2.2.2.1 requested.2.2.2.1
    subst other
    exact (survived frontier rightRequest).imp_right frontierEq.mpr

/-- Counted availability identifies the same actual current binding frontier
for both nonsilent aliases, while each prepared value remains literal. -/
theorem ownedAcceptanceWord_available_bindings_eq
    {length : Nat} (tape : Tape Player length)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (leftMaterial rightMaterial : WitnessedSubmission graph)
    (leftAvailable : (⟨some leftMaterial⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner (execution.recall owner)
        (execution.observe app owner))
    (rightAvailable : (⟨some rightMaterial⟩ : (app).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner (execution.recall owner)
        (execution.observe app owner))
    (phase : RuntimePhase graph) (installed : phase ∈ execution.application.phases.head?)
    (commitment : phase.kind = .commitment) (event : graph.EventId) :
    ownedAcceptanceWord runtime leaks tape (execution.respond app owner ⟨some leftMaterial⟩)
        owner event ↔
      ownedAcceptanceWord runtime leaks tape (execution.respond app owner ⟨some rightMaterial⟩)
        owner event := by
  classical
  obtain ⟨coordinate, requested⟩ := PhaseCount.onePacket_request_of_nonsilent runtime leaks
    bounds plan inputs horizon scheduler remaining owner execution trace leftMaterial leftAvailable
  obtain ⟨currentPhase, present, inside⟩ := requested.2.1
  have equal : currentPhase = phase := Option.some.inj
    ((Option.mem_def.mp present).symm.trans (Option.mem_def.mp installed))
  subst currentPhase
  have ranks := (phase.mem_events coordinate.event).mp inside
  obtain ⟨actor, payload, binding⟩ :=
    commitment ▸ phase.fields coordinate.event ranks.1 ranks.2
  have sameOwner : actor = owner := Option.some.inj
    (((graph).actor?_of_outputLayout_binding binding).symm.trans requested.2.2.2.1)
  subst actor
  have request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, coordinate.event⟩ := ⟨rfl, requested.2⟩
  obtain ⟨leftSerial, _leftPreparation, _leftEvidence, leftShape, _leftBounded, _leftFresh⟩ :=
    PhaseCount.onePacket_binding_shape runtime leaks bounds plan ordered inputs horizon scheduler
      remaining owner execution trace coordinate.event payload binding request leftMaterial
        leftAvailable
  obtain ⟨rightSerial, _rightPreparation, _rightEvidence, rightShape, _rightBounded,
      _rightFresh⟩ :=
    PhaseCount.onePacket_binding_shape runtime leaks bounds plan ordered inputs horizon scheduler
      remaining owner execution trace coordinate.event payload binding request rightMaterial
        rightAvailable
  exact ownedAcceptanceWord_sent_binding_eq runtime leaks tape ordered execution owner
    coordinate.event (owner, .prepared leftSerial) (owner, .prepared rightSerial)
      leftMaterial rightMaterial (by rw [leftShape]) (by rw [rightShape]) request event

end Vegas.EventGraphRuntime.ReservedEpoch
