/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingOpeningInclusion
import Vegas.Pending.PhaseBindingOpeningRead

/-! # Actual counted opening inclusion during a directed binding repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- An authentic counted opening is replayed from its actual source history.
Its surviving typed binding, image certificate, native guard result, and image
exclusion update are derived rather than supplied as repair hypotheses. -/
theorem counted_opening_inclusion
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (remaining : Nat) (actorTurn : Option Player)
    (left : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, actorTurn, original⟩))
    (right : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, actorTurn, repaired⟩))
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ original.network.inputs)
    (found : original.network.lookup message.id = some message)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (opening : message.payload.packet.call = .opening event candidate raw)
    (request : original.application.SeedRequest message.sender
      ⟨message.payload.attempt, event⟩)
    (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (timely : original.application.current.native.WithinDeadline runtime event)
    (clear : (original.includePending (phaseApplication runtime leaks)
      message.id).application.current.excluded = ∅) :
    Frame runtime leaks memory owner
      { original.includePending (phaseApplication runtime leaks) message.id with
        environmentRecall := original.environmentRecall ++
          [⟨original.observeEnvironment (phaseApplication runtime leaks), .include message.id⟩] }
      { repaired.includePending (phaseApplication runtime leaks) message.id with
        environmentRecall := repaired.environmentRecall ++
          [⟨repaired.observeEnvironment (phaseApplication runtime leaks),
            .include message.id⟩] } := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawLeft := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler left
  have rawRight := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler right
  have leftBinding := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler rawLeft
  have rightBinding := phaseBindingRecord_history runtime leaks plan inputs horizon
    scheduler rawRight
  have physical := PhaseCount.physicalBindings_history runtime leaks bounds plan inputs horizon
    scheduler left
  have permitted := (PhaseCount.permits_eq_true_iff _ _).mp (physical.clean.2 message member)
  obtain ⟨value, typed, stored, associated, fixed⟩ := opening_binding_success runtime leaks
    bounds plan inputs horizon scheduler left message member event candidate raw opening request
      actor payload binding checks outputEq codeEq node
  obtain ⟨imageStored, other, accepted, _imageAccepted, owned, _, imageFixed⟩ :=
    frame.live.successful_opening leftBinding.active rightBinding.active binding value stored
  have equal : candidate = other := Option.some.inj (associated.symm.trans accepted)
  subst other
  have correct := permitted.2.1
  unfold CountCallCorrect at correct
  dsimp only [PhaseCount.nativeMessage] at correct
  rw [opening] at correct
  simp only [node] at correct
  have sender : message.id.1 = actor := correct.2.1
  obtain ⟨named, addressed, attached⟩ :=
    (WitnessedPacket.tokenValid_iff message.payload.packet).mp permitted.1
  have sameEvent : named = event := by
    have same := addressed
    rw [opening] at same
    exact Option.some.inj same.symm
  subst named
  have packet : PhaseCount.nativeMessage message =
      ⟨message.id, ⟨.opening event candidate ⟨payload, value⟩,
        message.payload.packet.evidence, some ⟨event⟩⟩⟩ := by
    change (⟨message.id, ⟨message.payload.packet.call, message.payload.packet.evidence,
      message.payload.packet.token⟩⟩ : Message Player (WitnessedPacket graph)) = _
    rw [opening, typed, attached]
  have defined := EventCode.resolveOutput?_isSome binding checks true
    original.application.current.native.config.store (by
      intro field read
      apply original.application.current.native.config.read_available request.2.2.1
      rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
      exact read)
  obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp defined
  have token : message.payload.tokenValid original.application.attempt = true :=
    Bool.and_eq_true_iff.mpr ⟨decide_eq_true_eq.mpr request.1, permitted.1⟩
  have allowed : original.application.allows message.payload.packet.call = true := by
    obtain ⟨phase, member, inside⟩ := request.2.1
    have head : original.application.phases.head? = some phase := member
    simp only [PhaseRuntimeState.allows, head, opening, Payload.event?, decide_eq_true_eq]
    exact inside
  have active : original.application.current.excludedCall message.payload.packet.call = false := by
    rw [opening]
    change (graph.actor? event).any
      (fun who => decide (who ∈ original.application.current.excluded)) = false
    rw [request.2.2.2.1, Option.any_some]
    exact decide_eq_false request.2.2.2.2
  have admitted : (message.payload.tokenValid original.application.attempt &&
      original.application.allows message.payload.packet.call &&
      !original.application.current.excludedCall message.payload.packet.call) = true := by
    rw [token, allowed, active]
    rfl
  exact frame.opening_inclusion onlyBindings message.id message found event candidate actor payload
    binding checks outputEq codeEq node request.2.2.1 timely sender owned associated value fixed
    imageFixed stored imageStored result resolved message.payload.packet.evidence packet admitted
      clear

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
