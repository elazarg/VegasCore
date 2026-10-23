/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowOpening
import Vegas.Pending.PhaseCountCollection
import Vegas.Pending.PhasePacketEvidence
import Vegas.Pending.PhaseBindingInvariant
import Vegas.Pending.PhaseLatestBindingHistory

/-! # Original accepted openings construct repaired accepting handlers -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Actual source acceptance supplies all native readiness, authentication
and guard facts. The successful binding refinement supplies the same actual
proposal in the repaired prefix, including a guard-failed public result. -/
theorem PhaseStateFrame.repair_opening_of_history
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (left right : (app).Control)
    (leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some left))
    (rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some right))
    {memory : BindingShadow graph} {owner : Player}
    (frame : PhaseStateFrame memory owner left.execution.application right.execution.application)
    (owned : memory.OwnBindings owner)
    (supported : memory.CompletedAt right.execution.application.current.native.config)
    (entryRef : left.execution.application.entry.native.config.store.BindingRefines
      right.execution.application.entry.native.config.store)
    (currentRef : left.execution.application.current.native.config.store.BindingRefines
      right.execution.application.current.native.config.store)
    (message : Message Player (CommitAttemptPacket graph))
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (call : message.payload.packet.call = .opening event candidate raw)
    (next : PhaseRuntimeState graph)
    (accepted : left.execution.application.handle runtime message = some next) :
    ∃ (nextMemory : BindingShadow graph) (image : PhaseRuntimeState graph),
      right.execution.application.handle runtime message = some image ∧
      nextMemory.OwnBindings owner ∧ nextMemory.candidates = memory.candidates ∧
      PhaseStateFrame nextMemory owner next image ∧
      nextMemory.CompletedAt image.current.native.config ∧
      next.entry.native.config.store.BindingRefines image.entry.native.config.store ∧
      next.current.native.config.store.BindingRefines image.current.native.config.store := by
  classical
  have admitted : (message.payload.tokenValid left.execution.application.attempt &&
      left.execution.application.allows message.payload.packet.call &&
      !left.execution.application.current.excludedCall message.payload.packet.call) = true := by
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · assumption
    · cases accepted
  have nativeAccepted : ∃ native, handle runtime left.execution.application.current.native
      ⟨message.id, .opening event candidate raw⟩ = some native := by
    unfold PhaseRuntimeState.handle at accepted
    rw [admitted] at accepted
    simp only [↓reduceIte, call, Option.map_eq_some_iff] at accepted
    obtain ⟨native, handled, _⟩ := accepted
    exact ⟨native, handled⟩
  obtain ⟨native, handled⟩ := nativeAccepted
  obtain ⟨ready, timely, actor, payload, binding, checks, outputEq, codeEq, value, result,
      node, sender, candidateOwner, associated, typed, leftFixed, leftStored, resolved,
      _nativeEq⟩ :=
    handle_opening_conditions runtime _ native message.id event candidate raw handled
  have rawLeft := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler leftTrace
  have rawRight := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler rightTrace
  have leftBinding := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler rawLeft
  have rightBinding :=
    phaseBindingRecord_history runtime leaks plan inputs horizon scheduler rawRight
  obtain ⟨rightStored, other, leftAssociated, _rightAssociated, _owner, _leftFixed,
      rightFixed⟩ := frame.successful_opening owned currentRef leftBinding.active
        rightBinding.active binding value leftStored
  have same : candidate = other := Option.some.inj (associated.symm.trans leftAssociated)
  subst other
  obtain ⟨nextMemory, first, image, firstHandled, imageHandled, nextOwned, candidates,
      paired, nextSupport, refinement⟩ :=
    frame.handle_opening owned supported runtime event actor payload binding checks outputEq
      codeEq node message candidate value (call.trans (congrArg (Payload.opening event candidate)
        typed)) admitted ready timely sender candidateOwner associated leftFixed rightFixed
          leftStored rightStored result resolved
  have sameFirst : first = next := Option.some.inj (firstHandled.symm.trans accepted)
  subst first
  exact ⟨nextMemory, image, imageHandled, nextOwned, candidates, paired, nextSupport,
    (refinement entryRef currentRef).1, (refinement entryRef currentRef).2⟩

/-- An original counted certificate also rules out a newly accepted opening
on the repaired side. This uses the original packet's authentic fixed meaning,
not the false converse of successful-store refinement. -/
theorem PhaseStateFrame.opening_acceptance_reflects
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (left : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some left))
    {memory : BindingShadow graph} {owner : Player} {right : PhaseRuntimeState graph}
    (frame : PhaseStateFrame memory owner left.execution.application right)
    (owned : memory.OwnBindings owner)
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ left.execution.network.inputs)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (call : message.payload.packet.call = .opening event candidate raw)
    (next : PhaseRuntimeState graph)
    (accepted : right.handle runtime message = some next) :
    ∃ image, left.execution.application.handle runtime message = some image := by
  classical
  have admitted : (message.payload.tokenValid right.attempt &&
      right.allows message.payload.packet.call &&
      !right.current.excludedCall message.payload.packet.call) = true := by
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · assumption
    · cases accepted
  have nativeAccepted : ∃ native, handle runtime right.current.native
      ⟨message.id, .opening event candidate raw⟩ = some native := by
    unfold PhaseRuntimeState.handle at accepted
    rw [admitted] at accepted
    simp only [↓reduceIte, call, Option.map_eq_some_iff] at accepted
    obtain ⟨native, handled, _⟩ := accepted
    exact ⟨native, handled⟩
  obtain ⟨native, handled⟩ := nativeAccepted
  obtain ⟨ready, timely, actor, payload, binding, checks, outputEq, codeEq, value, result,
      node, sender, candidateOwner, associated, typed, _rightFixed, rightStored, resolved,
      _nativeEq⟩ :=
    handle_opening_conditions runtime _ native message.id event candidate raw handled
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler trace
  have physical := PhaseCount.physicalBindings_history runtime leaks bounds plan inputs horizon
    scheduler trace
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp
    (physical.clean.2 message member)).2.1
  unfold CountCallCorrect at correct
  dsimp only [PhaseCount.nativeMessage] at correct
  rw [call] at correct
  have certificate : message.payload.packet.evidence = some ⟨candidate, raw⟩ := by
    have certified := correct.1
    unfold certifiedOpening at certified
    rw [call] at certified
    cases found : message.payload.packet.evidence with
    | none => simp only [found, Bool.false_eq_true] at certified
    | some fact =>
        simp only [found, decide_eq_true_eq] at certified
        exact congrArg some certified
  have sound := (phasePacketEvidence runtime leaks).history_sound initial horizon scheduler rawTrace
  have leftRaw := sound.inputs message member ⟨candidate, raw⟩ (by
    simp only [phasePacketEvidence, certificate, Option.toList_some, List.mem_singleton])
  change left.execution.application.current.native.candidates.lookup candidate = .openable raw
    at leftRaw
  have leftFixed : left.execution.application.current.native.candidates.lookup candidate =
      .openable ⟨payload, value⟩ := by rwa [typed] at leftRaw
  have publicEq : left.execution.application.current.native.publicView =
      right.current.native.publicView := by
    rw [frame.current]
    exact native_publicView owned _
  have leftAssociated : left.execution.application.current.native.accepted binding.field =
      some candidate := by
    have tables : left.execution.application.current.native.accepted =
        right.current.native.accepted := congrArg PublicView.accepted publicEq
    rw [tables]
    exact associated
  have invariant := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler rawTrace
  have leftStored :=
    invariant.active.opening_stored binding candidate value leftAssociated leftFixed
  obtain ⟨leftReady, leftTimely, _associated, leftResolved⟩ :=
    opening_right_facts runtime right.current.native left.execution.application.current.native
      publicEq.symm event actor payload binding checks candidate ready timely associated value
        rightStored leftStored result resolved
  have leftHandled := handle_opening_eq runtime left.execution.application.current.native
    message.id event candidate actor payload binding checks outputEq codeEq node leftReady
      leftTimely sender candidateOwner leftAssociated value leftFixed leftStored result leftResolved
  have attempts : left.execution.application.attempt = right.attempt := by
    simp only [PhaseRuntimeState.attempt, frame.phases, frame.generation]
  have allows : left.execution.application.allows message.payload.packet.call =
      right.allows message.payload.packet.call := by
    simp only [PhaseRuntimeState.allows, frame.phases]
  have excluded : left.execution.application.current.excludedCall message.payload.packet.call =
      right.current.excludedCall message.payload.packet.call := by rw [frame.current]; rfl
  have leftAdmitted : (message.payload.tokenValid left.execution.application.attempt &&
      left.execution.application.allows message.payload.packet.call &&
      !left.execution.application.current.excludedCall message.payload.packet.call) = true := by
    rw [attempts, allows, excluded]
    exact admitted
  unfold PhaseRuntimeState.handle
  rw [leftAdmitted]
  simp only [↓reduceIte, call, typed, leftHandled, Option.map_some]
  exact ⟨_, rfl⟩

end Vegas.EventGraphRuntime.BindingShadow
