/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalShadowNormalization
import Vegas.Pending.PhaseBindingAdmittedInclude

/-! # Truthful opening handlers under general recovery shadows

An unchanged successful binding supplies the actual typed proposal. Public
guard evaluation is retained, including rejection and immediate exclusion.
The resulting native pair is passed through the actual dynamic normalizer.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Refinement plus the two factual binding invariants determines the same
accepted handle and its successful private meaning. -/
theorem PhaseStateFrame.successful_opening {memory : BindingShadow graph} {owner : Player}
    {original repaired : PhaseRuntimeState graph}
    (frame : PhaseStateFrame memory owner original repaired)
    (onlyBindings : memory.OwnBindings owner)
    (preserved : original.current.native.config.store.BindingRefines
      repaired.current.native.config.store)
    (leftBinding : original.current.native.BindingInvariant)
    (rightBinding : repaired.current.native.BindingInvariant)
    {actor : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding actor payload)) (value : L.Val payload)
    (successful : binding.get? original.current.native.config.store = some (.success value)) :
    binding.get? repaired.current.native.config.store = some (.success value) ∧
      ∃ candidate, original.current.native.accepted binding.field = some candidate ∧
        repaired.current.native.accepted binding.field = some candidate ∧ candidate.1 = actor ∧
        original.current.native.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
        repaired.current.native.candidates.lookup candidate = .openable ⟨payload, value⟩ := by
  have sameValue := Store.BindingRefines.success preserved binding value successful
  obtain ⟨candidate, associated, owned, fixed⟩ :=
    leftBinding.success_provenance binding value successful
  obtain ⟨other, rightAssociated, _, rightFixed⟩ :=
    rightBinding.success_provenance binding value sameValue
  have publicEq : original.current.native.publicView = repaired.current.native.publicView := by
    rw [frame.current]
    exact native_publicView onlyBindings _
  have accepted := congrArg PublicView.accepted publicEq
  have same : candidate = other := Option.some.inj
    (associated.symm.trans ((congrFun accepted binding.field).trans rightAssociated))
  subst other
  exact ⟨sameValue, candidate, associated, rightAssociated, owned, fixed, rightFixed⟩

/-- Both actual phase handlers accept the same truthful packet. The common
deferred result may be failure; its permanent exclusion and all automatic
recovery are derived on both sides without a survival assumption. -/
theorem PhaseStateFrame.handle_opening {memory : BindingShadow graph} {owner : Player}
    {original repaired : PhaseRuntimeState graph}
    (frame : PhaseStateFrame memory owner original repaired)
    (onlyBindings : memory.OwnBindings owner)
    (supported : memory.CompletedAt repaired.current.native.config)
    (runtime : EventGraphRuntime graph) (event : graph.EventId)
    (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (message : Message Player (CommitAttemptPacket graph)) (candidate : Handle graph)
    (value : L.Val payload)
    (call : message.payload.packet.call = .opening event candidate ⟨payload, value⟩)
    (admitted : (message.payload.tokenValid original.attempt &&
      original.allows message.payload.packet.call &&
      !original.current.excludedCall message.payload.packet.call) = true)
    (ready : original.current.native.config.cut.Ready event)
    (timely : original.current.native.WithinDeadline runtime event)
    (sender : message.id.1 = actor) (candidateOwner : candidate.1 = actor)
    (associated : original.current.native.accepted binding.field = some candidate)
    (leftFixed : original.current.native.candidates.lookup candidate =
      .openable ⟨payload, value⟩)
    (rightFixed : repaired.current.native.candidates.lookup candidate =
      .openable ⟨payload, value⟩)
    (leftStored : binding.get? original.current.native.config.store = some (.success value))
    (rightStored : binding.get? repaired.current.native.config.store = some (.success value))
    (result : PublicationResult (L.Val payload))
    (resolved : EventCode.resolveOutput? binding checks true
      original.current.native.config.store = some result) :
    ∃ (next : BindingShadow graph) (first second : PhaseRuntimeState graph),
      original.handle runtime message = some first ∧
      repaired.handle runtime message = some second ∧
      next.OwnBindings owner ∧ next.candidates = memory.candidates ∧
      PhaseStateFrame next owner first second ∧
      next.CompletedAt second.current.native.config ∧
      (original.entry.native.config.store.BindingRefines repaired.entry.native.config.store →
        original.current.native.config.store.BindingRefines repaired.current.native.config.store →
        first.entry.native.config.store.BindingRefines second.entry.native.config.store ∧
        first.current.native.config.store.BindingRefines second.current.native.config.store) := by
  classical
  have publicEq : original.current.native.publicView = repaired.current.native.publicView := by
    rw [frame.current]
    exact native_publicView onlyBindings _
  obtain ⟨rightReady, rightTimely, rightAssociated, rightResolved⟩ :=
    opening_right_facts runtime original.current.native repaired.current.native publicEq event actor
      payload binding checks candidate ready timely associated value leftStored rightStored
        result resolved
  let action : graph.Action event := cast (congrArg EventField.Action outputEq.symm) true
  let output : (graph.outputLayout event).Value :=
    cast (congrArg EventField.Value outputEq.symm) result
  let firstNative := original.current.native.complete event ready action output
  let secondNative := repaired.current.native.complete event rightReady action output
  have firstHandled : handle runtime original.current.native
      ⟨message.id, message.payload.packet.call⟩ = some firstNative := by
    rw [call]
    exact handle_opening_eq runtime original.current.native message.id event candidate actor
      payload binding checks outputEq codeEq node ready timely sender candidateOwner associated
        value leftFixed leftStored result resolved
  have secondHandled : handle runtime repaired.current.native
      ⟨message.id, message.payload.packet.call⟩ = some secondNative := by
    rw [call]
    exact handle_opening_eq runtime repaired.current.native message.id event candidate actor
      payload binding checks outputEq codeEq node rightReady rightTimely sender candidateOwner
        rightAssociated value rightFixed rightStored result rightResolved
  have visible : (graph.outputLayout event).IsPublic := by rw [outputEq]; trivial
  have remembered : memory.native owner secondNative = firstNative := by
    dsimp only [firstNative, secondNative]
    rw [native_complete_unmodified memory owner repaired.current.native event rightReady
      (onlyBindings.public_value_none (.inr event) visible)
      (onlyBindings.public_action_none event visible)]
    have nativeEq : original.current.native = memory.native owner repaired.current.native := by
      rw [frame.current]
      rfl
    have atReady :
        (⟨memory.native owner repaired.current.native, rightReady⟩ :
          { state : State graph // state.config.cut.Ready event }) =
        ⟨original.current.native, ready⟩ := Subtype.ext nativeEq.symm
    exact congrArg (fun state : { state : State graph // state.config.cut.Ready event } =>
      state.val.complete event state.property action output) atReady
  have nativePublic : firstNative.publicView = secondNative.publicView := by
    rw [← remembered]
    exact native_publicView onlyBindings _
  have excludedEq : original.current.excluded = repaired.current.excluded := by
    rw [frame.current]
    rfl
  have exclusions := PhaseBindingRepair.inclusion_exclusion_congr original.current
    repaired.current excludedEq firstNative secondNative nativePublic message.payload.packet.call
  let firstRaw : PhaseRuntimeState graph :=
    { original with
      current := original.current.inclusionResult message.payload.packet.call firstNative }
  let secondRaw : PhaseRuntimeState graph :=
    { repaired with
      current := repaired.current.inclusionResult message.payload.packet.call secondNative }
  have rawFrame : PhaseStateFrame memory owner firstRaw secondRaw := by
    refine ⟨frame.phases, frame.generation, frame.entry, ?_, frame.retired⟩
    exact congrArg₂ RecoveryState.mk remembered.symm exclusions
  have rawSupport : memory.CompletedAt secondRaw.current.native.config :=
    supported.complete event rightReady action output
  obtain ⟨next, nextOwned, candidates, nextFrame, nextSupport, refineStores⟩ :=
    rawFrame.normalize onlyBindings rawSupport
  have rawRefinement
      (preserved : original.current.native.config.store.BindingRefines
        repaired.current.native.config.store) :
      firstRaw.current.native.config.store.BindingRefines
        secondRaw.current.native.config.store := by
    apply Config.bindingRefines_complete preserved event ready rightReady action action
      output output
    exact EventField.BindingRefines.cast_some outputEq.symm (by trivial)
  have attempts : original.attempt = repaired.attempt := by
    simp only [PhaseRuntimeState.attempt, frame.phases, frame.generation]
  have allows : original.allows message.payload.packet.call =
      repaired.allows message.payload.packet.call := by
    simp only [PhaseRuntimeState.allows, frame.phases]
  have excluded : original.current.excludedCall message.payload.packet.call =
      repaired.current.excludedCall message.payload.packet.call := by rw [frame.current]; rfl
  have rightAdmitted : (message.payload.tokenValid repaired.attempt &&
      repaired.allows message.payload.packet.call &&
      !repaired.current.excludedCall message.payload.packet.call) = true := by
    rwa [attempts, allows, excluded] at admitted
  refine ⟨next, firstRaw.normalize, secondRaw.normalize, ?_, ?_, nextOwned, candidates,
    nextFrame, nextSupport, ?_⟩
  · simp only [PhaseRuntimeState.handle, admitted, ↓reduceIte, firstHandled, Option.map_some]
    rfl
  · simp only [PhaseRuntimeState.handle, rightAdmitted, ↓reduceIte, secondHandled, Option.map_some]
    rfl
  · intro entryRef currentRef
    exact refineStores entryRef (rawRefinement currentRef)

end Vegas.EventGraphRuntime.BindingShadow
