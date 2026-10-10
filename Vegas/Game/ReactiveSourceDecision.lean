/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveIntentionRecall
import Vegas.Compile.EventGraphPolicyLaw

/-! # Source decision kernels with reconstructed original own recall

At a compiled source suffix, actual semantic store agreement decodes every
private and public source observation. The reactive sampler then uses the
source policy with its complete memory-reconstructed original action list.
No equality between source histories and physical expiry actions is assumed.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Decode the original own actions retained by the reactive implementation.
The actual player observation supplies their order and private visible store;
only authenticated original resolution intentions replace expiry actions. -/
def originalReactiveSourceRecall {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (runtime : EventGraphRuntime (toEventGraph whole))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))
    (who : Player) (execution : (runtime.reactiveApplication leaks).Execution)
    (intentions : List (Option (toEventGraph whole).Completion)) :
    List (OwnAction Player L) :=
  decodeCompletions whole (((toEventGraph whole).ownCompletions who
    execution.application.config.history).map
      (runtime.reactiveOriginal leaks who (execution.recall who) intentions execution.receipts))

/-- The actual prescribed commit response samples exactly the source decision
kernel at the decoded visible state and full reconstructed original own recall. -/
theorem prescribedReactiveResponse_source_commit
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (runtime : EventGraphRuntime (toEventGraph whole))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (wholeProfile : BehavioralProfile whole)
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout whole) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) (.commit name owner
      fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix whole wholeProfile (.commit name owner fresh guard next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (intentions : List (Option (toEventGraph whole).Completion))
    (agree : refs.Agrees source.state execution.application.config.store)
    (turn : execution.application.publicView.ownTurn? owner =
      some (embedding.event ⟨0, by simp [eventCount]⟩))
    (unsubmitted : runtime.reactiveAlreadySubmitted leaks (execution.recall owner)
      (embedding.event ⟨0, by simp [eventCount]⟩) = false)
    (undecided : runtime.reactiveAlreadyDecided leaks owner (execution.recall owner) intentions
      (embedding.event ⟨0, by simp [eventCount]⟩) = false) :
    let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : (toEventGraph whole).outputLayout (embedding.event headIndex) = .binding
      owner payload := by
      change outputLayout whole (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    runtime.prescribedReactiveResponse leaks owner ((compileEventProfile whole wholeProfile) owner)
      (execution.recall owner) intentions
      (execution.observe (runtime.reactiveApplication leaks) owner) =
      (commitKernel profile (sourceObserve owner source.state,
        originalReactiveSourceRecall whole runtime leaks owner execution intentions)).map
          fun binding =>
            let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) binding
            (runtime.reactiveDecision leaks owner (embedding.event headIndex) action
              (execution.observe (runtime.reactiveApplication leaks) owner).application,
              some (⟨embedding.event headIndex, action⟩ : (toEventGraph whole).Completion)) := by
  dsimp only
  let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let event := embedding.event headIndex
  have actor : (toEventGraph whole).actor? event = some owner := by
    simpa [event, headIndex, eventOwner?, eventCount] using aligned.actorEq headIndex
  let view := execution.observe (runtime.reactiveApplication leaks) owner
  have identity : view.application.who = owner := rfl
  have ready : view.application.publicView.EventReady event :=
    (view.application.publicView.ownTurn?_spec owner event turn).1
  let observation := (toEventGraph whole).normalizeObservation event owner
    { (toEventGraph whole).playerObserve owner execution.application.config with
      ownActions := ((toEventGraph whole).ownCompletions owner
        execution.application.config.history).map
          (runtime.reactiveOriginal leaks owner (execution.recall owner) intentions
            execution.receipts) }
  have law := aligned.policyEq owner headIndex actor observation
  have decoded := decodeObservation?_playerStore_eq_some (graph := toEventGraph whole)
    refs owner source.state
    execution.application.config.store agree
  change _ = compilePolicyTable (.commit name owner fresh guard next) refs embedding.ref owner
    (profile owner) ⟨0, by simp [eventCount]⟩
    ((toEventGraph whole).playerStore owner execution.application.config.store)
    (originalReactiveSourceRecall whole runtime leaks owner execution intentions) at law
  rw [compilePolicyTable_commit_of_decode refs embedding.ref (profile owner) rfl _ _
    (sourceObserve owner source.state) decoded] at law
  have actionLaw := eq_map_cast_of_cast_eq
    (congrArg EventGraph.EventField.Action (embedding.layout_eq headIndex)) _ _ law
  change runtime.reactiveAlreadySubmitted leaks (execution.recall owner) event =
    false at unsubmitted
  change runtime.reactiveAlreadyDecided leaks owner (execution.recall owner) intentions event =
    false at undecided
  change view.application.publicView.ownTurn? owner = some event at turn
  change runtime.prescribedReactiveResponse leaks owner
    ((compileEventProfile whole wholeProfile) owner) (execution.recall owner) intentions view = _
  simp only [prescribedReactiveResponse, turn, unsubmitted, undecided, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, identity, ready, actor, ↓reduceDIte]
  change ((compileEventProfile whole wholeProfile) owner event actor observation).map _ = _
  rw [actionLaw, PMF.map_comp]
  rfl

/-- The actual prescribed reveal response samples exactly the source decision
kernel at the decoded visible state and full reconstructed original own recall. -/
theorem prescribedReactiveResponse_source_reveal
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (runtime : EventGraphRuntime (toEventGraph whole))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile whole)
    (profile : BehavioralProfile (.reveal published owner name fresh selected unresolved next))
    (refs : ContextRefs (graphLayout whole) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) (.reveal published
      owner name fresh selected unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix whole wholeProfile (.reveal published owner name fresh
      selected unresolved next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (intentions : List (Option (toEventGraph whole).Completion))
    (agree : refs.Agrees source.state execution.application.config.store)
    (turn : execution.application.publicView.ownTurn? owner =
      some (embedding.event ⟨0, by simp [eventCount]⟩))
    (unsubmitted : runtime.reactiveAlreadySubmitted leaks (execution.recall owner)
      (embedding.event ⟨0, by simp [eventCount]⟩) = false)
    (undecided : runtime.reactiveAlreadyDecided leaks owner (execution.recall owner) intentions
      (embedding.event ⟨0, by simp [eventCount]⟩) = false) :
    let headIndex : Fin (eventCount (.reveal published owner name fresh selected unresolved
      next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : (toEventGraph whole).outputLayout (embedding.event headIndex) = .publication
      payload := by
      change outputLayout whole (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    runtime.prescribedReactiveResponse leaks owner ((compileEventProfile whole wholeProfile) owner)
      (execution.recall owner) intentions
      (execution.observe (runtime.reactiveApplication leaks) owner) =
      (revealKernel profile (sourceObserve owner source.state,
        originalReactiveSourceRecall whole runtime leaks owner execution intentions)).map
          fun disclose =>
            let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose
            (runtime.reactiveDecision leaks owner (embedding.event headIndex) action
              (execution.observe (runtime.reactiveApplication leaks) owner).application,
              some (⟨embedding.event headIndex, action⟩ : (toEventGraph whole).Completion)) := by
  dsimp only
  let headIndex : Fin (eventCount (.reveal published owner name fresh selected unresolved next)) :=
    ⟨0, by simp [eventCount]⟩
  let event := embedding.event headIndex
  have actor : (toEventGraph whole).actor? event = some owner := by
    simpa [event, headIndex, eventOwner?, eventCount] using aligned.actorEq headIndex
  let view := execution.observe (runtime.reactiveApplication leaks) owner
  have identity : view.application.who = owner := rfl
  have ready : view.application.publicView.EventReady event :=
    (view.application.publicView.ownTurn?_spec owner event turn).1
  let observation := (toEventGraph whole).normalizeObservation event owner
    { (toEventGraph whole).playerObserve owner execution.application.config with
      ownActions := ((toEventGraph whole).ownCompletions owner
        execution.application.config.history).map
          (runtime.reactiveOriginal leaks owner (execution.recall owner) intentions
            execution.receipts) }
  have law := aligned.policyEq owner headIndex actor observation
  have decoded := decodeObservation?_playerStore_eq_some (graph := toEventGraph whole)
    refs owner source.state
    execution.application.config.store agree
  change _ = compilePolicyTable (.reveal published owner name fresh selected unresolved next)
    refs embedding.ref owner
    (profile owner) ⟨0, by simp [eventCount]⟩
    ((toEventGraph whole).playerStore owner execution.application.config.store)
    (originalReactiveSourceRecall whole runtime leaks owner execution intentions) at law
  rw [compilePolicyTable_reveal_of_decode refs embedding.ref (profile owner) rfl _ _
    (sourceObserve owner source.state) decoded] at law
  have actionLaw := eq_map_cast_of_cast_eq
    (congrArg EventGraph.EventField.Action (embedding.layout_eq headIndex)) _ _ law
  change runtime.reactiveAlreadySubmitted leaks (execution.recall owner) event =
    false at unsubmitted
  change runtime.reactiveAlreadyDecided leaks owner (execution.recall owner) intentions event =
    false at undecided
  change view.application.publicView.ownTurn? owner = some event at turn
  change runtime.prescribedReactiveResponse leaks owner
    ((compileEventProfile whole wholeProfile) owner) (execution.recall owner) intentions view = _
  simp only [prescribedReactiveResponse, turn, unsubmitted, undecided, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte, identity, ready, actor, ↓reduceDIte]
  change ((compileEventProfile whole wholeProfile) owner event actor observation).map _ = _
  rw [actionLaw, PMF.map_comp]
  rfl

end Vegas
