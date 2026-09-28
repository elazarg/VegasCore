/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePolicy
import Vegas.Game.RevealServiceState
import Vegas.Compile.EventGraphPolicyLaw

/-! # Source suffixes at actual native revelation checkpoints

The proofs reuse the compiler's suffix alignment and the actual native policy.
In particular, source-policy probabilities are read from the source observation
recovered from the current store and completed own actions. No native optimality
or source-to-native assessment correspondence is assumed.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The compiled head of a guard-free source suffix is the actual native
resolution node, with no outstanding deferred checks. -/
theorem reveal_head_code {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (refs : ContextRefs (graphLayout setup.program) Γ) (revelations : Revelations Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh selected unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (suffix : CompiledSuffix setup.program
      (.reveal published owner name fresh selected unresolved next) refs revelations []
      embedding refsBefore offset) :
    let headIndex : Fin (eventCount
      (.reveal published owner name fresh selected unresolved next)) := ⟨0, by simp [eventCount]⟩
    let event := embedding.event headIndex
    let outputEq : (graph setup).outputLayout event = .publication payload := by
      change outputLayout setup.program (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [] := by
  dsimp only
  change cast (congrArg (EventGraph.EventCode (graphLayout setup.program))
      (embedding.layout_eq ⟨0, by simp [eventCount]⟩))
    ((toEventGraph setup.program).nodes (embedding.event ⟨0, by simp [eventCount]⟩)) = _
  exact suffix.nodeEq ⟨0, by simp [eventCount]⟩

/-- A checked compiler alignment makes the actual native Boolean choice law
the residual source reveal kernel, for every source profile and hidden state. -/
theorem sourceChoiceLaw_reveal {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.reveal published owner name fresh selected unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh selected unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh selected unresolved next) profile
      refs source.revelations [] embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (granted : execution.application.serviceGrant =
      some (embedding.event ⟨0, by simp [eventCount]⟩)) :
    sourceChoiceLaw setup leaks wholeProfile owner
        (execution.observe (application setup leaks) owner) =
      revealKernel profile (source.view owner) := by
  let headIndex : Fin (eventCount
    (.reveal published owner name fresh selected unresolved next)) := ⟨0, by simp [eventCount]⟩
  let event := embedding.event headIndex
  have actor : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, headIndex, eventOwner?, eventCount] using aligned.actorEq headIndex
  have outputEq : (graph setup).outputLayout event = .publication payload :=
    embedding.layout_eq headIndex
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload (refs.get selected) [] :=
    reveal_head_code setup fresh selected unresolved next refs source.revelations
      embedding refsBefore offset aligned.graphSuffix
  have node : nodeView (graph setup) event =
      .resolve owner payload (refs.get selected) [] outputEq codeEq :=
    EventGraphRuntime.nodeView_eq_resolve _ _
  rw [sourceChoiceLaw_at_reveal setup leaks wholeProfile owner execution event granted actor
    owner payload (refs.get selected) [] outputEq codeEq node]
  let observation := setup.eventGraph.fromModeObservation .sequential owner
    ((graph setup).playerObserve owner execution.application.config)
  have law := aligned.policyEq owner headIndex actor observation
  have ownHistory : decodeCompletions setup.program observation.ownActions =
      source.history owner := by
    change decodeCompletions setup.program
      (((graph setup).ownCompletions owner execution.application.config.history).map
        (setup.eventGraph.fromModeCompletion .sequential)) = _
    rw [ownCompletions_from_sequential]
    exact congrFun history owner
  rw [ownHistory] at law
  have decoded := decodeObservation?_playerStore_eq_some (graph := graph setup)
    refs owner source.state execution.application.config.store agree
  change _ = compilePolicyTable
    (.reveal published owner name fresh selected unresolved next) refs embedding.ref
      owner (profile owner) ⟨0, by simp [eventCount]⟩
        ((graph setup).playerStore owner execution.application.config.store)
        (source.history owner) at law
  rw [compilePolicyTable_reveal_of_decode refs embedding.ref (profile owner) rfl _ _
    (sourceObserve owner source.state) decoded] at law
  exact law

end Vegas
