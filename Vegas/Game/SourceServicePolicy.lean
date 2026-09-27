/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceInformation
import Vegas.Pending.ReactiveCompiledMenu
import Vegas.Compile.EventGraphPolicyLaw

/-! # Source decisions in the existing sequential native service

The physical policy reads the existing compiler's policy table at the granted
event. Binding choices are atomic submissions; ineffective disclosures and
withholding are settled by silence and expiry. The correspondence below permits
arbitrary outstanding source guards and does not freeze the candidate catalogue
or accepted handles at initialization.

These are actual response-law equalities. Finite-menu coverage, complete service
execution, and sequential rationality require separate proofs. In particular,
erasing an ineffective private disclosure intention uses the checked source
normalization argument, not an equality of private action histories.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The source compiler's decision at the granted event, represented by one
actual native response. This definition introduces neither strategy memory nor
an additional runtime step. -/
def sourceServicePolicy (profile : BehavioralProfile setup.program) (who : Player) :
    (application setup leaks).Policy := fun past view =>
  if identity : view.application.who = who then
    match view.application.publicView.serviceGrant with
    | none => FinDist.pure ⟨none⟩
    | some event =>
        if owned : (graph setup).actor? event = some who then
          ((compileEventProfile setup.program profile) who event owned
            (setup.eventGraph.fromModeObservation .sequential who
              (identity ▸ view.application.observation))).map
            ((runtime setup).serviceDecision leaks who past view event)
        else FinDist.pure ⟨none⟩
  else FinDist.pure ⟨none⟩

theorem sourceServicePolicy_at_event (profile : BehavioralProfile setup.program)
    (who : Player) (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId)
    (granted : execution.application.serviceGrant = some event)
    (owned : (graph setup).actor? event = some who) :
    sourceServicePolicy setup leaks profile who (execution.recall who)
        (execution.observe (application setup leaks) who) =
      ((compileEventProfile setup.program profile) who event owned
        (setup.eventGraph.fromModeObservation .sequential who
          ((graph setup).playerObserve who execution.application.config))).map
        ((runtime setup).serviceDecision leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) event) := by
  unfold sourceServicePolicy
  rw [dite_eq_left (show (execution.observe (application setup leaks) who).application.who = who
    from rfl)]
  change (match execution.application.serviceGrant with
    | none => _
    | some selected => _) = _
  simp only [granted, dite_eq_left owned]
  rfl

private theorem eq_map_cast_of_cast_eq {A B : Type} (same : A = B)
    (left : FinDist A) (right : FinDist B)
    (equal : cast (congrArg FinDist same) left = right) :
    left = right.map (cast same.symm) := by
  cases same
  change left = right.map id
  rw [FinDist.map_id]
  exact equal

/-- The local source commitment distribution is retained exactly, including
its dependence on the owner's initial type and complete source recall. -/
theorem sourceServicePolicy_commit {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (granted : execution.application.serviceGrant =
      some (embedding.event ⟨0, by simp [eventCount]⟩)) :
    let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : (graph setup).outputLayout (embedding.event headIndex) =
        .binding owner payload := by
      change outputLayout setup.program (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    sourceServicePolicy setup leaks wholeProfile owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) =
      (commitKernel profile (source.view owner)).map fun binding =>
        (runtime setup).serviceDecision leaks owner (execution.recall owner)
          (execution.observe (application setup leaks) owner) (embedding.event headIndex)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) binding) := by
  dsimp only
  let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let event := embedding.event headIndex
  have actor : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, headIndex, eventOwner?, eventCount] using aligned.actorEq headIndex
  rw [sourceServicePolicy_at_event setup leaks wholeProfile owner execution event granted actor]
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
  change _ = compilePolicyTable (.commit name owner fresh guard next) refs embedding.ref
    owner (profile owner) ⟨0, by simp [eventCount]⟩
      ((graph setup).playerStore owner execution.application.config.store)
      (source.history owner) at law
  rw [compilePolicyTable_commit_of_decode refs embedding.ref (profile owner) rfl _ _
    (sourceObserve owner source.state) decoded] at law
  have actionLaw := eq_map_cast_of_cast_eq
    (congrArg EventGraph.EventField.Action (embedding.layout_eq headIndex)) _ _ law
  rw [actionLaw, FinDist.map_comp]
  rfl

/-- Outstanding deferred obligations do not change how the source disclosure
policy is read. They are evaluated by the existing physical decision function. -/
theorem sourceServicePolicy_reveal {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.reveal published owner name fresh selected unresolved next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh selected unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.reveal published owner name fresh selected unresolved next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) = source.history)
    (granted : execution.application.serviceGrant =
      some (embedding.event ⟨0, by simp [eventCount]⟩)) :
    let headIndex : Fin (eventCount
      (.reveal published owner name fresh selected unresolved next)) := ⟨0, by simp [eventCount]⟩
    let outputEq : (graph setup).outputLayout (embedding.event headIndex) =
        .publication payload := by
      change outputLayout setup.program (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    sourceServicePolicy setup leaks wholeProfile owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) =
      (revealKernel profile (source.view owner)).map fun disclose =>
        (runtime setup).serviceDecision leaks owner (execution.recall owner)
          (execution.observe (application setup leaks) owner) (embedding.event headIndex)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) := by
  dsimp only
  let headIndex : Fin (eventCount
    (.reveal published owner name fresh selected unresolved next)) := ⟨0, by simp [eventCount]⟩
  let event := embedding.event headIndex
  have actor : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, headIndex, eventOwner?, eventCount] using aligned.actorEq headIndex
  rw [sourceServicePolicy_at_event setup leaks wholeProfile owner execution event granted actor]
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
  change _ = compilePolicyTable (.reveal published owner name fresh selected unresolved next)
    refs embedding.ref owner (profile owner) ⟨0, by simp [eventCount]⟩
      ((graph setup).playerStore owner execution.application.config.store)
      (source.history owner) at law
  rw [compilePolicyTable_reveal_of_decode refs embedding.ref (profile owner) rfl _ _
    (sourceObserve owner source.state) decoded] at law
  have actionLaw := eq_map_cast_of_cast_eq
    (congrArg EventGraph.EventField.Action (embedding.layout_eq headIndex)) _ _ law
  rw [actionLaw, FinDist.map_comp]
  rfl

end Vegas.SourceProgram.RevealService
