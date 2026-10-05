/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePolicy
import Vegas.Pending.ReactiveCanonicalDecision
import Vegas.Compile.EventGraphDeviation
import Interaction.ReactiveRoundsFiniteness

/-! # Source decisions at the audit's canonical slot

`sourceServiceCanonicalPolicy` reads the source compiler's policy table at the
player's turn exactly as `sourceServicePolicy` does, and realizes the chosen
action by the canonical decision (`EventGraphRuntime.canonicalServiceDecision`),
which submits a binding at the slot the audit's conformance rule expects.

`sourceServiceCanonicalOpportunity` is one opportunity of the turn-counted
policy: it remains silent once the event is recorded in the owner's recall, and
it makes a fresh call only while a packet included within `bound event` slots
is included strictly before the event's deadline.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The source compiler's decision at the player's turn, realized by the
canonical decision. -/
def sourceServiceCanonicalPolicy (profile : BehavioralProfile setup.program) (who : Player) :
    (application setup leaks).Policy := fun past view =>
  if identity : view.application.who = who then
    match view.application.publicView.ownTurn? who with
    | none => PMF.pure ⟨none⟩
    | some event =>
        if owned : (graph setup).actor? event = some who then
          ((compileEventProfile setup.program profile) who event owned
            (setup.eventGraph.fromModeObservation .sequential who
              (identity ▸ view.application.observation))).map
            ((runtime setup).canonicalServiceDecision leaks who past view event)
        else PMF.pure ⟨none⟩
  else PMF.pure ⟨none⟩

theorem sourceServiceCanonicalPolicy_at_event (profile : BehavioralProfile setup.program)
    (who : Player) (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId)
    (selected : execution.application.publicView.ownTurn? who = some event)
    (owned : (graph setup).actor? event = some who) :
    sourceServiceCanonicalPolicy setup leaks profile who (execution.recall who)
        (execution.observe (application setup leaks) who) =
      ((compileEventProfile setup.program profile) who event owned
        (setup.eventGraph.fromModeObservation .sequential who
          ((graph setup).playerObserve who execution.application.config))).map
        ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) event) := by
  unfold sourceServiceCanonicalPolicy
  rw [dite_eq_left (show (execution.observe (application setup leaks) who).application.who = who
    from rfl)]
  change (match execution.application.publicView.ownTurn? who with
    | none => _
    | some chosen => _) = _
  simp only [selected, dite_eq_left owned]
  rfl

/-- The local source commitment distribution is retained exactly. -/
theorem sourceServiceCanonicalPolicy_commit {Γ : SourceCtx Player L}
    {openNames : Finset VarId} {name : VarId} {owner : Player} {payload : L.Ty}
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
    (ready : execution.application.config.cut.Ready
      (embedding.event ⟨0, by simp [eventCount]⟩)) :
    let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : (graph setup).outputLayout (embedding.event headIndex) =
        .binding owner payload := by
      change outputLayout setup.program (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    sourceServiceCanonicalPolicy setup leaks wholeProfile owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) =
      (commitKernel profile (source.view owner)).map fun binding =>
        (runtime setup).canonicalServiceDecision leaks owner (execution.recall owner)
          (execution.observe (application setup leaks) owner) (embedding.event headIndex)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) binding) := by
  dsimp only
  let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let event := embedding.event headIndex
  have actor : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, headIndex, eventOwner?, eventCount] using aligned.actorEq headIndex
  rw [sourceServiceCanonicalPolicy_at_event setup leaks wholeProfile owner execution event
    (ownTurn?_of_ready setup execution.application ready actor) actor]
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
  rw [actionLaw, PMF.map_comp]
  rfl

/-- The local source disclosure distribution is retained exactly. -/
theorem sourceServiceCanonicalPolicy_reveal {Γ : SourceCtx Player L}
    {openNames : Finset VarId} {published name : VarId} {owner : Player} {payload : L.Ty}
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
    (ready : execution.application.config.cut.Ready
      (embedding.event ⟨0, by simp [eventCount]⟩)) :
    let headIndex : Fin (eventCount
      (.reveal published owner name fresh selected unresolved next)) := ⟨0, by simp [eventCount]⟩
    let outputEq : (graph setup).outputLayout (embedding.event headIndex) =
        .publication payload := by
      change outputLayout setup.program (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    sourceServiceCanonicalPolicy setup leaks wholeProfile owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) =
      (revealKernel profile (source.view owner)).map fun disclose =>
        (runtime setup).canonicalServiceDecision leaks owner (execution.recall owner)
          (execution.observe (application setup leaks) owner) (embedding.event headIndex)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) := by
  dsimp only
  let headIndex : Fin (eventCount
    (.reveal published owner name fresh selected unresolved next)) := ⟨0, by simp [eventCount]⟩
  let event := embedding.event headIndex
  have actor : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, headIndex, eventOwner?, eventCount] using aligned.actorEq headIndex
  rw [sourceServiceCanonicalPolicy_at_event setup leaks wholeProfile owner execution event
    (ownTurn?_of_ready setup execution.application ready actor) actor]
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
  rw [actionLaw, PMF.map_comp]
  rfl

/-- One opportunity of the turn-counted policy: silence once the event is
recorded in the owner's recall or once a fresh call could no longer be
included before the deadline within `bound event` slots; otherwise make the
canonical source decision, retaining silence if it emits nothing. -/
def sourceServiceCanonicalOpportunity (bound : (graph setup).EventId → Nat)
    (profile : BehavioralProfile setup.program) (who : Player) (event : (graph setup).EventId) :
    (application setup leaks).Policy := fun past view =>
  if (runtime setup).eventRecorded leaks past event then
    (application setup leaks).silentPolicy past view
  else if view.application.publicView.InclusionFitsDeadline (runtime setup) bound event then
    (sourceServiceCanonicalPolicy setup leaks profile who past view).bind fun response =>
      if response.transmission = none then (application setup leaks).silentPolicy past view
      else PMF.pure response
  else (application setup leaks).silentPolicy past view

theorem sourceServiceCanonicalPolicy_finiteSupport (finite : setup.program.FiniteBindingTypes)
    (profile : BehavioralProfile setup.program) (who : Player) :
    ReactiveApplication.Policy.FiniteSupport _
      (sourceServiceCanonicalPolicy setup leaks profile who) := by
  intro past view
  have finiteActions := Vegas.toEventGraph_finiteActions setup.program finite
  unfold sourceServiceCanonicalPolicy
  split
  · split
    · simp
    · split
      · rw [PMF.support_map]
        exact ((Set.finite_univ_iff.mpr (finiteActions _)).subset (Set.subset_univ _)).image _
      · simp
  · simp

theorem sourceServiceCanonicalOpportunity_finiteSupport (bound : (graph setup).EventId → Nat)
    (finite : setup.program.FiniteBindingTypes) (profile : BehavioralProfile setup.program)
    (who : Player) (event : (graph setup).EventId) :
    ReactiveApplication.Policy.FiniteSupport _
      (sourceServiceCanonicalOpportunity setup leaks bound profile who event) := by
  intro past view
  unfold sourceServiceCanonicalOpportunity
  split
  · exact (application setup leaks).silentPolicy_finiteSupport past view
  · split
    · refine bind_support_finite
        (sourceServiceCanonicalPolicy_finiteSupport setup leaks finite profile who past view)
        fun response _ => ?_
      split
      · exact (application setup leaks).silentPolicy_finiteSupport past view
      · simp
    · exact (application setup leaks).silentPolicy_finiteSupport past view

end Vegas
