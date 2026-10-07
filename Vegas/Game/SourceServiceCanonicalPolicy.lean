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

section Configured

variable (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The source compiler's decision at the player's turn, realized by the
canonical decision. -/
def serviceCanonicalPolicy (profile : BehavioralProfile setup.program) (who : Player) :
    (serviceApplication setup mode deadline leaks).Policy := fun past view =>
  if identity : view.application.who = who then
    match view.application.publicView.ownTurn? who with
    | none => PMF.pure ⟨none⟩
    | some event =>
        if owned : (serviceGraph setup mode).actor? event = some who then
          ((compileEventProfile setup.program profile) who event owned
            (setup.eventGraph.fromModeObservation mode who
              (identity ▸ view.application.observation))).map
            ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks who past view
              event)
        else PMF.pure ⟨none⟩
  else PMF.pure ⟨none⟩

/-- One opportunity of the turn-counted policy: silence once the event is
recorded in the owner's recall or once a fresh call could no longer be
included before the deadline within `bound event` slots; otherwise make the
canonical source decision, retaining silence if it emits nothing. -/
def serviceCanonicalOpportunity (bound : (serviceGraph setup mode).EventId → Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (event : (serviceGraph setup mode).EventId) :
    (serviceApplication setup mode deadline leaks).Policy := fun past view =>
  if (serviceRuntime setup mode deadline).eventRecorded leaks past event then
    (serviceApplication setup mode deadline leaks).silentPolicy past view
  else if view.application.publicView.InclusionFitsDeadline (serviceRuntime setup mode deadline)
      bound event then
    (serviceCanonicalPolicy setup mode deadline leaks profile who past view).bind fun response =>
      if response.transmission = none then
        (serviceApplication setup mode deadline leaks).silentPolicy past view
      else PMF.pure response
  else (serviceApplication setup mode deadline leaks).silentPolicy past view

end Configured

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The canonical source decision on the default runtime. -/
abbrev sourceServiceCanonicalPolicy : BehavioralProfile setup.program → Player →
    (application setup leaks).Policy :=
  serviceCanonicalPolicy setup .sequential (rankDeadline setup .sequential) leaks

/-- One opportunity of the turn-counted policy on the default runtime. -/
abbrev sourceServiceCanonicalOpportunity : ((graph setup).EventId → Nat) →
    BehavioralProfile setup.program → Player → (graph setup).EventId →
      (application setup leaks).Policy :=
  serviceCanonicalOpportunity setup .sequential (rankDeadline setup .sequential) leaks

section Generic

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

theorem sourceServiceCanonicalPolicy_at_event (profile : BehavioralProfile setup.program)
    (who : Player) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (event : (serviceGraph setup mode).EventId)
    (selected : execution.application.publicView.ownTurn? who = some event)
    (owned : (serviceGraph setup mode).actor? event = some who) :
    serviceCanonicalPolicy setup mode deadline leaks profile who (execution.recall who)
        (execution.observe (serviceApplication setup mode deadline leaks) who) =
      ((compileEventProfile setup.program profile) who event owned
        (setup.eventGraph.fromModeObservation mode who
          ((serviceGraph setup mode).playerObserve who execution.application.config))).map
        ((serviceRuntime setup mode deadline).canonicalServiceDecision leaks who
            (execution.recall who)
          (execution.observe (serviceApplication setup mode deadline leaks) who) event) := by
  unfold serviceCanonicalPolicy
  rw [dite_eq_left
          (show (execution.observe (serviceApplication setup mode deadline leaks)
          who).application.who = who from rfl)]
  have turn :
      (execution.observe (serviceApplication setup mode deadline leaks)
          who).application.publicView.ownTurn? who = some event := selected
  rw [turn]
  simp only [dite_eq_left owned]
  rfl

/-- **The local source commitment distribution, from the owner's observation.**
At the owner's turn at the commitment, the canonical decision follows the
source commitment kernel of any source configuration whose owner-visible part
the native store decodes to and whose owner history the native own completions
decode to. Fields the owner cannot see, such as other players' commitments, are
not consulted. -/
theorem serviceCanonicalPolicy_commit_of_observation {Γ : SourceCtx Player L}
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
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (decoded : decodeObservation? owner refs
      ((serviceGraph setup mode).playerStore owner execution.application.config.store) =
        some (sourceObserve owner source.state))
    (ownHistory : decodeCompletions setup.program
      (((serviceGraph setup mode).ownCompletions owner execution.application.config.history).map
        (setup.eventGraph.fromModeCompletion mode)) = source.history owner)
    (turn : execution.application.publicView.ownTurn? owner =
      some (embedding.event ⟨0, by simp [eventCount]⟩)) :
    let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : (serviceGraph setup mode).outputLayout (embedding.event headIndex) =
        .binding owner payload := by
      change outputLayout setup.program (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    serviceCanonicalPolicy setup mode deadline leaks wholeProfile owner (execution.recall owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      (commitKernel profile (source.view owner)).map fun binding =>
        (serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner
        (execution.recall owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner)
        (embedding.event headIndex)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) binding) := by
  dsimp only
  let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let event := embedding.event headIndex
  have actor : (serviceGraph setup mode).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, headIndex, eventOwner?, eventCount] using aligned.actorEq headIndex
  rw [sourceServiceCanonicalPolicy_at_event setup leaks wholeProfile owner execution event
    turn actor]
  let observation := setup.eventGraph.fromModeObservation mode owner
    ((serviceGraph setup mode).playerObserve owner execution.application.config)
  have law := aligned.policyEq owner headIndex actor observation
  have observed : decodeCompletions setup.program observation.ownActions =
      source.history owner := ownHistory
  rw [observed] at law
  change _ = compilePolicyTable (.commit name owner fresh guard next) refs embedding.ref
    owner (profile owner) ⟨0, by simp [eventCount]⟩
      ((serviceGraph setup mode).playerStore owner execution.application.config.store)
      (source.history owner) at law
  rw [compilePolicyTable_commit_of_decode refs embedding.ref (profile owner) rfl _ _
    (sourceObserve owner source.state) decoded] at law
  have actionLaw := eq_map_cast_of_cast_eq
    (congrArg EventGraph.EventField.Action (embedding.layout_eq headIndex)) _ _ law
  rw [actionLaw, PMF.map_comp]
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
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion mode)) = source.history)
    (ready : execution.application.config.cut.Ready
      (embedding.event ⟨0, by simp [eventCount]⟩)) :
    let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : (serviceGraph setup mode).outputLayout (embedding.event headIndex) =
        .binding owner payload := by
      change outputLayout setup.program (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    serviceCanonicalPolicy setup mode deadline leaks wholeProfile owner (execution.recall owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      (commitKernel profile (source.view owner)).map fun binding =>
        (serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner
        (execution.recall owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner)
        (embedding.event headIndex)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) binding) := by
  have actor : (serviceGraph setup mode).actor? (embedding.event ⟨0, by simp [eventCount]⟩) =
      some owner := by
    change (toEventGraph setup.program).actor? _ = some owner
    simpa [eventOwner?, eventCount] using aligned.actorEq ⟨0, by simp [eventCount]⟩
  refine serviceCanonicalPolicy_commit_of_observation setup leaks fresh guard next wholeProfile
    profile refs source embedding refsBefore offset aligned execution
    (decodeObservation?_playerStore_eq_some (graph := serviceGraph setup mode) refs owner
      source.state execution.application.config.store agree) ?_
    (serviceOwnTurn?_of_ready setup execution.application ready actor)
  rw [ownCompletions_fromModeCompletion]
  exact congrFun history owner

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
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion mode)) = source.history)
    (ready : execution.application.config.cut.Ready
      (embedding.event ⟨0, by simp [eventCount]⟩)) :
    let headIndex : Fin (eventCount
      (.reveal published owner name fresh selected unresolved next)) := ⟨0, by simp [eventCount]⟩
    let outputEq : (serviceGraph setup mode).outputLayout (embedding.event headIndex) =
        .publication payload := by
      change outputLayout setup.program (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    serviceCanonicalPolicy setup mode deadline leaks wholeProfile owner (execution.recall owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      (revealKernel profile (source.view owner)).map fun disclose =>
        (serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner
        (execution.recall owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner)
        (embedding.event headIndex)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) := by
  dsimp only
  let headIndex : Fin (eventCount
    (.reveal published owner name fresh selected unresolved next)) := ⟨0, by simp [eventCount]⟩
  let event := embedding.event headIndex
  have actor : (serviceGraph setup mode).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, headIndex, eventOwner?, eventCount] using aligned.actorEq headIndex
  rw [sourceServiceCanonicalPolicy_at_event setup leaks wholeProfile owner execution event
    (serviceOwnTurn?_of_ready setup execution.application ready actor) actor]
  let observation := setup.eventGraph.fromModeObservation mode owner
    ((serviceGraph setup mode).playerObserve owner execution.application.config)
  have law := aligned.policyEq owner headIndex actor observation
  have ownHistory : decodeCompletions setup.program observation.ownActions =
      source.history owner := by
    change decodeCompletions setup.program
      (((serviceGraph setup mode).ownCompletions owner execution.application.config.history).map
        (setup.eventGraph.fromModeCompletion mode)) = _
    rw [ownCompletions_fromModeCompletion]
    exact congrFun history owner
  rw [ownHistory] at law
  have decoded := decodeObservation?_playerStore_eq_some (graph := serviceGraph setup mode)
    refs owner source.state execution.application.config.store agree
  change _ = compilePolicyTable (.reveal published owner name fresh selected unresolved next)
    refs embedding.ref owner (profile owner) ⟨0, by simp [eventCount]⟩
      ((serviceGraph setup mode).playerStore owner execution.application.config.store)
      (source.history owner) at law
  rw [compilePolicyTable_reveal_of_decode refs embedding.ref (profile owner) rfl _ _
    (sourceObserve owner source.state) decoded] at law
  have actionLaw := eq_map_cast_of_cast_eq
    (congrArg EventGraph.EventField.Action (embedding.layout_eq headIndex)) _ _ law
  rw [actionLaw, PMF.map_comp]
  rfl


theorem sourceServiceCanonicalPolicy_finiteSupport (finite : setup.program.FiniteBindingTypes)
    (profile : BehavioralProfile setup.program) (who : Player) :
    ReactiveApplication.Policy.FiniteSupport _
      (serviceCanonicalPolicy setup mode deadline leaks profile who) := by
  intro past view
  have finiteActions := Vegas.toEventGraph_finiteActions setup.program finite
  unfold serviceCanonicalPolicy
  split
  · split
    · simp
    · split
      · rw [PMF.support_map]
        exact ((Set.finite_univ_iff.mpr (finiteActions _)).subset (Set.subset_univ _)).image _
      · simp
  · simp

theorem sourceServiceCanonicalOpportunity_finiteSupport
    (bound : (serviceGraph setup mode).EventId → Nat) (finite : setup.program.FiniteBindingTypes)
    (profile : BehavioralProfile setup.program) (who : Player)
    (event : (serviceGraph setup mode).EventId) : ReactiveApplication.Policy.FiniteSupport _
      (serviceCanonicalOpportunity setup mode deadline leaks bound profile who event) := by
  intro past view
  unfold serviceCanonicalOpportunity
  split
  · exact (serviceApplication setup mode deadline leaks).silentPolicy_finiteSupport past view
  · split
    · refine bind_support_finite
        (sourceServiceCanonicalPolicy_finiteSupport setup leaks finite profile who past view)
        fun response _ => ?_
      split
      · exact (serviceApplication setup mode deadline leaks).silentPolicy_finiteSupport past view
      · simp
    · exact (serviceApplication setup mode deadline leaks).silentPolicy_finiteSupport past view

end Generic

end Vegas
