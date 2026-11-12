module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServicePolicy
public import Vegas.Pending.ReactiveCanonicalDecision
public import Vegas.Pending.ReactiveSubmissionRecall
public import Vegas.Compile.EventGraphPolicyLaw
public import Vegas.Game.SourceServiceFacts
public import GameTheoryExtensions.Math.Probability.Support

@[expose] public section

/-! # Source decisions at the audit's canonical slot

`Vegas.sourceServiceCanonicalPolicy` reads the source compiler's policy table at
the player's turn exactly as `Vegas.sourceServicePolicy` does, and realizes the
chosen action by the canonical decision
(`Vegas.EventGraphRuntime.canonicalServiceDecision`), which submits a binding at
the slot the audit's conformance rule expects.

`Vegas.serviceCanonicalOpportunity` is one opportunity of the turn-counted
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
  (duration : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- A reference graph profile's decision at the player's turn, realized by the
canonical decision. -/
def serviceReferencePolicy (reference : (serviceGraph setup mode).BehavioralProfile)
    (who : Player) : (serviceApplication setup mode duration leaks).Policy := fun past view =>
  if identity : view.application.who = who then
    match view.application.publicView.ownTurn? who with
    | none => PMF.pure ⟨none⟩
    | some event =>
        if owned : (serviceGraph setup mode).actor? event = some who then
          let observed := id
            (identity ▸ view.application.observation)
          if inactive : who ∈ observed.defaulted then PMF.pure ⟨none⟩ else
            (reference who event owned observed inactive).map
              ((canonicalServiceDecision (serviceTimeouts setup mode duration)) leaks who past view
                event)
        else PMF.pure ⟨none⟩
  else PMF.pure ⟨none⟩

/-- The source compiler's decision at the player's turn, realized by the
canonical decision. -/
def serviceCanonicalPolicy (profile : BehavioralProfile setup.program) (who : Player) :
    (serviceApplication setup mode duration leaks).Policy :=
  serviceReferencePolicy setup mode duration leaks (compileEventProfile setup.program profile) who

/-- One opportunity of a reference's turn-counted policy: silence once the event
is recorded in the owner's recall or once a fresh call could no longer be
included before the deadline within `bound event` slots; otherwise make the
reference decision, retaining silence if it emits nothing. -/
def serviceReferenceOpportunity (bound : (serviceGraph setup mode).EventId → Nat)
    (reference : (serviceGraph setup mode).BehavioralProfile) (who : Player)
    (event : (serviceGraph setup mode).EventId) :
    (serviceApplication setup mode duration leaks).Policy := fun past view =>
  if (eventRecorded (serviceTimeouts setup mode duration)) leaks past event then
    (serviceApplication setup mode duration leaks).silentPolicy past view
  else if view.application.publicView.InclusionFitsDeadline (serviceTimeouts setup mode duration)
      bound event then
    (serviceReferencePolicy setup mode duration leaks reference who past view).bind fun response =>
      if response.transmission = none then
        (serviceApplication setup mode duration leaks).silentPolicy past view
      else PMF.pure response
  else (serviceApplication setup mode duration leaks).silentPolicy past view

/-- One opportunity of the turn-counted policy of the compiled source profile. -/
def serviceCanonicalOpportunity (bound : (serviceGraph setup mode).EventId → Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (event : (serviceGraph setup mode).EventId) :
    (serviceApplication setup mode duration leaks).Policy :=
  serviceReferenceOpportunity setup mode duration leaks bound
    (compileEventProfile setup.program profile) who event

end Configured

variable (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The canonical source decision on a supplied sequential runtime. -/
abbrev sourceServiceCanonicalPolicy : BehavioralProfile setup.program → Player →
    (application setup timeouts leaks).Policy :=
  serviceCanonicalPolicy setup .sequential timeouts.duration leaks

section Generic

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- At an owned turn, the total client is silent after public default and
otherwise realizes the active compiled callback. -/
theorem sourceServiceCanonicalPolicy_at_event_reference (reference :
    (serviceGraph setup mode).BehavioralProfile)
    (who : Player) (execution : (serviceApplication setup mode duration leaks).Execution)
    (event : (serviceGraph setup mode).EventId)
    (selected : execution.application.publicView.ownTurn? who = some event)
    (owned : (serviceGraph setup mode).actor? event = some who) :
    serviceReferencePolicy setup mode duration leaks reference who (execution.logs who)
        (execution.observe (serviceApplication setup mode duration leaks) who) =
      if inactive : who ∈ execution.application.config.defaulted then PMF.pure ⟨none⟩ else
        (reference who event owned
          (id
            ((serviceGraph setup mode).playerObserve who execution.application.config))
          inactive).map
          ((canonicalServiceDecision (serviceTimeouts setup mode duration)) leaks who
            (execution.logs who)
            (execution.observe (serviceApplication setup mode duration leaks) who) event) := by
  unfold serviceReferencePolicy
  rw [dite_eq_left
          (show (execution.observe (serviceApplication setup mode duration leaks)
          who).application.who = who from rfl)]
  have turn :
      (execution.observe (serviceApplication setup mode duration leaks)
          who).application.publicView.ownTurn? who = some event := selected
  rw [turn]
  simp only [dite_eq_left owned]
  rfl

/-- At an owned turn, the total client is silent after public default and
otherwise realizes the active compiled callback. -/
theorem sourceServiceCanonicalPolicy_at_event (profile : BehavioralProfile setup.program)
    (who : Player) (execution : (serviceApplication setup mode duration leaks).Execution)
    (event : (serviceGraph setup mode).EventId)
    (selected : execution.application.publicView.ownTurn? who = some event)
    (owned : (serviceGraph setup mode).actor? event = some who) :
    serviceCanonicalPolicy setup mode duration leaks profile who (execution.logs who)
        (execution.observe (serviceApplication setup mode duration leaks) who) =
      if inactive : who ∈ execution.application.config.defaulted then PMF.pure ⟨none⟩ else
        ((compileEventProfile setup.program profile) who event owned
          (id
            ((serviceGraph setup mode).playerObserve who execution.application.config))
          inactive).map
          ((canonicalServiceDecision (serviceTimeouts setup mode duration)) leaks who
            (execution.logs who)
            (execution.observe (serviceApplication setup mode duration leaks) who) event) :=
  sourceServiceCanonicalPolicy_at_event_reference setup leaks
    (compileEventProfile setup.program profile) who execution event selected owned

/-- Every initialized actual callback at an owned ready turn is active; no
activity premise is imposed on the scheduler or source policies. -/
theorem sourceServiceCanonicalPolicy_at_event_history_reference
    (reference : (serviceGraph setup mode).BehavioralProfile) (who : Player) {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    (control : (serviceApplication setup mode duration leaks).Control)
    (trace : ((serviceApplication setup mode duration leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (event : (serviceGraph setup mode).EventId)
    (selected : control.execution.application.publicView.ownTurn? who = some event)
    (owned : (serviceGraph setup mode).actor? event = some who) :
    ∃ active : who ∉ control.execution.application.config.defaulted,
      serviceReferencePolicy setup mode duration leaks reference who (control.execution.logs who)
          (control.execution.observe (serviceApplication setup mode duration leaks) who) =
        (reference who event owned
          (id
            ((serviceGraph setup mode).playerObserve who control.execution.application.config))
          active).map
          ((canonicalServiceDecision (serviceTimeouts setup mode duration)) leaks who
            (control.execution.logs who)
            (control.execution.observe (serviceApplication setup mode duration leaks) who)
            event) := by
  have facts := legalFacts setup leaks horizon scheduler control trace
  have ready := (control.execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event selected).1
  have active := control.execution.application.active_of_ready_owned facts.quiescent ready owned
  refine ⟨active, ?_⟩
  rw [sourceServiceCanonicalPolicy_at_event_reference setup leaks reference who control.execution
    event
    selected owned, dite_eq_right active]

/-- Every initialized actual callback at an owned ready turn is active; no
activity premise is imposed on the scheduler or source policies. -/
theorem sourceServiceCanonicalPolicy_at_event_history
    (profile : BehavioralProfile setup.program) (who : Player) {horizon : Nat}
    {scheduler : (serviceApplication setup mode duration leaks).Scheduler}
    (control : (serviceApplication setup mode duration leaks).Control)
    (trace : ((serviceApplication setup mode duration leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some control))
    (event : (serviceGraph setup mode).EventId)
    (selected : control.execution.application.publicView.ownTurn? who = some event)
    (owned : (serviceGraph setup mode).actor? event = some who) :
    ∃ active : who ∉ control.execution.application.config.defaulted,
      serviceCanonicalPolicy setup mode duration leaks profile who (control.execution.logs who)
          (control.execution.observe (serviceApplication setup mode duration leaks) who) =
        ((compileEventProfile setup.program profile) who event owned
          (id
            ((serviceGraph setup mode).playerObserve who control.execution.application.config))
          active).map
          ((canonicalServiceDecision (serviceTimeouts setup mode duration)) leaks who
            (control.execution.logs who)
            (control.execution.observe (serviceApplication setup mode duration leaks) who)
            event) := by
  apply sourceServiceCanonicalPolicy_at_event_history_reference
    (reference := compileEventProfile setup.program profile) <;> assumption

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
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (decoded : decodeObservation? owner refs
      ((serviceGraph setup mode).playerStore owner execution.application.config.store) =
        some (sourceObserve owner source.state))
    (ownHistory : decodeCompletions setup.program
      ((serviceGraph setup mode).ownCompletions owner execution.application.config.history) =
        source.history owner)
    (defaults : execution.application.config.defaults = source.defaults)
    (turn : execution.application.publicView.ownTurn? owner =
      some (embedding.event ⟨0, by simp [eventCount]⟩)) :
    let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : (serviceGraph setup mode).outputLayout (embedding.event headIndex) =
        .binding owner payload := by
      change outputLayout setup.program (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    serviceCanonicalPolicy setup mode duration leaks wholeProfile owner (execution.logs owner)
        (execution.observe (serviceApplication setup mode duration leaks) owner) =
      (if inactive : owner ∈ source.defaulted then PMF.pure none
        else commitKernel profile (source.view owner) inactive).map fun binding =>
        (canonicalServiceDecision (serviceTimeouts setup mode duration)) leaks owner
        (execution.logs owner)
        (execution.observe (serviceApplication setup mode duration leaks) owner)
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
  let observation := id
    ((serviceGraph setup mode).playerObserve owner execution.application.config)
  by_cases inactive : owner ∈ source.defaulted
  · have nativeInactive : owner ∈ execution.application.config.defaulted := by
      change owner ∈ execution.application.config.defaults.defaulted
      rw [defaults]
      exact inactive
    rw [dite_eq_left nativeInactive, dite_eq_left inactive, PMF.pure_map]
    rw [(canonicalServiceDecision_defaulted (serviceTimeouts setup mode duration)) leaks owner
      (execution.logs owner)
      (execution.observe (serviceApplication setup mode duration leaks) owner) event _
      nativeInactive]
  · have nativeActive : owner ∉ execution.application.config.defaulted := by
      change owner ∉ execution.application.config.defaults.defaulted
      rw [defaults]
      exact inactive
    rw [dite_eq_right nativeActive, dite_eq_right inactive]
    have law := aligned.policyEq owner headIndex actor observation nativeActive
    have observed : decodeCompletions setup.program observation.ownActions =
        source.history owner := ownHistory
    have viewDefaults : observation.defaults = source.defaults := defaults
    rw [observed, viewDefaults] at law
    change _ = compilePolicyTable (.commit name owner fresh guard next) refs embedding.ref
      owner (profile owner) ⟨0, by simp [eventCount]⟩
        ((serviceGraph setup mode).playerStore owner execution.application.config.store)
        source.defaults (source.history owner) at law
    rw [compilePolicyTable_commit_of_decode refs embedding.ref (profile owner) rfl _ _ inactive _
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
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history) = source.history)
    (defaults : execution.application.config.defaults = source.defaults)
    (ready : execution.application.config.cut.Ready
      (embedding.event ⟨0, by simp [eventCount]⟩)) :
    let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let outputEq : (serviceGraph setup mode).outputLayout (embedding.event headIndex) =
        .binding owner payload := by
      change outputLayout setup.program (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    serviceCanonicalPolicy setup mode duration leaks wholeProfile owner (execution.logs owner)
        (execution.observe (serviceApplication setup mode duration leaks) owner) =
      (if inactive : owner ∈ source.defaulted then PMF.pure none
        else commitKernel profile (source.view owner) inactive).map fun binding =>
        (canonicalServiceDecision (serviceTimeouts setup mode duration)) leaks owner
        (execution.logs owner)
        (execution.observe (serviceApplication setup mode duration leaks) owner)
        (embedding.event headIndex)
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) binding) := by
  have actor : (serviceGraph setup mode).actor? (embedding.event ⟨0, by simp [eventCount]⟩) =
      some owner := by
    change (toEventGraph setup.program).actor? _ = some owner
    simpa [eventOwner?, eventCount] using aligned.actorEq ⟨0, by simp [eventCount]⟩
  refine serviceCanonicalPolicy_commit_of_observation setup leaks fresh guard next wholeProfile
    profile refs source embedding refsBefore offset aligned execution
    (decodeObservation?_playerStore_eq_some (graph := serviceGraph setup mode) refs owner
      source.state execution.application.config.store agree) ?_ defaults
    (serviceOwnTurn?_of_ready setup execution.application ready actor)
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
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
      (execution.application.config.history) = source.history)
    (defaults : execution.application.config.defaults = source.defaults)
    (ready : execution.application.config.cut.Ready
      (embedding.event ⟨0, by simp [eventCount]⟩)) :
    let headIndex : Fin (eventCount
      (.reveal published owner name fresh selected unresolved next)) := ⟨0, by simp [eventCount]⟩
    let outputEq : (serviceGraph setup mode).outputLayout (embedding.event headIndex) =
        .publication payload := by
      change outputLayout setup.program (embedding.event headIndex) = _
      simpa [headIndex, outputLayout, eventCount] using embedding.layout_eq headIndex
    serviceCanonicalPolicy setup mode duration leaks wholeProfile owner (execution.logs owner)
        (execution.observe (serviceApplication setup mode duration leaks) owner) =
      (if inactive : owner ∈ source.defaulted then PMF.pure false
        else revealKernel profile (source.view owner) inactive).map fun disclose =>
        (canonicalServiceDecision (serviceTimeouts setup mode duration)) leaks owner
        (execution.logs owner)
        (execution.observe (serviceApplication setup mode duration leaks) owner)
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
  let observation := id
    ((serviceGraph setup mode).playerObserve owner execution.application.config)
  by_cases inactive : owner ∈ source.defaulted
  · have nativeInactive : owner ∈ execution.application.config.defaulted := by
      change owner ∈ execution.application.config.defaults.defaulted
      rw [defaults]
      exact inactive
    rw [dite_eq_left nativeInactive, dite_eq_left inactive, PMF.pure_map]
    rw [(canonicalServiceDecision_defaulted (serviceTimeouts setup mode duration)) leaks owner
      (execution.logs owner)
      (execution.observe (serviceApplication setup mode duration leaks) owner) event _
      nativeInactive]
  · have nativeActive : owner ∉ execution.application.config.defaulted := by
      change owner ∉ execution.application.config.defaults.defaulted
      rw [defaults]
      exact inactive
    rw [dite_eq_right nativeActive, dite_eq_right inactive]
    have law := aligned.policyEq owner headIndex actor observation nativeActive
    have ownHistory : decodeCompletions setup.program observation.ownActions =
        source.history owner := by
      change decodeCompletions setup.program
        (((serviceGraph setup mode).ownCompletions owner execution.application.config.history)) = _
      exact congrFun history owner
    have viewDefaults : observation.defaults = source.defaults := defaults
    rw [ownHistory, viewDefaults] at law
    have decoded := decodeObservation?_playerStore_eq_some (graph := serviceGraph setup mode)
      refs owner source.state execution.application.config.store agree
    change _ = compilePolicyTable (.reveal published owner name fresh selected unresolved next)
      refs embedding.ref owner (profile owner) ⟨0, by simp [eventCount]⟩
        ((serviceGraph setup mode).playerStore owner execution.application.config.store)
        source.defaults (source.history owner) at law
    rw [compilePolicyTable_reveal_of_decode refs embedding.ref (profile owner) rfl _ _ inactive _
      (sourceObserve owner source.state) decoded] at law
    have actionLaw := eq_map_cast_of_cast_eq
      (congrArg EventGraph.EventField.Action (embedding.layout_eq headIndex)) _ _ law
    rw [actionLaw, PMF.map_comp]
    rfl


end Generic

end Vegas
