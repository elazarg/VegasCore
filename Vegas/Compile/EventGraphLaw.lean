/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphPolicyLaw
import Vegas.Compile.EventGraphReadout
import Vegas.Compile.EventGraphStep
import Vegas.EventGraph.CanonicalStep
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning

/-! # Exact source-order law for event-graph compilation

The proof runs the ordinary event-graph executor with the canonical public
scheduler.  Its induction invariant relates one residual source program to the
corresponding suffix of the single graph compiled from the whole program.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

omit [DecidableEq Player] in
private theorem canonical_ready_least
    {graph : Vegas.EventGraph Player L} {config : graph.Config}
    {offset : Nat} (ordered : config.cut.IsPrefix offset)
    (event : graph.EventId) (rank : event.val = offset) :
    config.cut.Ready event ∧
      ∀ other, other ∉ config.cut.completed → event.val ≤ other.val := by
  have active : offset < graph.order.eventCount := rank ▸ event.isLt
  have eventEq : event = ⟨offset, active⟩ := Fin.ext rank
  subst event
  refine ⟨ordered.ready active, ?_⟩
  intro other unfinished
  rw [ordered.2] at unfinished
  omega


private theorem commit_head_policy_eq
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (wholeProfile : BehavioralProfile whole)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {guard : SourceGuard L Γ owner name payload}
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout whole) Γ)
    (revelations : Revelations Γ) (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix whole wholeProfile (.commit name owner fresh guard next)
      profile refs revelations registry embedding refsBefore offset)
    (config : (toEventGraph whole).Config)
    (state : State L Γ) (refsAgree : refs.Agrees state config.store)
    (history : History Player L) (historyAgree : decodeHistory whole config.history = history)
    (defaults : DefaultHistory Player) (defaultsAgree : config.defaults = defaults)
    (active : owner ∉ defaults.defaulted)
    (actor : (toEventGraph whole).actor?
      (embedding.event ⟨0, Nat.zero_lt_succ (eventCount next)⟩) = some owner) :
    cast (congrArg PMF (congrArg Vegas.EventGraph.EventField.Action
      (embedding.layout_eq ⟨0, Nat.zero_lt_succ (eventCount next)⟩)))
      ((compileEventProfile whole wholeProfile) owner
        (embedding.event ⟨0, Nat.zero_lt_succ (eventCount next)⟩) actor
        ((toEventGraph whole).playerObserve owner config)
        (by simpa only [EventGraph.playerObserve_defaulted, EventGraph.Config.defaulted,
          defaultsAgree] using active)) =
      commitKernel profile ⟨sourceObserve owner state, defaults, history owner⟩ active := by
  have graphActive : owner ∉ ((toEventGraph whole).playerObserve owner config).defaulted := by
    simpa only [EventGraph.playerObserve_defaulted, EventGraph.Config.defaulted,
      defaultsAgree] using active
  have decodedObservation := decodeObservation?_playerStore_eq_some
    (graph := toEventGraph whole) refs owner state config.store refsAgree
  have policyLaw := aligned.policyEq owner ⟨0, Nat.zero_lt_succ (eventCount next)⟩ actor
    ((toEventGraph whole).playerObserve owner config) graphActive
  rw [decodeCompletions_playerObserve whole config owner, historyAgree] at policyLaw
  change _ = compilePolicyTable (.commit name owner fresh guard next) refs embedding.ref
    owner (profile owner) ⟨0, Nat.zero_lt_succ (eventCount next)⟩
    ((toEventGraph whole).playerStore owner config.store) config.defaults (history owner)
      at policyLaw
  rw [defaultsAgree, compilePolicyTable_commit_of_decode refs embedding.ref
    (profile owner) rfl _ defaults active (history owner) (sourceObserve owner state)
      decodedObservation] at policyLaw
  exact policyLaw

private theorem reveal_head_policy_eq
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (wholeProfile : BehavioralProfile whole)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : published ∉ Γ.map Prod.fst}
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (profile : BehavioralProfile (.reveal published owner name fresh selected unresolved next))
    (refs : ContextRefs (graphLayout whole) Γ)
    (revelations : Revelations Γ) (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.reveal published owner name fresh selected unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix whole wholeProfile
      (.reveal published owner name fresh selected unresolved next)
      profile refs revelations registry embedding refsBefore offset)
    (config : (toEventGraph whole).Config)
    (state : State L Γ) (refsAgree : refs.Agrees state config.store)
    (history : History Player L) (historyAgree : decodeHistory whole config.history = history)
    (defaults : DefaultHistory Player) (defaultsAgree : config.defaults = defaults)
    (active : owner ∉ defaults.defaulted)
    (actor : (toEventGraph whole).actor?
      (embedding.event ⟨0, Nat.zero_lt_succ (eventCount next)⟩) = some owner) :
    cast (congrArg PMF (congrArg Vegas.EventGraph.EventField.Action
      (embedding.layout_eq ⟨0, Nat.zero_lt_succ (eventCount next)⟩)))
      ((compileEventProfile whole wholeProfile) owner
        (embedding.event ⟨0, Nat.zero_lt_succ (eventCount next)⟩) actor
        ((toEventGraph whole).playerObserve owner config)
        (by simpa only [EventGraph.playerObserve_defaulted, EventGraph.Config.defaulted,
          defaultsAgree] using active)) =
      revealKernel profile ⟨sourceObserve owner state, defaults, history owner⟩ active := by
  have graphActive : owner ∉ ((toEventGraph whole).playerObserve owner config).defaulted := by
    simpa only [EventGraph.playerObserve_defaulted, EventGraph.Config.defaulted,
      defaultsAgree] using active
  have decodedObservation := decodeObservation?_playerStore_eq_some
    (graph := toEventGraph whole) refs owner state config.store refsAgree
  have policyLaw := aligned.policyEq owner ⟨0, Nat.zero_lt_succ (eventCount next)⟩ actor
    ((toEventGraph whole).playerObserve owner config) graphActive
  rw [decodeCompletions_playerObserve whole config owner, historyAgree] at policyLaw
  change _ = compilePolicyTable
    (.reveal published owner name fresh selected unresolved next) refs embedding.ref
    owner (profile owner) ⟨0, Nat.zero_lt_succ (eventCount next)⟩
    ((toEventGraph whole).playerStore owner config.store) config.defaults (history owner)
      at policyLaw
  rw [defaultsAgree, compilePolicyTable_reveal_of_decode refs embedding.ref
    (profile owner) rfl _ defaults active (history owner) (sourceObserve owner state)
      decodedObservation] at policyLaw
  exact policyLaw

/-- A compiled commitment preserves typed cells, actual own choices and the
public default history, including automatic failure after default. -/
private theorem commit_head_agreement
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (wholeProfile : BehavioralProfile whole)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {guard : SourceGuard L Γ owner name payload}
    {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames)}
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout whole) Γ) (source : SourceProgram.Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix whole wholeProfile (.commit name owner fresh guard next)
      profile refs source.revelations source.registry embedding refsBefore offset)
    (config : (toEventGraph whole).Config)
    (ready : config.cut.Ready (embedding.event ⟨0, by simp [eventCount]⟩))
    (outputEq : (toEventGraph whole).outputLayout
      (embedding.event ⟨0, by simp [eventCount]⟩) = .binding owner payload)
    (refsAgree : refs.Agrees source.state config.store)
    (historyAgree : decodeHistory whole config.history = source.history)
    (defaultsAgree : config.defaults = source.defaults)
    (choice : Option (PublicationResult (L.Val payload))) :
    let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event := embedding.event headIndex
    let sourceAfter := commitSuccessor name guard source choice
    let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) choice
    let stored := cast (congrArg EventGraph.EventField.Value outputEq.symm)
      (sourceAfter.state.get .here)
    let after := config.complete event ready action stored
    (refs.cons (name := name) (embedding.ref headIndex)).Agrees sourceAfter.state after.store ∧
      decodeHistory whole after.history = sourceAfter.history ∧
        after.defaults = sourceAfter.defaults := by
  dsimp only
  let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let event := embedding.event headIndex
  let sourceAfter := commitSuccessor name guard source choice
  let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) choice
  let stored := cast (congrArg EventGraph.EventField.Value outputEq.symm)
    (sourceAfter.state.get .here)
  let after := config.complete event ready action stored
  have status : config.defaulted = source.defaulted :=
    congrArg DefaultHistory.defaulted defaultsAgree
  have codeEq : cast (congrArg (EventGraph.EventCode (graphLayout whole)) outputEq)
      ((toEventGraph whole).nodes event) = .bind owner payload := by
    simpa [event, headIndex, compileRankedNodes] using aligned.graphSuffix.nodeEq headIndex
  have actor : (toEventGraph whole).actor? event = some owner := by
    simpa [event, headIndex, eventOwner?] using aligned.actorEq headIndex
  have nodeActor : ((toEventGraph whole).nodes event).actor = some owner := actor
  have oldRefs : refs.Agrees source.state after.store := by
    apply ContextRefs.Agrees.complete ready action stored refs source.state refsAgree
    exact fun cell => refsBefore cell headIndex
  have storedResult : (embedding.ref headIndex).get? after.store =
      some (sourceAfter.state.get .here) :=
    embedding.ref_get?_complete whole config headIndex ready action outputEq _
  have supported : after ∈ (config.step event ready action).support := by
    rw [commit_step config event ready outputEq codeEq choice]
    simp [after, action, stored, sourceAfter, commitSuccessor, status]
  have decodedAction : decodeEventAction whole event action =
      some (OwnAction.commit owner name payload choice) := by
    have embedded := aligned.actionEq headIndex action
    simpa [event, headIndex, action, outputEq, decodeEventAction] using embedded
  have decodedDecision : (config.actualDecision event action).bind
      (decodeEventAction whole event) =
        if owner ∈ source.defaulted then none
          else some (OwnAction.commit owner name payload choice) := by
    by_cases inactive : owner ∈ source.defaulted
    · simp [EventGraph.Config.actualDecision, EventGraph.EventCode.actualDecision,
        nodeActor, status, inactive]
    · simp [EventGraph.Config.actualDecision, EventGraph.EventCode.actualDecision,
        nodeActor, status, inactive, decodedAction]
  refine ⟨?_, ?_, ?_⟩
  · change (refs.cons (name := name) (embedding.ref headIndex)).Agrees
      (Env.cons (sourceAfter.state.get .here) source.state) after.store
    exact ContextRefs.Agrees.cons refs source.state after.store oldRefs
      (name := name) (cell := .commitment owner payload)
      (embedding.ref headIndex) (sourceAfter.state.get .here) storedResult
  · rw [decodeHistory_step whole config after event ready action supported, decodedDecision]
    by_cases inactive : owner ∈ source.defaulted
    · simp [commitSuccessor, inactive, historyAgree]
    · simp [commitSuccessor, inactive, historyAgree, sourceActionOwner]
  · change after.defaults = sourceAfter.defaults
    rw [show after.defaults = config.defaults.record
      (((EventGraph.EventCode.bind (layout := graphLayout whole) owner payload).actualDecision
        config.defaulted choice).bind fun chosen =>
          (EventGraph.EventCode.bind (layout := graphLayout whole) owner payload).defaultEvent
            chosen (sourceAfter.state.get .here)) from
      config.complete_defaults_of_code event ready outputEq _ codeEq choice _]
    by_cases inactive : owner ∈ source.defaulted
    · simp [sourceAfter, commitSuccessor, EventGraph.EventCode.actualDecision,
        EventGraph.EventCode.actor, status, inactive, defaultsAgree]
    · simp [sourceAfter, commitSuccessor, EventGraph.EventCode.actualDecision,
        EventGraph.EventCode.actor, EventGraph.EventCode.defaultEvent,
        EventGraph.EventCode.causesDefault, status, inactive, defaultsAgree]

private theorem reveal_head_agreement
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (wholeProfile : BehavioralProfile whole)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : published ∉ Γ.map Prod.fst}
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ openNames)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name))
    (profile : BehavioralProfile (.reveal published owner name fresh selected unresolved next))
    (source : SourceProgram.Config Player L Γ)
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.reveal published owner name fresh selected unresolved next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix whole wholeProfile
      (.reveal published owner name fresh selected unresolved next)
      profile refs source.revelations source.registry embedding refsBefore offset)
    (config : (toEventGraph whole).Config)
    (refsAgree : refs.Agrees source.state config.store)
    (historyAgree : decodeHistory whole config.history = source.history)
    (defaultsAgree : config.defaults = source.defaults)
    (ready : config.cut.Ready (embedding.event ⟨0, Nat.zero_lt_succ (eventCount next)⟩))
    (disclose : Bool) :
    let headIndex : Fin (eventCount
      (.reveal published owner name fresh selected unresolved next)) :=
      ⟨0, Nat.zero_lt_succ (eventCount next)⟩
    let sourceAfter := revealSuccessor published selected source disclose
    let action := cast
      (congrArg EventGraph.EventField.Action (embedding.layout_eq headIndex).symm) disclose
    let stored := cast
      (congrArg EventGraph.EventField.Value (embedding.layout_eq headIndex).symm)
      (sourceAfter.state.get .here)
    let graphAfter := config.complete (embedding.event headIndex) ready action stored
    (refs.cons (name := published) (embedding.ref headIndex)).Agrees
        sourceAfter.state graphAfter.store ∧
      decodeHistory whole graphAfter.history = sourceAfter.history ∧
      graphAfter.defaults = sourceAfter.defaults := by
  let headIndex : Fin (eventCount
    (.reveal published owner name fresh selected unresolved next)) :=
    ⟨0, Nat.zero_lt_succ (eventCount next)⟩
  let event := embedding.event headIndex
  let sourceAfter := revealSuccessor published selected source disclose
  let outputEq : (toEventGraph whole).outputLayout event = .publication payload :=
    embedding.layout_eq headIndex
  let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose
  let accepted := sourceAfter.state.get .here
  let stored := cast (congrArg EventGraph.EventField.Value outputEq.symm) accepted
  let graphAfter := config.complete event ready action stored
  change (refs.cons (name := published) (embedding.ref headIndex)).Agrees
      sourceAfter.state graphAfter.store ∧
    decodeHistory whole graphAfter.history = sourceAfter.history ∧
    graphAfter.defaults = sourceAfter.defaults
  have codeEq : cast (congrArg (EventGraph.EventCode (graphLayout whole)) outputEq)
      ((toEventGraph whole).nodes event) =
      .resolve owner payload (refs.get selected)
        (compileChecks (published := published) refs source.registry source.revelations
          selected) := by
    simpa [event, headIndex, compileRankedNodes] using aligned.graphSuffix.nodeEq headIndex
  have actor : (toEventGraph whole).actor? event = some owner := by
    simpa [event, headIndex, eventOwner?] using aligned.actorEq headIndex
  have defaultedAgree : config.defaulted = source.defaulted := by
    exact congrArg DefaultHistory.defaulted defaultsAgree
  have oldRefs : refs.Agrees source.state graphAfter.store := by
    apply ContextRefs.Agrees.complete ready action stored refs source.state refsAgree
    exact fun cell => refsBefore cell headIndex
  have storedResult : (embedding.ref headIndex).get? graphAfter.store = some accepted := by
    exact embedding.ref_get?_complete whole config headIndex ready action outputEq accepted
  have stateAgree : (refs.cons (name := published) (embedding.ref headIndex)).Agrees
      sourceAfter.state graphAfter.store := by
    exact ContextRefs.Agrees.cons refs source.state graphAfter.store oldRefs
      (name := published) (cell := .publication payload) (embedding.ref headIndex) accepted
      storedResult
  have stepLaw : config.step event ready action = PMF.pure graphAfter := by
    have step := reveal_step config event ready outputEq refs source.revelations source.registry
      selected codeEq source.state refsAgree disclose
    simpa only [defaultedAgree, sourceAfter, accepted, stored, action, graphAfter,
      revealSuccessor, Env.get, Env.cons] using step
  have supported : graphAfter ∈ (config.step event ready action).support := by
    rw [stepLaw]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  have decodedAction : decodeEventAction whole event action =
      some (OwnAction.reveal owner name disclose) := by
    have embedded := aligned.actionEq headIndex action
    simpa [event, headIndex, action, outputEq, decodeEventAction] using embedded
  have actualDecision : config.actualDecision event action =
      if owner ∈ source.defaulted then none else some action := by
    have owned : ((toEventGraph whole).nodes event).actor = some owner := actor
    simp only [EventGraph.Config.actualDecision, EventGraph.EventCode.actualDecision,
      owned, defaultedAgree]
  have historyAfter : decodeHistory whole graphAfter.history = sourceAfter.history := by
    have historyStep := decodeHistory_step whole config graphAfter event ready action supported
    rw [actualDecision] at historyStep
    by_cases inactive : owner ∈ source.defaulted
    · simpa [inactive, sourceAfter, revealSuccessor, historyAgree] using historyStep
    · simpa [inactive, decodedAction, historyAgree, sourceAfter, revealSuccessor,
        sourceActionOwner] using historyStep
  have defaultsAfter : graphAfter.defaults = sourceAfter.defaults := by
    have sourceDefaults : sourceAfter.defaults = source.defaults.record
        (if owner ∈ source.defaulted then none
          else if accepted.isFailure then some owner else none) := rfl
    have graphDefaults := config.complete_defaults_of_code event ready outputEq
      (.resolve owner payload (refs.get selected)
        (compileChecks (published := published) refs source.registry source.revelations selected))
      codeEq disclose accepted
    change graphAfter.defaults = _ at graphDefaults
    rw [graphDefaults, sourceDefaults, defaultsAgree, defaultedAgree]
    by_cases inactive : owner ∈ source.defaulted <;>
      simp [EventGraph.EventCode.actualDecision, EventGraph.EventCode.actor,
        EventGraph.EventCode.defaultEvent, EventGraph.EventCode.causesDefault, inactive]
  exact ⟨stateAgree, historyAfter, defaultsAfter⟩

/-- Canonical graph execution preserves the complete source configuration at
every aligned suffix, including all public defaults and actual choices. -/
theorem runFrom_option_law
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (wholeProfile : BehavioralProfile whole) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (profile : BehavioralProfile program)
      (refs : ContextRefs (graphLayout whole) Γ) (source : SourceProgram.Config Player L Γ)
      (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program)
      (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix whole wholeProfile program profile refs
        source.revelations source.registry embedding refsBefore offset →
      ∀ (config : (toEventGraph whole).Config),
      config.cut.IsPrefix offset → refs.Agrees source.state config.store →
      decodeHistory whole config.history = source.history →
      config.defaults = source.defaults →
      ((toEventGraph whole).runPlan
        ((toEventGraph whole).policyPlan (compileEventProfile whole wholeProfile)
          (toEventGraph whole).canonicalScheduler) (eventCount program) config).map
          (fun final => decodeConfig? whole program refs source.revelations source.registry
            embedding final.store final.history) =
        (runFrom program profile source).map some := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro profile refs source embedding refsBefore offset aligned config ordered
        refsAgree historyAgree defaultsAgree
      change EventGraph.Completion.defaults config.history = source.defaults at defaultsAgree
      simp only [eventCount, EventGraph.runPlan, PMF.pure_map, decodeConfig?,
        terminalRefsWith, finalRegistry, finalRevelations, runFrom]
      rw [decodeState?_eq_some refs source.state config.store refsAgree]
      simp only [Option.map_some, historyAgree, defaultsAgree]
  | sample name fresh law next ih =>
      intro profile refs source embedding refsBefore offset aligned config ordered
        refsAgree historyAgree defaultsAgree
      let headIndex : Fin (eventCount (.sample name fresh law next)) := ⟨0, by simp [eventCount]⟩
      let event := embedding.event headIndex
      have rank : event.val = offset := by
        simpa [event, headIndex] using aligned.graphSuffix.rankEq headIndex
      obtain ⟨ready, least⟩ := canonical_ready_least ordered event rank
      have outputEq : (toEventGraph whole).outputLayout event =
          outputLayout (.sample name fresh law next) headIndex := embedding.layout_eq headIndex
      have codeEq : cast (congrArg (EventGraph.EventCode (graphLayout whole)) outputEq)
          ((toEventGraph whole).nodes event) =
          .sample _ (compilePublicDist refs law) := by
        simpa [event, headIndex, compileRankedNodes] using aligned.graphSuffix.nodeEq headIndex
      have ownerless : (toEventGraph whole).actor? event = none := by
        simpa [event, headIndex, eventOwner?] using aligned.actorEq headIndex
      have suppliedAction : EventGraph.EventCode.actionOfActorNone
          ((toEventGraph whole).nodes event) ownerless =
          cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit :=
        EventGraph.EventCode.action_eq_of_actor_none
          ((toEventGraph whole).nodes event) ownerless _ _
      rw [show eventCount (.sample name fresh law next) = eventCount next + 1 by rfl,
        EventGraph.runPlan_canonical_ownerless (compileEventProfile whole wholeProfile)
          (eventCount next) config event ready least ownerless, suppliedAction,
        sample_step config event ready outputEq refs law codeEq source.state refsAgree]
      simp only [PMF.bind_map, PMF.map_bind, runFrom, Function.comp_def]
      apply bind_congr_on_support _
      intro value valueMem
      let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit
      let stored := cast (congrArg EventGraph.EventField.Value outputEq.symm) value
      let nextConfig := config.complete event ready action stored
      let sourceAfter := sampleSuccessor name source value
      have oldRefs : refs.Agrees source.state nextConfig.store := by
        apply ContextRefs.Agrees.complete ready action stored refs source.state refsAgree
        exact fun cell => refsBefore cell headIndex
      have storedResult : (embedding.ref headIndex).get? nextConfig.store = some value :=
        embedding.ref_get?_complete whole config headIndex ready action outputEq value
      have nextRefs : (refs.cons (name := name) (embedding.ref headIndex)).Agrees
          sourceAfter.state nextConfig.store :=
        ContextRefs.Agrees.cons refs source.state nextConfig.store oldRefs
          (name := name) (cell := .publicData _) (embedding.ref headIndex) value storedResult
      have nextPrefix : nextConfig.cut.IsPrefix (offset + 1) :=
        ordered.complete_at event ready rank
      have noDecision : config.actualDecision event action = none := by
        have owned : ((toEventGraph whole).nodes event).actor = none := ownerless
        simp only [EventGraph.Config.actualDecision, EventGraph.EventCode.actualDecision, owned]
      have supported : nextConfig ∈ (config.step event ready action).support := by
        rw [sample_step config event ready outputEq refs law codeEq source.state refsAgree,
          PMF.support_map]
        exact ⟨value, valueMem, rfl⟩
      have nextHistory : decodeHistory whole nextConfig.history = sourceAfter.history := by
        have silent : (config.actualDecision event action).bind
            (decodeEventAction whole event) = none := by rw [noDecision]; rfl
        exact (decodeHistory_step_of_none whole config nextConfig event ready
          action silent supported).trans historyAgree
      have nextDefaults : nextConfig.defaults = sourceAfter.defaults := by
        change (config.complete event ready action stored).defaults = source.defaults.record none
        rw [EventGraph.Config.complete_defaults, noDecision]
        simpa only [EventGraph.Completion.fromDecision, Option.bind_none] using
          congrArg (fun previous => previous.record none) defaultsAgree
      have tailAligned := aligned.sampleTail (whole := whole)
        (wholeProfile := wholeProfile) (_openNames := ∅) fresh law next profile refs
        source.revelations source.registry embedding refsBefore offset
      exact ih (afterSample profile) (refs.cons (embedding.ref headIndex)) sourceAfter
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
        (refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl)
        (offset + 1) tailAligned nextConfig nextPrefix nextRefs nextHistory nextDefaults
  | commit name owner fresh guard next ih =>
      intro profile refs source embedding refsBefore offset aligned config ordered
        refsAgree historyAgree defaultsAgree
      let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
        ⟨0, by simp [eventCount]⟩
      let event := embedding.event headIndex
      have rank : event.val = offset := by
        simpa [event, headIndex] using aligned.graphSuffix.rankEq headIndex
      obtain ⟨ready, least⟩ := canonical_ready_least ordered event rank
      have outputEq : (toEventGraph whole).outputLayout event =
          outputLayout (.commit name owner fresh guard next) headIndex :=
        embedding.layout_eq headIndex
      have codeEq : cast (congrArg (EventGraph.EventCode (graphLayout whole)) outputEq)
          ((toEventGraph whole).nodes event) = .bind owner _ := by
        simpa [event, headIndex, compileRankedNodes] using aligned.graphSuffix.nodeEq headIndex
      have actor : (toEventGraph whole).actor? event = some owner := by
        simpa [event, headIndex, eventOwner?] using aligned.actorEq headIndex
      have status : config.defaulted = source.defaulted :=
        congrArg DefaultHistory.defaulted defaultsAgree
      let kernel := if inactive : owner ∈ source.defaulted then PMF.pure none
        else commitKernel profile (source.view owner) inactive
      have policyLaw :
          (if inactive : owner ∈ config.defaulted then
            PMF.pure (((toEventGraph whole).nodes event).failureAction owner actor)
          else (compileEventProfile whole wholeProfile) owner event actor
            ((toEventGraph whole).playerObserve owner config) inactive) =
          kernel.map (fun choice => cast
            (congrArg EventGraph.EventField.Action outputEq.symm) choice) := by
        by_cases inactive : owner ∈ source.defaulted
        · have stopped : owner ∈ config.defaulted := status.symm ▸ inactive
          simp only [kernel, dite_eq_left inactive, dite_eq_left stopped, PMF.pure_map]
          exact congrArg PMF.pure (EventGraph.EventCode.failureAction_eq_cast outputEq
            ((toEventGraph whole).nodes event) (.bind owner _) codeEq owner actor rfl)
        · have active : owner ∉ config.defaulted := status.symm ▸ inactive
          simp only [kernel, dite_eq_right inactive, dite_eq_right active]
          exact eq_map_cast_of_cast_eq (congrArg EventGraph.EventField.Action outputEq) _ _
            (commit_head_policy_eq whole wholeProfile next profile refs source.revelations
              source.registry embedding refsBefore offset aligned config source.state refsAgree
              source.history historyAgree source.defaults defaultsAgree inactive actor)
      rw [show eventCount (.commit name owner fresh guard next) = eventCount next + 1 by rfl,
        EventGraph.runPlan_canonical_actor_cases (compileEventProfile whole wholeProfile)
          (eventCount next) config event ready least owner actor, policyLaw]
      simp only [PMF.bind_map, PMF.map_bind, runFrom, Function.comp_def]
      apply bind_congr_on_support _
      intro choice _
      let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) choice
      let sourceAfter := commitSuccessor name guard source choice
      let stored := cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (sourceAfter.state.get .here)
      let nextConfig := config.complete event ready action stored
      have stepLaw : config.step event ready action = PMF.pure nextConfig := by
        have step := commit_step config event ready outputEq codeEq choice
        simpa only [status, sourceAfter, stored, action, nextConfig, commitSuccessor,
          Env.get, Env.cons] using step
      rw [stepLaw, PMF.pure_bind]
      have nextPrefix : nextConfig.cut.IsPrefix (offset + 1) :=
        ordered.complete_at event ready rank
      have agrees := commit_head_agreement whole wholeProfile profile refs source embedding
        refsBefore offset aligned config ready outputEq refsAgree historyAgree defaultsAgree choice
      have tailAligned := aligned.commitTail whole wholeProfile fresh guard next profile refs
        source.revelations source.registry embedding refsBefore offset
      exact ih (afterCommit profile) (refs.cons (embedding.ref headIndex)) sourceAfter
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
        (refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl)
        (offset + 1) tailAligned nextConfig nextPrefix agrees.1 agrees.2.1 agrees.2.2
  | reveal published owner name fresh selected unresolved next ih =>
      intro profile refs source embedding refsBefore offset aligned config ordered
        refsAgree historyAgree defaultsAgree
      let headIndex : Fin (eventCount
          (.reveal published owner name fresh selected unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      let event := embedding.event headIndex
      have rank : event.val = offset := by
        simpa [event, headIndex] using aligned.graphSuffix.rankEq headIndex
      obtain ⟨ready, least⟩ := canonical_ready_least ordered event rank
      have outputEq : (toEventGraph whole).outputLayout event =
          outputLayout (.reveal published owner name fresh selected unresolved next) headIndex :=
        embedding.layout_eq headIndex
      have codeEq : cast (congrArg (EventGraph.EventCode (graphLayout whole)) outputEq)
          ((toEventGraph whole).nodes event) =
          .resolve owner _ (refs.get selected)
            (compileChecks (published := published) refs source.registry source.revelations
              selected) := by
        simpa [event, headIndex, compileRankedNodes] using aligned.graphSuffix.nodeEq headIndex
      have actor : (toEventGraph whole).actor? event = some owner := by
        simpa [event, headIndex, eventOwner?] using aligned.actorEq headIndex
      have status : config.defaulted = source.defaulted :=
        congrArg DefaultHistory.defaulted defaultsAgree
      let kernel := if inactive : owner ∈ source.defaulted then PMF.pure false
        else revealKernel profile (source.view owner) inactive
      have policyLaw :
          (if inactive : owner ∈ config.defaulted then
            PMF.pure (((toEventGraph whole).nodes event).failureAction owner actor)
          else (compileEventProfile whole wholeProfile) owner event actor
            ((toEventGraph whole).playerObserve owner config) inactive) =
          kernel.map (fun disclose => cast
            (congrArg EventGraph.EventField.Action outputEq.symm) disclose) := by
        by_cases inactive : owner ∈ source.defaulted
        · have stopped : owner ∈ config.defaulted := status.symm ▸ inactive
          simp only [kernel, dite_eq_left inactive, dite_eq_left stopped, PMF.pure_map]
          exact congrArg PMF.pure (EventGraph.EventCode.failureAction_eq_cast outputEq
            ((toEventGraph whole).nodes event)
            (.resolve owner _ (refs.get selected)
              (compileChecks (published := published) refs source.registry source.revelations
                selected)) codeEq owner actor rfl)
        · have active : owner ∉ config.defaulted := status.symm ▸ inactive
          simp only [kernel, dite_eq_right inactive, dite_eq_right active]
          exact eq_map_cast_of_cast_eq (congrArg EventGraph.EventField.Action outputEq) _ _
            (reveal_head_policy_eq whole wholeProfile selected unresolved next profile refs
              source.revelations source.registry embedding refsBefore offset aligned config
              source.state refsAgree source.history historyAgree source.defaults defaultsAgree
              inactive actor)
      rw [show eventCount (.reveal published owner name fresh selected unresolved next) =
          eventCount next + 1 by rfl,
        EventGraph.runPlan_canonical_actor_cases (compileEventProfile whole wholeProfile)
          (eventCount next) config event ready least owner actor, policyLaw]
      simp only [PMF.bind_map, PMF.map_bind, runFrom, Function.comp_def]
      apply bind_congr_on_support _
      intro disclose _
      let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose
      let sourceAfter := revealSuccessor published selected source disclose
      let stored := cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (sourceAfter.state.get .here)
      let nextConfig := config.complete event ready action stored
      have stepLaw : config.step event ready action = PMF.pure nextConfig := by
        have step := reveal_step config event ready outputEq refs source.revelations
          source.registry selected codeEq source.state refsAgree disclose
        simpa only [status, sourceAfter, stored, action, nextConfig, revealSuccessor,
          Env.get, Env.cons] using step
      rw [stepLaw, PMF.pure_bind]
      have nextPrefix : nextConfig.cut.IsPrefix (offset + 1) :=
        ordered.complete_at event ready rank
      have agrees := reveal_head_agreement whole wholeProfile selected unresolved next profile
        source refs embedding refsBefore offset aligned config refsAgree historyAgree defaultsAgree
        ready disclose
      have tailAligned := aligned.revealTail (whole := whole)
        (wholeProfile := wholeProfile) fresh selected unresolved next profile refs
        source.revelations source.registry embedding refsBefore offset
      exact ih (afterReveal profile) (refs.cons (embedding.ref headIndex)) sourceAfter
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
        (refsBefore.tail_cons next (by simp [eventCount]) (fun _ => rfl) _ rfl)
        (offset + 1) tailAligned nextConfig nextPrefix agrees.1 agrees.2.1 agrees.2.2

end Vegas
