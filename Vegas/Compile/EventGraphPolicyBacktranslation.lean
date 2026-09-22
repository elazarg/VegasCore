/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphBacktranslation
import Vegas.Compile.EventGraphObservationEncoding
import Vegas.EventGraph.NormalizedPolicy
import Vegas.EventGraph.Recall

/-! # Canonical event-graph policy backtranslation

An arbitrary policy of the compiled graph is interpreted as a source policy
by reconstructing the canonical rank-prefix observation at each source
decision. Malformed source views use genuine failure actions.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Transport an action from one whole-graph output to the corresponding
residual source output named by an embedding. -/
def OutputEmbedding.castAction {inputCount totalCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin totalCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {program : SourceProgram Player L Γ openNames}
    (embedding : OutputEmbedding inputs outputs program)
    (index : Fin (eventCount program)) :
    Vegas.EventGraph.EventField.Action (outputs (embedding.event index)) →
      Vegas.EventGraph.EventField.Action (outputLayout program index) :=
  fun action => cast (congrArg Vegas.EventGraph.EventField.Action
    (embedding.layout_eq index)) action

/-- Transport the action at an embedded commitment head to its concrete
failure-aware binding value. -/
def OutputEmbedding.commitHeadAction {inputCount totalCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin totalCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames)}
    (embedding : OutputEmbedding inputs outputs
      (.commit name owner fresh guard next)) :
    Vegas.EventGraph.EventField.Action
        (outputs (embedding.event ⟨0, by simp [eventCount]⟩)) →
      PublicationResult (L.Val payload) :=
  let index : Fin (eventCount (.commit name owner fresh guard next)) :=
    ⟨0, by simp [eventCount]⟩
  let outputEq : outputLayout (.commit name owner fresh guard next) index =
      .binding owner payload := by simp [index, outputLayout, eventCount]
  fun action => cast (congrArg Vegas.EventGraph.EventField.Action outputEq)
    (embedding.castAction index action)

/-- Transport the action at an embedded resolution head to its disclosure
Boolean. -/
def OutputEmbedding.revealHeadAction {inputCount totalCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin totalCount → Vegas.EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : published ∉ Γ.map Prod.fst}
    {selected : HasVar Γ name (.commitment owner payload)}
    {unresolved : name ∈ openNames}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name)}
    (embedding : OutputEmbedding inputs outputs
      (.reveal published owner name fresh selected unresolved next)) :
    Vegas.EventGraph.EventField.Action
        (outputs (embedding.event ⟨0, by simp [eventCount]⟩)) → Bool :=
  let index : Fin (eventCount
      (.reveal published owner name fresh selected unresolved next)) :=
    ⟨0, by simp [eventCount]⟩
  let outputEq : outputLayout
      (.reveal published owner name fresh selected unresolved next) index =
      .publication payload := by simp [index, outputLayout, eventCount]
  fun action => cast (congrArg Vegas.EventGraph.EventField.Action outputEq)
    (embedding.castAction index action)

/-- Encode a source decision view as the canonical observation at one event.
The store construction is total; history encoding fails rather than inventing
an event identity or dependent action. -/
def encodeDecisionView? {Γ₀ : SourceCtx Player L} {open₀ : Finset VarId}
    (whole : SourceProgram Player L Γ₀ open₀)
    {Γ : SourceCtx Player L} (refs : ContextRefs (graphLayout whole) Γ)
    (who : Player) (event : Fin (eventCount whole))
    (view : DecisionView who Γ) :
    Option ((toEventGraph whole).PlayerObservation who) := do
  let ownActions ← encodeCompletions? whole
    ((toEventGraph whole).prefixSchema.ownHistory event) view.2
  pure
    { completionOrder := (toEventGraph whole).rankPrefix event
      store := encodeObservationStore who refs view.1
      ownActions := ownActions }

/-- Successful decision-view encoding retains the original own-action history. -/
theorem encodeDecisionView?_history
    {Γ₀ : SourceCtx Player L} {open₀ : Finset VarId}
    (whole : SourceProgram Player L Γ₀ open₀)
    {Γ : SourceCtx Player L} (refs : ContextRefs (graphLayout whole) Γ)
    (who : Player) (event : Fin (eventCount whole))
    (view : DecisionView who Γ)
    (observation : (toEventGraph whole).PlayerObservation who)
    (encoded : encodeDecisionView? whole refs who event view = some observation) :
    decodeCompletions whole observation.ownActions = view.2 := by
  unfold encodeDecisionView? at encoded
  cases historyEncoded : encodeCompletions? whole
      ((toEventGraph whole).prefixSchema.ownHistory event) view.2 with
  | none =>
      rw [historyEncoded] at encoded
      contradiction
  | some completions =>
      rw [historyEncoded] at encoded
      cases encoded
      exact decodeCompletions_encodeCompletions?_eq whole _ view.2 completions
        historyEncoded

/-- At an actual reachable canonical source prefix, encoding the decoded
source decision view reconstructs the graph's normalized player observation
exactly: fixed rank prefix, actual visible store, and original own actions. -/
theorem encodeDecisionView?_eq_normalizeObservation
    {Γ₀ : SourceCtx Player L} {open₀ : Finset VarId}
    (whole : SourceProgram Player L Γ₀ open₀)
    {Γ : SourceCtx Player L} (refs : ContextRefs (graphLayout whole) Γ)
    (offset : Nat) (covered : refs.CoversPrefix whole offset)
    (inputs : (toEventGraph whole).Inputs)
    (config : (toEventGraph whole).Config)
    (reachable : config.Reachable inputs)
    (ordered : config.cut.IsPrefix offset) (state : State L Γ)
    (refsAgree : refs.Agrees state config.store)
    (history : History Player L)
    (historyAgree : decodeHistory whole config.history = history)
    (event : Fin (eventCount whole)) (ready : config.cut.Ready event)
    (who : Player) (actor : (toEventGraph whole).actor? event = some who) :
    encodeDecisionView? whole refs who event
        (sourceObserve who state, history who) =
      some ((toEventGraph whole).normalizeObservation event who
        ((toEventGraph whole).playerObserve who config)) := by
  let graph := toEventGraph whole
  let own := graph.ownCompletions who config.history
  have ownIds : own.map Vegas.EventGraph.Completion.event =
      graph.prefixSchema.ownHistory event := by
    exact (toEventGraph_barrierOrdered whole).informationDiscipline.ready_ownEventIds
      reachable ready actor
  have decodedOwn : decodeCompletions whole own = history who := by
    change decodeHistory whole config.history who = history who
    exact congrFun historyAgree who
  have strategic : ∀ completion ∈ own,
      ∃ sourceAction,
        decodeEventAction whole completion.event completion.action = some sourceAction := by
    intro completion member
    have filtered := List.mem_filter.mp member
    have ownerLaw := decodeEventAction_owner whole completion.event completion.action
    have actorLaw : graph.actor? completion.event = some who :=
      of_decide_eq_true filtered.2
    rw [eventOwner?_eq_actor whole completion.event, actorLaw] at ownerLaw
    cases decoded : decodeEventAction whole completion.event completion.action with
    | none => simp [decoded] at ownerLaw
    | some sourceAction => exact ⟨sourceAction, rfl⟩
  have historyEncoded : encodeCompletions? whole
      (graph.prefixSchema.ownHistory event) (history who) = some own := by
    have reconstructed := encodeCompletions?_decodeCompletions_eq_some whole own
      strategic
    rw [ownIds, decodedOwn] at reconstructed
    exact reconstructed
  have storeEq := encodeObservationStore_eq_playerStore_of_prefix whole refs
    offset covered config ordered state refsAgree who
  unfold encodeDecisionView?
  rw [historyEncoded]
  apply congrArg some
  apply Vegas.EventGraph.PlayerObservation.ext graph
  · rfl
  · exact storeEq
  · rfl

/-- At a reachable canonical prefix, any source observation obtained by
decoding the actual masked graph store re-encodes, together with the decoded
original own actions, to the graph's normalized decision observation. This
version needs no source-state simulation invariant. -/
theorem encodeDecisionView?_decodeActual_eq_normalizeObservation
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    {Γ : SourceCtx Player L} (refs : ContextRefs (graphLayout whole) Γ)
    (offset : Nat) (covered : refs.CoversPrefix whole offset)
    (inputs : (toEventGraph whole).Inputs)
    (config : (toEventGraph whole).Config)
    (reachable : config.Reachable inputs)
    (ordered : config.cut.IsPrefix offset)
    (event : Fin (eventCount whole)) (ready : config.cut.Ready event)
    (who : Player) (actor : (toEventGraph whole).actor? event = some who)
    (sourceObservation : SourceObservation L who Γ)
    (decodedStore : decodeObservation? who refs
      ((toEventGraph whole).playerStore who config.store) =
        some sourceObservation) :
    encodeDecisionView? whole refs who event
        (sourceObservation,
          decodeCompletions whole
            ((toEventGraph whole).ownCompletions who config.history)) =
      some ((toEventGraph whole).normalizeObservation event who
        ((toEventGraph whole).playerObserve who config)) := by
  let graph := toEventGraph whole
  let own := graph.ownCompletions who config.history
  have ownIds : own.map Vegas.EventGraph.Completion.event =
      graph.prefixSchema.ownHistory event :=
    (toEventGraph_barrierOrdered whole).informationDiscipline.ready_ownEventIds
      reachable ready actor
  have strategic : ∀ completion ∈ own,
      ∃ sourceAction,
        decodeEventAction whole completion.event completion.action = some sourceAction := by
    intro completion member
    have filtered := List.mem_filter.mp member
    have ownerLaw := decodeEventAction_owner whole completion.event completion.action
    have actorLaw : graph.actor? completion.event = some who :=
      of_decide_eq_true filtered.2
    rw [eventOwner?_eq_actor whole completion.event, actorLaw] at ownerLaw
    cases decoded : decodeEventAction whole completion.event completion.action with
    | none => simp [decoded] at ownerLaw
    | some sourceAction => exact ⟨sourceAction, rfl⟩
  have historyEncoded : encodeCompletions? whole
      (graph.prefixSchema.ownHistory event) (decodeCompletions whole own) =
        some own := by
    have reconstructed := encodeCompletions?_decodeCompletions_eq_some whole own
      strategic
    rw [ownIds] at reconstructed
    exact reconstructed
  have storeEq : encodeObservationStore who refs sourceObservation =
      graph.playerStore who config.store := by
    apply encodeObservationStore_decodeObservation?_eq refs who
      (graph.playerStore who config.store) sourceObservation decodedStore
    intro field absent
    exact ContextRefs.CoversPrefix.available_visible whole refs offset covered
      config ordered who field absent
  unfold encodeDecisionView?
  rw [historyEncoded]
  apply congrArg some
  apply Vegas.EventGraph.PlayerObservation.ext graph
  · rfl
  · exact storeEq
  · rfl

/-- Backtranslate one graph policy along a residual source program embedded in
the single graph compiled from `whole`. -/
def backtranslatePolicyTable
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (who : Player) (policy : (toEventGraph whole).BehavioralPolicy who) :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    (refs : ContextRefs (graphLayout whole) Γ) →
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole) program) →
    (actorEq : ∀ index,
      (toEventGraph whole).actor? (embedding.event index) =
        eventOwner? program index) →
      BehavioralPolicy who program
  | _, _, .ret _, _, _, _ => PUnit.unit
  | _, _, .sample name fresh law next, refs, embedding, actorEq =>
      let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
      let headIndex : Fin (eventCount (.sample name fresh law next)) :=
        ⟨0, by simp [eventCount]⟩
      let headRef : Vegas.EventGraph.FieldRef (graphLayout whole)
          (.publicData _) := by
        simpa [headIndex, outputLayout, eventCount] using embedding.ref headIndex
      backtranslatePolicyTable whole who policy next
        (refs.cons headRef) tailEmbedding
        (fun index => by
          simpa [tailEmbedding, OutputEmbedding.tail, eventOwner?, eventCount,
            Fin.cases_succ] using actorEq (Fin.succ index))
  | _, _, .commit (payload := payload) name owner fresh guard next, refs,
      embedding, actorEq =>
      let headIndex : Fin (eventCount (.commit name owner fresh guard next)) :=
        ⟨0, by simp [eventCount]⟩
      let event := embedding.event headIndex
      let headRef : Vegas.EventGraph.FieldRef (graphLayout whole)
          (.binding owner payload) := by
        simpa [headIndex, outputLayout, eventCount] using embedding.ref headIndex
      let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
      (fun same view =>
          have actor : (toEventGraph whole).actor? event = some who := by
            simpa [event, headIndex, eventOwner?, same] using actorEq headIndex
          match encodeDecisionView? whole refs who event view with
          | none => FinDist.pure .failure
          | some observation =>
              (policy event actor observation).map embedding.commitHeadAction,
        backtranslatePolicyTable whole who policy next
          (refs.cons headRef) tailEmbedding
          (fun index => by
            simpa [tailEmbedding, OutputEmbedding.tail, eventOwner?, eventCount,
              Fin.cases_succ] using actorEq (Fin.succ index)))
  | Γ, _, .reveal (payload := payload) published owner name fresh selected unresolved
      next, refs, embedding, actorEq =>
      let headIndex : Fin (eventCount
          (.reveal published owner name fresh selected unresolved next)) :=
        ⟨0, by simp [eventCount]⟩
      let event := embedding.event headIndex
      let resultRef : Vegas.EventGraph.FieldRef (graphLayout whole)
          (.publication payload) := by
        simpa [headIndex, outputLayout, eventCount] using embedding.ref headIndex
      let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
      (fun same view =>
          have actor : (toEventGraph whole).actor? event = some who := by
            simpa [event, headIndex, eventOwner?, same] using actorEq headIndex
          match encodeDecisionView? whole refs who event view with
          | none => FinDist.pure false
          | some observation =>
              (policy event actor observation).map embedding.revealHeadAction,
        backtranslatePolicyTable whole who policy next
          (refs.cons resultRef) tailEmbedding
          (fun index => by
            simpa [tailEmbedding, OutputEmbedding.tail, eventOwner?, eventCount,
              Fin.cases_succ] using actorEq (Fin.succ index)))

/-- Pull one arbitrary policy of the compiled graph back to a setup-uniform
source policy. -/
def backtranslateEventPolicy
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (who : Player)
    (policy : (toEventGraph program).BehavioralPolicy who) :
    BehavioralPolicy who program :=
  backtranslatePolicyTable program who policy program
    (ContextRefs.initial Γ (outputLayout program)) (outputEmbedding program)
    (fun index => (eventOwner?_eq_actor program index).symm)

/-- At a commitment view that encodes successfully, the backtranslated choice
is the arbitrary graph-policy kernel, transported only across the suffix
output-layout equality. -/
theorem backtranslatePolicyTable_commit_kernel
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (who : Player)
    (policy : (toEventGraph whole).BehavioralPolicy who)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {guard : SourceGuard L Γ owner name payload}
    {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames)}
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.commit name owner fresh guard next))
    (actorEq : ∀ index,
      (toEventGraph whole).actor? (embedding.event index) =
        eventOwner? (.commit name owner fresh guard next) index)
    (same : owner = who) (view : DecisionView who Γ)
    (observation : (toEventGraph whole).PlayerObservation who)
    (encoded : encodeDecisionView? whole refs who
      (embedding.event ⟨0, by simp [eventCount]⟩) view = some observation) :
    (backtranslatePolicyTable whole who policy
        (.commit name owner fresh guard next) refs embedding actorEq).1
        same view =
      (policy (embedding.event ⟨0, by simp [eventCount]⟩)
        (by simpa [eventOwner?, same] using actorEq ⟨0, by simp [eventCount]⟩)
        observation).map embedding.commitHeadAction := by
  simp only [backtranslatePolicyTable]
  rw [encoded]

/-- The analogous resolution kernel transports its Boolean action across the
suffix output-layout equality. -/
theorem backtranslatePolicyTable_reveal_kernel
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    (who : Player)
    (policy : (toEventGraph whole).BehavioralPolicy who)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : published ∉ Γ.map Prod.fst}
    {selected : HasVar Γ name (.commitment owner payload)}
    {unresolved : name ∈ openNames}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (openNames.erase name)}
    (refs : ContextRefs (graphLayout whole) Γ)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (.reveal published owner name fresh selected unresolved next))
    (actorEq : ∀ index,
      (toEventGraph whole).actor? (embedding.event index) =
        eventOwner? (.reveal published owner name fresh selected unresolved next) index)
    (same : owner = who) (view : DecisionView who Γ)
    (observation : (toEventGraph whole).PlayerObservation who)
    (encoded : encodeDecisionView? whole refs who
      (embedding.event ⟨0, by simp [eventCount]⟩) view = some observation) :
    (backtranslatePolicyTable whole who policy
        (.reveal published owner name fresh selected unresolved next) refs
        embedding actorEq).1 same view =
      (policy (embedding.event ⟨0, by simp [eventCount]⟩)
        (by simpa [eventOwner?, same] using actorEq ⟨0, by simp [eventCount]⟩)
        observation).map embedding.revealHeadAction := by
  simp only [backtranslatePolicyTable]
  rw [encoded]

end Vegas.SourceProgram.EventLowering
