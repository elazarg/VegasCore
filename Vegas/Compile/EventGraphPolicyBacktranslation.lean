/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphBacktranslation
import Vegas.Compile.EventGraphObservationEncoding
import Vegas.EventGraph.Recall

/-! # Canonical event-graph policy backtranslation

An arbitrary policy of the compiled graph is interpreted as a source policy
by reconstructing the canonical rank-prefix observation at each source
decision. Malformed source views use omission or withholding choices.
-/

noncomputable section

namespace Vegas

open SourceProgram

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

/-- Transport an embedded commitment action to its source binding choice,
retaining omission separately from accepted unusability. -/
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
      Option (PublicationResult (L.Val payload)) :=
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

/-- Encode the active source player's view at its fixed source-ranked event.
The complete public default history is copied without erasure. -/
def encodeDecisionView? {Γ₀ : SourceCtx Player L} {open₀ : Finset VarId}
    (whole : SourceProgram Player L Γ₀ open₀)
    {Γ : SourceCtx Player L} (refs : ContextRefs (graphLayout whole) Γ)
    (who : Player) (event : Fin (eventCount whole))
    (view : DecisionView who Γ) :
    Option ((toEventGraph whole).PlayerObservation who) := do
  let ownActions ← encodeCompletions? whole
    ((toEventGraph whole).prefixSchema.ownHistory event) view.history
  pure
    { completionOrder := (List.finRange (eventCount whole)).filter
        (fun prior => prior.val < event.val)
      store := encodeObservationStore who refs view.observation
      ownActions := ownActions
      defaults := view.defaults }

/-- Successful encoding retains the source default record exactly. -/
theorem encodeDecisionView?_defaults {Γ₀ : SourceCtx Player L} {open₀ : Finset VarId}
    (whole : SourceProgram Player L Γ₀ open₀) {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout whole) Γ) (who : Player)
    (event : Fin (eventCount whole)) (view : DecisionView who Γ)
    (observation : (toEventGraph whole).PlayerObservation who)
    (encoded : encodeDecisionView? whole refs who event view = some observation) :
    observation.defaults = view.defaults := by
  unfold encodeDecisionView? at encoded
  cases histories : encodeCompletions? whole
      ((toEventGraph whole).prefixSchema.ownHistory event) view.history with
  | none => simp [histories] at encoded
  | some actions =>
      simp only [histories, pure] at encoded
      cases encoded
      rfl

private theorem compiled_history_pairwise
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    {inputs : (toEventGraph program).Inputs} {config : (toEventGraph program).Config}
    (reachable : config.Reachable inputs) :
    (config.history.map Vegas.EventGraph.Completion.event).Pairwise
      (fun left right => left.val < right.val) := by
  induction reachable with
  | initial => simp [Vegas.EventGraph.Config.initial]
  | @step prior priorReachable event ready action next supported ih =>
      obtain ⟨value, _, history⟩ := prior.step_completion event ready action next supported
      rw [history, List.map_append]
      simp only [List.map_cons, List.map_nil, List.pairwise_append]
      refine ⟨ih, by simp, ?_⟩
      intro earlier member later last
      have same : later = event := by
        have selected := List.mem_singleton.mp last
        exact selected
      subst later
      have completed := (prior.history_exact earlier).mp member
      exact (EventOrder.Cut.mem_completed_iff_lt_of_ready prior.cut ready).mp completed

/-- The compiled sequential order determines its complete chronological prefix. -/
private theorem compiled_history_eq_prefix
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    {inputs : (toEventGraph program).Inputs} {config : (toEventGraph program).Config}
    (reachable : config.Reachable inputs) (offset : Nat) (ordered : config.cut.IsPrefix offset)
    (event : Fin (eventCount program)) (rank : event.val = offset) :
    config.history.map Vegas.EventGraph.Completion.event =
      (List.finRange (eventCount program)).filter (fun prior => prior.val < event.val) := by
  apply (compiled_history_pairwise program reachable).eq_of_mem_iff
    ((List.sortedLT_finRange (eventCount program)).pairwise.filter _)
  intro prior
  simp only [config.history_exact, ordered.2, List.mem_filter, List.mem_finRange, true_and]
  rw [rank]
  simp only [decide_eq_true_eq]

/-- Decoding and re-encoding an active actual compiled view recovers that same
view. All chronological and public default information is retained. -/
theorem encodeDecisionView?_decodeActual_eq
    {wholeΓ : SourceCtx Player L} {wholeOpen : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeOpen)
    {Γ : SourceCtx Player L} (refs : ContextRefs (graphLayout whole) Γ)
    (offset : Nat) (covered : refs.CoversPrefix whole offset)
    (inputs : (toEventGraph whole).Inputs) (config : (toEventGraph whole).Config)
    (reachable : config.Reachable inputs) (ordered : config.cut.IsPrefix offset)
    (event : Fin (eventCount whole)) (rank : event.val = offset)
    (ready : config.cut.Ready event)
    (who : Player) (actor : (toEventGraph whole).actor? event = some who)
    (active : who ∉ config.defaulted)
    (sourceObservation : SourceObservation L who Γ)
    (decodedStore : decodeObservation? who refs
      ((toEventGraph whole).playerStore who config.store) = some sourceObservation) :
    encodeDecisionView? whole refs who event
        ⟨sourceObservation, config.defaults,
          decodeCompletions whole ((toEventGraph whole).ownCompletions who config.history)⟩ =
      some ((toEventGraph whole).playerObserve who config) := by
  let graph := toEventGraph whole
  let own := graph.ownCompletions who config.history
  have ownIds : own.map Vegas.EventGraph.Completion.event =
      graph.prefixSchema.ownHistory event :=
    (toEventGraph_barrierOrdered whole).informationDiscipline.ready_ownEventIds
      reachable ready actor active
  have strategic : ∀ completion ∈ own,
      ∃ action sourceAction, completion.decision = some action ∧
        decodeEventAction whole completion.event action = some sourceAction := by
    intro completion member
    have filtered := List.mem_filter.mp member
    have selected := of_decide_eq_true filtered.2
    obtain ⟨action, chosen⟩ := Option.isSome_iff_exists.mp selected.2
    have ownerLaw := decodeEventAction_owner whole completion.event action
    rw [eventOwner?_eq_actor whole completion.event, selected.1] at ownerLaw
    cases decoded : decodeEventAction whole completion.event action with
    | none => simp [decoded] at ownerLaw
    | some sourceAction => exact ⟨action, sourceAction, chosen, decoded⟩
  have noDefault : ∀ completion ∈ own, completion.defaultEvent = none := by
    intro completion member
    have filtered := List.mem_filter.mp member
    exact reachable.owned_defaultEvent_eq_none_of_active who active completion filtered.1
      (of_decide_eq_true filtered.2).1
  have historyEncoded : encodeCompletions? whole
      (graph.prefixSchema.ownHistory event) (decodeCompletions whole own) = some own := by
    have reconstructed := encodeCompletions?_decodeCompletions_eq_some whole own
      strategic noDefault
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
  · exact (compiled_history_eq_prefix whole reachable offset ordered event rank).symm
  · exact storeEq
  · rfl
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
      (fun same view _active =>
          have actor : (toEventGraph whole).actor? event = some who := by
            simpa [event, headIndex, eventOwner?, same] using actorEq headIndex
          match encodeDecisionView? whole refs who event view with
          | none => PMF.pure none
          | some observation =>
              if observedActive : who ∉ observation.defaulted then
                (policy event actor observation observedActive).map embedding.commitHeadAction
              else PMF.pure none,
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
      (fun same view _active =>
          have actor : (toEventGraph whole).actor? event = some who := by
            simpa [event, headIndex, eventOwner?, same] using actorEq headIndex
          match encodeDecisionView? whole refs who event view with
          | none => PMF.pure false
          | some observation =>
              if observedActive : who ∉ observation.defaulted then
                (policy event actor observation observedActive).map embedding.revealHeadAction
              else PMF.pure false,
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
    (active : who ∉ view.defaulted) (observation : (toEventGraph whole).PlayerObservation who)
    (encoded : encodeDecisionView? whole refs who
      (embedding.event ⟨0, by simp [eventCount]⟩) view = some observation)
    (observedActive : who ∉ observation.defaulted) :
    (backtranslatePolicyTable whole who policy
        (.commit name owner fresh guard next) refs embedding actorEq).1
        same view active =
      (policy (embedding.event ⟨0, by simp [eventCount]⟩)
        (by simpa [eventOwner?, same] using actorEq ⟨0, by simp [eventCount]⟩)
        observation observedActive).map embedding.commitHeadAction := by
  simp only [backtranslatePolicyTable, encoded, dite_eq_left observedActive]

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
    (active : who ∉ view.defaulted) (observation : (toEventGraph whole).PlayerObservation who)
    (encoded : encodeDecisionView? whole refs who
      (embedding.event ⟨0, by simp [eventCount]⟩) view = some observation)
    (observedActive : who ∉ observation.defaulted) :
    (backtranslatePolicyTable whole who policy
        (.reveal published owner name fresh selected unresolved next) refs
        embedding actorEq).1 same view active =
      (policy (embedding.event ⟨0, by simp [eventCount]⟩)
        (by simpa [eventOwner?, same] using actorEq ⟨0, by simp [eventCount]⟩)
        observation observedActive).map embedding.revealHeadAction := by
  simp only [backtranslatePolicyTable, encoded, dite_eq_left observedActive]

end Vegas
