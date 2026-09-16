/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Execution

/-! # Event-graph information projections

Actual observations retain chronological completion metadata and a player's
original supplied actions. Store projections hide foreign bindings without
hiding public data or publication results. Logical decision schemas are a
separate, smaller interface used by prescribed policy compilers.
-/

noncomputable section

namespace Vegas

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

namespace EventGraph

namespace EventField

/-- Fields visible to a player: all public fields and that player's bindings. -/
def VisibleTo (who : Player) : EventField Player L → Prop
  | .publicData _ | .publication _ => True
  | .binding owner _ => owner = who

/-- Fields visible to a public scheduler. -/
def IsPublic : EventField Player L → Prop
  | .publicData _ | .publication _ => True
  | .binding _ _ => False

instance (who : Player) (field : EventField Player L) : Decidable (field.VisibleTo who) := by
  cases field <;> simp only [VisibleTo] <;> infer_instance

instance (field : EventField Player L) : Decidable field.IsPublic := by
  cases field <;> simp only [IsPublic] <;> infer_instance

end EventField

variable (graph : Vegas.EventGraph Player L)

/-- The player owning a strategic event. Samples have no player owner. -/
def actor? (event : graph.EventId) : Option Player :=
  EventCode.actor (graph.nodes event)

/-- Whether a field is visible to a given player. -/
def fieldVisibleTo (who : Player) (field : graph.Field) : Prop :=
  (graph.layout field).VisibleTo who

/-- Whether a field is public. -/
def fieldPublic (field : graph.Field) : Prop :=
  (graph.layout field).IsPublic

instance (who : Player) (field : graph.Field) : Decidable (graph.fieldVisibleTo who field) :=
  by unfold fieldVisibleTo; infer_instance

instance (field : graph.Field) : Decidable (graph.fieldPublic field) :=
  by unfold fieldPublic; infer_instance

/-- Mask a partial store to public fields and the player's own bindings. -/
def playerStore (who : Player) (store : EventGraph.Store graph.layout) :
    EventGraph.Store graph.layout :=
  fun field => if graph.fieldVisibleTo who field then store field else none

/-- Mask a partial store to public fields only. -/
def publicStore (store : EventGraph.Store graph.layout) : EventGraph.Store graph.layout :=
  fun field => if graph.fieldPublic field then store field else none

@[simp] theorem playerStore_of_visible (who : Player) (store : EventGraph.Store graph.layout)
    (field : graph.Field) (visible : graph.fieldVisibleTo who field) :
    graph.playerStore who store field = store field := by
  simp [playerStore, visible]

@[simp] theorem playerStore_of_hidden (who : Player) (store : EventGraph.Store graph.layout)
    (field : graph.Field) (hidden : ¬ graph.fieldVisibleTo who field) :
    graph.playerStore who store field = none := by
  simp [playerStore, hidden]

omit [DecidableEq Player] in
@[simp] theorem publicStore_of_public (store : EventGraph.Store graph.layout)
    (field : graph.Field) (isPublic : graph.fieldPublic field) :
    graph.publicStore store field = store field := by
  simp [publicStore, isPublic]

omit [DecidableEq Player] in
@[simp] theorem publicStore_of_private (store : EventGraph.Store graph.layout)
    (field : graph.Field) (isPrivate : ¬ graph.fieldPublic field) :
    graph.publicStore store field = none := by
  simp [publicStore, isPrivate]

/-- Player projections depend only on fields visible to that player. -/
theorem playerStore_congr (who : Player) (left right : EventGraph.Store graph.layout)
    (agree : ∀ field, graph.fieldVisibleTo who field → left field = right field) :
    graph.playerStore who left = graph.playerStore who right := by
  funext field
  by_cases visible : graph.fieldVisibleTo who field
  · simp [playerStore, visible, agree field visible]
  · simp [playerStore, visible]

omit [DecidableEq Player] in
/-- Scheduler projections depend only on public fields. -/
theorem publicStore_congr (left right : EventGraph.Store graph.layout)
    (agree : ∀ field, graph.fieldPublic field → left field = right field) :
    graph.publicStore left = graph.publicStore right := by
  funext field
  by_cases isPublic : graph.fieldPublic field
  · simp [publicStore, isPublic, agree field isPublic]
  · simp [publicStore, isPublic]

/-- A foreign binding is absent from a player's projected store. -/
theorem playerStore_foreign_binding (who owner : Player) (different : owner ≠ who)
    (store : EventGraph.Store graph.layout) (field : graph.Field) {payload : L.Ty}
    (binding : graph.layout field = .binding owner payload) :
    graph.playerStore who store field = none := by
  apply playerStore_of_hidden
  unfold fieldVisibleTo
  rw [binding]
  simpa [EventField.VisibleTo] using different

/-- A typed reference to a player-visible field reads the same value from the
player's actual masked observation as from the semantic store. -/
theorem FieldRef.get?_playerStore {graph : Vegas.EventGraph Player L}
    {kind : EventField Player L} (ref : FieldRef graph.layout kind)
    (who : Player) (store : EventGraph.Store graph.layout) (visible : kind.VisibleTo who) :
    ref.get? (graph.playerStore who store) = ref.get? store := by
  apply ref.get?_congr
  apply graph.playerStore_of_visible
  change (graph.layout ref.field).VisibleTo who
  rw [ref.layout_eq]
  exact visible

omit [DecidableEq Player] in
/-- Every binding is absent from the public scheduler's projected store. -/
theorem publicStore_binding (store : EventGraph.Store graph.layout)
    (field : graph.Field) (owner : Player) {payload : L.Ty}
    (binding : graph.layout field = .binding owner payload) :
    graph.publicStore store field = none := by
  apply publicStore_of_private
  unfold fieldPublic
  rw [binding]
  simp [EventField.IsPublic]

/-- Chronological actions supplied by one player. Filtering retains the
dependent action itself, rather than attempting to reconstruct it from the
event's possibly failed output. -/
def ownCompletions (who : Player) (history : List graph.Completion) :
    List graph.Completion :=
  history.filter fun completion => graph.actor? completion.event = some who

/-- Completing a field hidden from a player leaves that player's entire store
projection unchanged. The public completion order still changes. -/
theorem playerStore_complete_of_hidden (who : Player) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (hidden : ¬ graph.fieldVisibleTo who (.inr event)) :
    graph.playerStore who (config.complete event ready action value).store =
      graph.playerStore who config.store := by
  funext field
  by_cases visible : graph.fieldVisibleTo who field
  · simp only [playerStore, if_pos visible]
    cases field with
    | inl input => rfl
    | inr query =>
        have different : query ≠ event := by
          intro same
          subst query
          exact hidden visible
        exact config.complete_output_of_ne event query ready action value different
  · simp only [playerStore, if_neg visible]

/-- Another actor's completion does not change the player's original-action
recall, regardless of the result written by that event. -/
theorem ownCompletions_complete_of_not_actor (who : Player) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (notOwned : graph.actor? event ≠ some who) :
    graph.ownCompletions who (config.complete event ready action value).history =
      graph.ownCompletions who config.history := by
  simp [Config.complete_history, ownCompletions, notOwned]

/-- The public scheduler observes public store contents and completion order. -/
structure PublicObservation where
  completionOrder : List graph.EventId
  store : EventGraph.Store graph.layout

namespace PublicObservation

omit [DecidableEq Player] in
@[ext] theorem ext {left right : graph.PublicObservation}
    (completionOrder : left.completionOrder = right.completionOrder)
    (store : left.store = right.store) : left = right := by
  cases left
  cases right
  cases completionOrder
  cases store
  rfl

end PublicObservation

/-- A player observes public and own-private store contents, completion order,
and its original supplied strategic actions. -/
structure PlayerObservation (who : Player) where
  completionOrder : List graph.EventId
  store : EventGraph.Store graph.layout
  ownActions : List graph.Completion

namespace PlayerObservation

omit [DecidableEq Player] in
@[ext] theorem ext {who : Player} {left right : graph.PlayerObservation who}
    (completionOrder : left.completionOrder = right.completionOrder)
    (store : left.store = right.store)
    (ownActions : left.ownActions = right.ownActions) : left = right := by
  cases left
  cases right
  cases completionOrder
  cases store
  cases ownActions
  rfl

end PlayerObservation

/-- Actual public observation of a coherent execution configuration. -/
def publicObserve (config : graph.Config) : graph.PublicObservation where
  completionOrder := config.history.map Completion.event
  store := graph.publicStore config.store

/-- Actual player observation of a coherent execution configuration. -/
def playerObserve (who : Player) (config : graph.Config) : graph.PlayerObservation who where
  completionOrder := config.history.map Completion.event
  store := graph.playerStore who config.store
  ownActions := graph.ownCompletions who config.history

omit [DecidableEq Player] in
@[simp] theorem publicObserve_completionOrder (config : graph.Config) :
    (graph.publicObserve config).completionOrder = config.history.map Completion.event := rfl

@[simp] theorem playerObserve_completionOrder (who : Player) (config : graph.Config) :
    (graph.playerObserve who config).completionOrder =
      config.history.map Completion.event := rfl

@[simp] theorem playerObserve_ownActions (who : Player) (config : graph.Config) :
    (graph.playerObserve who config).ownActions = graph.ownCompletions who config.history := rfl

omit [DecidableEq Player] in
/-- Public observations agree when chronological histories and public fields
agree. In particular, private bindings cannot affect this observation. -/
theorem publicObserve_congr (left right : graph.Config)
    (history : left.history = right.history)
    (stores : ∀ field, graph.fieldPublic field → left.store field = right.store field) :
    graph.publicObserve left = graph.publicObserve right := by
  have orderEq : left.history.map Completion.event =
      right.history.map Completion.event := congrArg _ history
  have storeEq := graph.publicStore_congr left.store right.store stores
  exact PublicObservation.ext graph orderEq storeEq

/-- Player observations agree when chronological histories and all fields
visible to that player agree. Foreign bindings need not agree. -/
theorem playerObserve_congr (who : Player) (left right : graph.Config)
    (history : left.history = right.history)
    (stores : ∀ field,
      graph.fieldVisibleTo who field → left.store field = right.store field) :
    graph.playerObserve who left = graph.playerObserve who right := by
  have orderEq : left.history.map Completion.event =
      right.history.map Completion.event := congrArg _ history
  have storeEq := graph.playerStore_congr who left.store right.store stores
  have actionsEq : graph.ownCompletions who left.history =
      graph.ownCompletions who right.history := congrArg _ history
  exact PlayerObservation.ext graph orderEq storeEq actionsEq

/-- A declared logical decision interface. It deliberately omits actual
completion-order metadata. -/
structure LogicalSchema where
  fields : graph.EventId → Finset graph.Field
  ownHistory : graph.EventId → List graph.EventId

/-- Restrict a partial store to a declared finite field set. -/
def restrictStore (fields : Finset graph.Field) (store : EventGraph.Store graph.layout) :
    EventGraph.Store graph.layout :=
  fun field => if field ∈ fields then store field else none

/-- Select the supplied own actions declared by one decision schema, preserving
their actual chronological order and their dependent action payloads. -/
def declaredOwnActions (schema : graph.LogicalSchema) (event : graph.EventId)
    (history : List graph.Completion) : List graph.Completion :=
  history.filter fun completion => completion.event ∈ schema.ownHistory event

/-- The logical observation consumed by a prescribed policy compiler. -/
structure LogicalObservation where
  store : EventGraph.Store graph.layout
  ownActions : List graph.Completion

/-- Project an actual player observation to a declared logical interface. -/
def logicalObserve (schema : graph.LogicalSchema) (event : graph.EventId)
    (who : Player) (observation : graph.PlayerObservation who) :
    graph.LogicalObservation where
  store := graph.restrictStore (schema.fields event) observation.store
  ownActions := graph.declaredOwnActions schema event observation.ownActions

/-- Availability of a graph field at a completed cut. Inputs are initially
available; an output is available exactly when its producer is complete. -/
def FieldAvailable (cut : graph.order.Cut) : graph.Field → Prop
  | .inl _ => True
  | .inr producer => producer ∈ cut.completed

instance (cut : graph.order.Cut) (field : graph.Field) :
    Decidable (graph.FieldAvailable cut field) := by
  cases field <;> simp only [FieldAvailable] <;> infer_instance

omit [DecidableEq Player] in
/-- Configuration stores have exactly the field domain described by their
completed cut. -/
theorem Config.store_isSome_iff_fieldAvailable (config : graph.Config)
    (field : graph.Field) :
    (config.store field).isSome ↔ graph.FieldAvailable config.cut field := by
  cases field with
  | inl input => simp [Config.store, FieldAvailable]
  | inr event => simpa [Config.store, FieldAvailable] using config.output_available event

/-- All fields actually visible to a player at a cut. -/
def visibleFields (who : Player) (cut : graph.order.Cut) : Finset graph.Field :=
  Finset.univ.filter fun field =>
    graph.FieldAvailable cut field ∧ graph.fieldVisibleTo who field

/-- Completed strategic events owned by a player. -/
def completedOwnEvents (who : Player) (cut : graph.order.Cut) :
    Finset graph.EventId :=
  cut.completed.filter fun event => graph.actor? event = some who

/-- A source-independent information certificate for logical decision schemas.
It rules out early public or same-owner information at every ready strategic
cut, while allowing foreign hidden bindings and chronological metadata to vary. -/
structure InformationDiscipline (schema : graph.LogicalSchema) : Prop where
  fields_visible : ∀ event who,
    graph.actor? event = some who → ∀ field, field ∈ schema.fields event →
      graph.fieldVisibleTo who field
  fields_causal : ∀ event field, field ∈ schema.fields event →
    match field with
    | .inl _ => True
    | .inr producer => producer ∈ graph.order.predecessors event
  ready_fields_exact : ∀ cut event who,
    cut.Ready event → graph.actor? event = some who →
      graph.visibleFields who cut = schema.fields event
  own_history_ranked : ∀ event, (schema.ownHistory event).Pairwise fun left right =>
    left.val < right.val
  own_history_owned : ∀ event who,
    graph.actor? event = some who → ∀ prior, prior ∈ schema.ownHistory event →
      graph.actor? prior = some who
  own_history_causal : ∀ event prior, prior ∈ schema.ownHistory event →
    prior ∈ graph.order.predecessors event
  ready_own_history_exact : ∀ cut event who,
    cut.Ready event → graph.actor? event = some who →
      (schema.ownHistory event).toFinset = graph.completedOwnEvents who cut
  same_owner_ordered : ∀ {earlier later who}, earlier.val < later.val →
    graph.actor? earlier = some who → graph.actor? later = some who →
      earlier ∈ graph.order.predecessors later

namespace InformationDiscipline

variable {graph : Vegas.EventGraph Player L} {schema : graph.LogicalSchema}

/-- At a ready strategic event, restricting the actual player store to the
declared logical fields removes no visible value. Early public information and
undeclared own bindings are excluded by `ready_fields_exact`. -/
theorem logicalObserve_store (discipline : graph.InformationDiscipline schema)
    (config : graph.Config) (event : graph.EventId) (who : Player)
    (ready : config.cut.Ready event) (actor : graph.actor? event = some who) :
    (graph.logicalObserve schema event who (graph.playerObserve who config)).store =
      (graph.playerObserve who config).store := by
  funext field
  have fieldsExact := discipline.ready_fields_exact config.cut event who ready actor
  have membership : field ∈ schema.fields event ↔
      graph.FieldAvailable config.cut field ∧ graph.fieldVisibleTo who field := by
    rw [← fieldsExact]
    simp [visibleFields]
  by_cases declared : field ∈ schema.fields event
  · simp [logicalObserve, restrictStore, declared]
  · rw [show (graph.logicalObserve schema event who
        (graph.playerObserve who config)).store field = none by
        simp [logicalObserve, restrictStore, declared]]
    rw [membership] at declared
    by_cases visible : graph.fieldVisibleTo who field
    · have unavailable : ¬ graph.FieldAvailable config.cut field := by
        exact fun available => declared ⟨available, visible⟩
      have absent : config.store field = none :=
        Option.not_isSome_iff_eq_none.mp (by
          simpa [Config.store_isSome_iff_fieldAvailable] using unavailable)
      simp [playerObserve, playerStore, visible, absent]
    · simp [playerObserve, playerStore, visible]

/-- At a ready strategic event, selecting declared own actions filters no
actual own completion out. Original dependent actions, including a resolving
`true` whose output failed, are retained verbatim. -/
theorem logicalObserve_ownActions
    (discipline : graph.InformationDiscipline schema)
    (config : graph.Config) (event : graph.EventId) (who : Player)
    (ready : config.cut.Ready event) (actor : graph.actor? event = some who) :
    (graph.logicalObserve schema event who (graph.playerObserve who config)).ownActions =
      (graph.playerObserve who config).ownActions := by
  unfold logicalObserve playerObserve declaredOwnActions
  apply List.filter_eq_self.mpr
  intro completion member
  have memberFiltered := List.mem_filter.mp member
  have inHistory : completion.event ∈ config.history.map Completion.event := by
    exact List.mem_map.mpr ⟨completion, memberFiltered.1, rfl⟩
  have completed : completion.event ∈ config.cut.completed :=
    (config.history_exact completion.event).mp inHistory
  have owned : graph.actor? completion.event = some who :=
    of_decide_eq_true memberFiltered.2
  have inOwned : completion.event ∈ graph.completedOwnEvents who config.cut := by
    simp [completedOwnEvents, completed, owned]
  have exactHistory := discipline.ready_own_history_exact config.cut event who ready actor
  rw [← exactHistory] at inOwned
  simpa using inOwned

end InformationDiscipline

end EventGraph

end Vegas
