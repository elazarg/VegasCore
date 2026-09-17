/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Validation
import Interaction.CommitmentCandidates
import Interaction.MessageApplication

/-! # Event-addressed pending-message application

This is the source-independent runtime core for one fixed `EventGraph`.
Packets address stable events, readiness comes from the graph cut, and each
strategic event has its own activation time. Candidate meanings and remembered
actions are private semantic state; public views expose only handles and the
graph's public observation.
-/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Deadline parameters for one fixed event graph. -/
structure EventGraphRuntime (graph : Vegas.EventGraph Player L) where
  deadline : graph.EventId → Nat

namespace EventGraphRuntime

/-- Dynamically typed wire data. The type tag is public; its candidate meaning
remains in the private commitment catalogue until an opening is submitted. -/
structure Raw (L : IExpr) where
  ty : L.Ty
  value : L.Val ty

namespace Raw

def as? (raw : Raw L) (payload : L.Ty) : Option (L.Val payload) :=
  if same : raw.ty = payload then
    some (cast (congrArg L.Val same) raw.value)
  else none

omit R in
@[simp] theorem as?_mk (payload : L.Ty) (value : L.Val payload) :
    (Raw.mk payload value).as? payload = some value := by
  simp [as?]

end Raw

instance : DecidableEq (Raw L) := fun left right =>
  if typeEq : left.ty = right.ty then
    match left, right, typeEq with
    | ⟨payload, leftValue⟩, ⟨_, rightValue⟩, rfl =>
        if valueEq : leftValue = rightValue then
          isTrue (by cases valueEq; rfl)
        else isFalse (by intro same; cases same; exact valueEq rfl)
  else isFalse (by intro same; exact typeEq (congrArg Raw.ty same))

/-- Initial handles are stable input identities. Prepared slots remain
principal-local and allow arbitrary policies to create competing candidates. -/
inductive Slot (inputCount : Nat) where
  | initial (input : Fin inputCount)
  | prepared (serial : Nat)
  deriving DecidableEq

abbrev CandidateSlot (graph : Vegas.EventGraph Player L) := Slot graph.inputCount
abbrev Handle (graph : Vegas.EventGraph Player L) :=
  CommitmentHandle Player (CandidateSlot graph)

/-- Publicly accepted handles are indexed by graph field identity, not source
names. Non-binding fields permanently carry `none`. -/
abbrev AcceptedHandles (graph : Vegas.EventGraph Player L) :=
  graph.Field → Option (Handle graph)

/-- Private sample-once memory. The public application transition never
exposes this table. -/
abbrev RememberedActions (graph : Vegas.EventGraph Player L) :=
  (event : graph.EventId) → Option (graph.Action event)

/-- Runtime application state. `config` is the semantic EventGraph state; its
binding values and original actions are exposed only through graph projections. -/
structure State (graph : Vegas.EventGraph Player L) where
  config : graph.Config
  accepted : AcceptedHandles graph
  candidates : CommitmentCandidates Player (CandidateSlot graph) (Raw L)
  remembered : RememberedActions graph
  clock : Nat
  activatedAt : graph.EventId → Option Nat
  /-- Public service request; it does not restrict packet submission or acceptance. -/
  serviceGrant : Option graph.EventId

/-- Public application projection. Candidate meanings, hidden binding values,
and remembered actions are absent. -/
structure PublicView (graph : Vegas.EventGraph Player L) where
  observation : graph.PublicObservation
  accepted : AcceptedHandles graph
  clock : Nat
  activatedAt : graph.EventId → Option Nat
  serviceGrant : Option graph.EventId

/-- Authenticated player projection. Unfinished remembered choices and this
player's candidate catalogue are private additions to `playerObserve`. -/
structure PlayerView (graph : Vegas.EventGraph Player L) where
  who : Player
  publicView : PublicView graph
  observation : graph.PlayerObservation who
  remembered : (event : graph.EventId) → Option (graph.Action event)
  candidates : CandidateSlot graph → CommitmentCandidate (Raw L)

/-- Public packets retain malformed, premature, replayed, and competing
traffic in the shared message pool even when inclusion has no state effect. -/
inductive Payload (graph : Vegas.EventGraph Player L) where
  | commitment (event : graph.EventId) (handle : Handle graph)
  | opening (event : graph.EventId) (handle : Handle graph) (raw : Raw L)
  | withhold (event : graph.EventId)
  | malformed (raw : Raw L)

namespace Payload

/-- Stable event address carried by every well-formed application packet. -/
def event? (graph : Vegas.EventGraph Player L) : Payload graph → Option graph.EventId
  | .commitment event _ => some event
  | .opening event _ _ => some event
  | .withhold event => some event
  | .malformed _ => none

end Payload

/-- Authenticated private actions prepare arbitrary candidates or remember a
typed graph action. Remembering is first-write and owner-checked. -/
inductive PrivateCommand (graph : Vegas.EventGraph Player L) where
  | prepare (serial : Nat) (raw : Raw L)
  | remember (event : graph.EventId) (action : graph.Action event)

/-- Public environment operations are separate: clocks do not automatically
sample or expire events. Expiry tests the current clock. -/
inductive EnvironmentCommand (graph : Vegas.EventGraph Player L) where
  | grant (event : graph.EventId)
  | advanceClock
  | executeSample (event : graph.EventId)
  | expire (event : graph.EventId)

namespace EnvironmentCommand

/-- Number of logical clock ticks contributed by one environment command. -/
def clockTicks {graph : Vegas.EventGraph Player L} : EnvironmentCommand graph → Nat
  | .advanceClock => 1
  | .grant _ | .executeSample _ | .expire _ => 0

end EnvironmentCommand

variable {graph : Vegas.EventGraph Player L}

namespace State

/-- Candidate meaning induced by one typed initial field value for a proposed
owner. Non-binding fields and bindings owned by somebody else stay fresh. -/
def candidateOfValue (owner : Player) :
    (kind : EventField Player L) → kind.Value → CommitmentCandidate (Raw L)
  | .publicData _, _ | .publication _, _ => .fresh
  | .binding inputOwner payload, result =>
      if inputOwner = owner then
        match result with
        | .failure => .unopenable
        | .success value => .openable ⟨payload, value⟩
      else .fresh

omit R in theorem candidateOfValue_binding_success (kind : EventField Player L)
    (input : kind.Value) (owner : Player) (payload : L.Ty)
    (kindEq : kind = .binding owner payload) (value : L.Val payload)
    (success : cast (congrArg EventField.Value kindEq) input =
      PublicationResult.success value) :
    candidateOfValue owner kind input = .openable ⟨payload, value⟩ := by
  subst kind
  change input = PublicationResult.success value at success
  subst input
  simp only [candidateOfValue, ↓reduceIte]

/-- Candidate meaning installed for one initial binding input. -/
private def initialCandidate (inputs : graph.Inputs) (owner : Player)
    (input : graph.InputId) : CommitmentCandidate (Raw L) :=
  candidateOfValue owner (graph.inputLayout input) (inputs input)

private def initialCandidates (inputs : graph.Inputs) :
    CommitmentCandidates Player (CandidateSlot graph) (Raw L) where
  table owner slot := match slot with
    | .initial input => initialCandidate inputs owner input
    | .prepared _ => .fresh

private def initialAccepted : AcceptedHandles graph := fun field =>
  match field with
  | .inr _ => none
  | .inl input =>
      match _kindEq : graph.inputLayout input with
      | .binding owner _ => some (owner, .initial input)
      | .publicData _ | .publication _ => none

/-- Refresh activation metadata after any graph completion. Existing ready
events retain their timestamp; newly ready strategic events receive `clock`. -/
def refreshActivated (config : graph.Config) (clock : Nat)
    (prior : graph.EventId → Option Nat) : graph.EventId → Option Nat :=
  fun event =>
    if _ready : config.cut.Ready event then
      match graph.actor? event with
      | none => none
      | some _ => (prior event).orElse (fun _ => some clock)
    else none

/-- Initialize the semantic graph and install opaque handles for every initial
binding field. Public metadata is independent of initial binding meanings. -/
def initial (inputs : graph.Inputs) : State graph :=
  let config := Vegas.EventGraph.Config.initial (graph := graph) inputs
  { config
    accepted := initialAccepted
    candidates := initialCandidates inputs
    remembered := fun _ => none
    clock := 0
    activatedAt := refreshActivated config 0 (fun _ => none)
    serviceGrant := none }

/-- Initial candidate slots contain precisely the owner-visible typed input;
prepared slots have not yet been allocated. -/
theorem initial_candidate (inputs : graph.Inputs) (owner : Player)
    (slot : CandidateSlot graph) :
    (initial inputs).candidates.lookup (owner, slot) =
      match slot with
      | .initial input => candidateOfValue owner (graph.inputLayout input) (inputs input)
      | .prepared _ => .fresh := by
  cases slot <;> rfl

/-- Every initially accepted handle is the canonical opaque handle of one
typed binding input. Event outputs have no accepted handle initially. -/
theorem initial_accepted_eq_some (inputs : graph.Inputs) (field : graph.Field)
    (handle : Handle graph) (accepted : (initial inputs).accepted field = some handle) :
    ∃ (input : graph.InputId) (owner : Player) (payload : L.Ty),
      field = .inl input ∧ graph.inputLayout input = .binding owner payload ∧
        handle = (owner, .initial input) := by
  cases field with
  | inr event => simp [initial, initialAccepted] at accepted
  | inl input =>
      change initialAccepted (.inl input) = some handle at accepted
      unfold initialAccepted at accepted
      dsimp only at accepted
      generalize kindEq : graph.inputLayout input = kind at accepted
      cases kind with
      | publicData payload => simp at accepted
      | publication payload => simp at accepted
      | binding owner payload =>
          have handleEq : handle = (owner, .initial input) :=
            Option.some.inj accepted.symm
          exact ⟨input, owner, payload, rfl, kindEq, handleEq⟩

/-- Initial accepted handles are injective across typed graph fields. -/
theorem initial_accepted_injective (inputs : graph.Inputs)
    (left right : graph.Field) (handle : Handle graph)
    (leftAccepted : (initial inputs).accepted left = some handle)
    (rightAccepted : (initial inputs).accepted right = some handle) : left = right := by
  obtain ⟨leftInput, leftOwner, leftPayload, rfl, _, leftHandle⟩ :=
    initial_accepted_eq_some inputs left handle leftAccepted
  obtain ⟨rightInput, rightOwner, rightPayload, fieldEq, _, rightHandle⟩ :=
    initial_accepted_eq_some inputs right handle rightAccepted
  subst right
  have slotEq : Slot.initial leftInput = Slot.initial rightInput := by
    simpa [leftHandle] using congrArg Prod.snd rightHandle
  cases slotEq
  rfl

/-- A typed initial binding field has its canonical opaque accepted handle. -/
theorem initial_accepted_binding (inputs : graph.Inputs) (input : graph.InputId)
    (owner : Player) (payload : L.Ty)
    (kindEq : graph.inputLayout input = .binding owner payload) :
    (initial inputs).accepted (.inl input) = some (owner, .initial input) := by
  unfold initial initialAccepted
  dsimp only
  rw [kindEq]

/-- A successful typed initial binding value installs that exact immutable
candidate meaning under its canonical opaque handle. -/
theorem initial_candidate_binding_success (inputs : graph.Inputs)
    (input : graph.InputId) (owner : Player) (payload : L.Ty)
    (kindEq : graph.inputLayout input = .binding owner payload)
    (value : L.Val payload)
    (success : cast (congrArg EventField.Value kindEq) (inputs input) =
      PublicationResult.success value) :
    (initial inputs).candidates.lookup (owner, .initial input) =
      .openable ⟨payload, value⟩ := by
  unfold initial initialCandidates CommitmentCandidates.lookup initialCandidate
  dsimp only
  exact candidateOfValue_binding_success (graph.inputLayout input) (inputs input)
    owner payload kindEq value success

def publicView (state : State graph) : PublicView graph where
  observation := graph.publicObserve state.config
  accepted := state.accepted
  clock := state.clock
  activatedAt := state.activatedAt
  serviceGrant := state.serviceGrant

def playerView (state : State graph) (who : Player) : PlayerView graph where
  who
  publicView := state.publicView
  observation := graph.playerObserve who state.config
  remembered := fun event =>
    if graph.actor? event = some who then state.remembered event else none
  candidates := fun slot => state.candidates.lookup (who, slot)

/-- Complete one deterministic event and refresh all event-relative clocks. -/
def complete (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) : State graph :=
  let config := state.config.complete event ready action value
  { state with
    config
    activatedAt := refreshActivated config state.clock state.activatedAt }

/-- No accepted handle may be reused for another binding field. -/
def HandleUnused (state : State graph) (handle : Handle graph) : Prop :=
  ∀ field, state.accepted field ≠ some handle

/-- Typed meaning of a candidate when it is accepted at a binding event.
Fresh, unopenable, and wrong-typed candidates all produce binding failure. -/
def bindingResult (state : State graph) (handle : Handle graph) (payload : L.Ty) :
    PublicationResult (L.Val payload) :=
  match state.candidates.lookup handle with
  | .openable raw => (raw.as? payload).elim .failure .success
  | .fresh | .unopenable => .failure

/-- Packet inclusion is allowed strictly before this event's relative
deadline. Expiry becomes effective at the boundary. -/
def WithinDeadline (runtime : EventGraphRuntime graph) (state : State graph)
    (event : graph.EventId) : Prop :=
  match state.activatedAt event with
  | none => False
  | some entered => state.clock - entered < runtime.deadline event

end State

/-- A private preparation changes only the authenticated candidate catalogue.
Remembering a choice is first-write and restricted to the event's actor. -/
def privateStep (state : State graph) (who : Player) :
    PrivateCommand graph → State graph
  | .prepare serial raw =>
      { state with candidates :=
          state.candidates.prepare who (.prepared serial) raw }
  | .remember event action =>
      if _owned : graph.actor? event = some who then
        match state.remembered event with
        | some _ => state
        | none => { state with remembered := Function.update state.remembered event (some action) }
      else state

/-- Private preparation and choice recall do not alter accepted handles. -/
theorem privateStep_accepted (state : State graph) (who : Player)
    (command : PrivateCommand graph) :
    (privateStep state who command).accepted = state.accepted := by
  cases command with
  | prepare => rfl
  | remember event action =>
      by_cases owned : graph.actor? event = some who
      · rw [privateStep, dif_pos owned]
        cases state.remembered event <;> rfl
      · rw [privateStep, dif_neg owned]

/-- Install a binding handle and complete the bind with the immutable meaning
already associated with that handle. Wrong-typed and unprepared candidates
produce genuine binding failure without changing packet shape. -/
private def acceptBinding (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (handle : Handle graph) :
    State graph := by
  let result := state.bindingResult handle payload
  let action : graph.Action event :=
    cast (congrArg EventField.Action outputEq.symm) result
  let value : (graph.outputLayout event).Value :=
    cast (congrArg EventField.Value outputEq.symm) result
  let next := state.complete event ready action value
  exact { next with
    accepted := Function.update state.accepted (.inr event) (some handle)
    candidates := state.candidates.accept handle }

/-- Complete one resolution through the deterministic evaluator retained by
`EventCode`; no handler-local copy of deferred validation exists. -/
private def acceptResolution (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (disclose : Bool) : Option (State graph) := do
  let result ← EventCode.resolveOutput? binding checks disclose state.config.store
  let action : graph.Action event :=
    cast (congrArg EventField.Action outputEq.symm) disclose
  let value : (graph.outputLayout event).Value :=
    cast (congrArg EventField.Value outputEq.symm) result
  pure (state.complete event ready action value)

/-- Interpret a canonical withholding packet. A privately remembered `true`
is retained only when owner-local prevalidation gives it exactly the canonical
`false` output; otherwise withholding is recorded as the graph action `false`. -/
private def withholdingAction (state : State graph) (event : graph.EventId)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload) : Bool :=
  match state.remembered event with
  | none => false
  | some remembered =>
      match cast (congrArg EventField.Action outputEq) remembered with
      | false => false
      | true =>
          if EventCode.resolveOutput? binding checks true
                (graph.playerStore owner state.config.store) =
              EventCode.resolveOutput? binding checks false
                (graph.playerStore owner state.config.store) then
            true
          else false

omit [DecidableEq Player] in
private theorem State.publicView_complete_action_irrel (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (left right : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    (state.complete event ready left value).publicView =
      (state.complete event ready right value).publicView := by
  unfold State.publicView
  congr 1
  apply PublicObservation.ext graph
  · simp [State.complete, Vegas.EventGraph.publicObserve]
  · rfl

omit [DecidableEq Player] in
private theorem acceptResolution_publicView_congr (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (left right : Bool)
    (resultEq : EventCode.resolveOutput? binding checks left state.config.store =
      EventCode.resolveOutput? binding checks right state.config.store) :
    Option.map State.publicView
        (acceptResolution state event ready owner payload binding checks outputEq left) =
      Option.map State.publicView
        (acceptResolution state event ready owner payload binding checks outputEq right) := by
  cases rightResult : EventCode.resolveOutput? binding checks right state.config.store with
  | none =>
      have leftResult := resultEq.trans rightResult
      simp [acceptResolution, leftResult, rightResult]
  | some value =>
      have leftResult := resultEq.trans rightResult
      simp only [acceptResolution, leftResult, rightResult, bind, pure,
        Option.bind_some, Option.map_some]
      exact congrArg some (state.publicView_complete_action_irrel event ready
        (cast (congrArg EventField.Action outputEq.symm) left)
        (cast (congrArg EventField.Action outputEq.symm) right)
        (cast (congrArg EventField.Value outputEq.symm) value))

private theorem withholdingAction_output (state : State graph)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload) :
    EventCode.resolveOutput? binding checks
        (withholdingAction state event owner payload binding checks outputEq)
        state.config.store =
      EventCode.resolveOutput? binding checks false state.config.store := by
  cases remembered : state.remembered event with
  | none => simp [withholdingAction, remembered]
  | some action =>
      cases actionEq : cast (congrArg EventField.Action outputEq) action with
      | false => simp [withholdingAction, remembered, actionEq]
      | true =>
          simp only [withholdingAction, remembered, actionEq]
          split
          · rename_i localEq
            exact (EventCode.resolveOutput?_playerStore (graph := graph) binding checks
                state.config.store true).symm.trans
              (localEq.trans (EventCode.resolveOutput?_playerStore (graph := graph) binding checks
                state.config.store false))
          · rfl

private theorem acceptBinding_publicView_replaceRemembered (state : State graph)
    (memory : RememberedActions graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (handle : Handle graph) :
    State.publicView (acceptBinding { state with remembered := memory }
        event ready owner payload outputEq handle) =
      State.publicView (acceptBinding state event ready owner payload outputEq handle) := by
  rfl

omit [DecidableEq Player] in
private theorem acceptResolution_publicView_replaceRemembered (state : State graph)
    (memory : RememberedActions graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload) (disclose : Bool) :
    Option.map State.publicView
        (acceptResolution { state with remembered := memory }
          event ready owner payload binding checks outputEq disclose) =
      Option.map State.publicView
        (acceptResolution state event ready owner payload binding checks
          outputEq disclose) := by
  cases result : EventCode.resolveOutput? binding checks disclose state.config.store with
  | none => simp [acceptResolution, result]
  | some value =>
      simp only [acceptResolution, result, bind, pure, Option.bind_some,
        Option.map_some]
      rfl

/-- A node viewed through its output field. This performs the dependent
transport from `Vegas.EventGraph.nodes` once, so every handler sees the same typed
constructor data. -/
inductive NodeView (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) where
  | bind (owner : Player) (payload : L.Ty)
      (outputEq : graph.outputLayout event = .binding owner payload)
      (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
        (graph.nodes event) = .bind owner payload)
  | resolve (owner : Player) (payload : L.Ty)
      (binding : FieldRef graph.layout (.binding owner payload))
      (checks : List (GuardCheck graph.layout payload))
      (outputEq : graph.outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
        (graph.nodes event) = .resolve owner payload binding checks)
  | sample (payload : L.Ty) (law : PublicDist graph.layout payload)
      (outputEq : graph.outputLayout event = .publicData payload)
      (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
        (graph.nodes event) = .sample payload law)

def nodeView (graph : Vegas.EventGraph Player L)
    (event : graph.EventId) : NodeView graph event :=
  match outputEq : graph.outputLayout event with
  | .binding owner payload =>
      let code : EventCode graph.layout (.binding owner payload) :=
        cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event)
      match codeEq : code with
      | .bind _ _ => .bind owner payload outputEq codeEq
  | .publication payload =>
      let code : EventCode graph.layout (.publication payload) :=
        cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event)
      match codeEq : code with
      | .resolve owner _ binding checks =>
          .resolve owner payload binding checks outputEq codeEq
  | .publicData payload =>
      let code : EventCode graph.layout (.publicData payload) :=
        cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event)
      match codeEq : code with
      | .sample _ law => .sample payload law outputEq codeEq

omit [DecidableEq Player] in
private theorem bind_complete_mem_step (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (result : PublicationResult (L.Val payload)) :
    state.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) result)
        (cast (congrArg EventField.Value outputEq.symm) result) ∈
      (state.config.step event ready
        (cast (congrArg EventField.Action outputEq.symm) result)).support := by
  rw [state.config.step_eq_map_of_code event ready outputEq (.bind owner payload)
    codeEq result (FinDist.pure result) rfl]
  simp

omit [DecidableEq Player] in
private theorem resolve_complete_mem_step (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (disclose : Bool) (result : PublicationResult (L.Val payload))
    (resultEq : EventCode.resolveOutput? binding checks disclose state.config.store =
      some result) :
    state.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) disclose)
        (cast (congrArg EventField.Value outputEq.symm) result) ∈
      (state.config.step event ready
        (cast (congrArg EventField.Action outputEq.symm) disclose)).support := by
  rw [state.config.step_eq_map_of_code event ready outputEq
    (.resolve owner payload binding checks) codeEq disclose
    (FinDist.pure result)]
  · simp
  · rw [EventCode.resolve_eval?, resultEq]
    rfl

omit [DecidableEq Player] in
private theorem resolveOutput?_false_eq_failure_of_ready (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks) :
    EventCode.resolveOutput? binding checks false state.config.store = some .failure := by
  apply EventCode.resolveOutput?_false_eq_failure binding checks state.config.store
  intro field read
  apply state.config.read_available ready
  have readsEq : (graph.nodes event).readFields =
      insert binding.field (GuardCheck.listReadFields checks) := by
    calc
      (graph.nodes event).readFields =
          (cast (congrArg (EventCode graph.layout) outputEq)
            (graph.nodes event)).readFields :=
        (EventCode.readFields_cast outputEq (graph.nodes event)).symm
      _ = (EventCode.resolve owner payload binding checks).readFields :=
        congrArg EventCode.readFields codeEq
      _ = insert binding.field (GuardCheck.listReadFields checks) := rfl
  rw [readsEq]
  exact read

/-- Event-addressed packet inclusion. Rejected packets remain observable in
the shared message pool and receipt history, but this function changes no
application state for them. -/
def handle (runtime : EventGraphRuntime graph) (state : State graph)
    (message : Message Player (Payload graph)) : Option (State graph) := by
  classical
  exact match message.payload with
  | .malformed _ => none
  | .commitment event handle =>
      if ready : state.config.cut.Ready event then
        if timely : state.WithinDeadline runtime event then
          match nodeView graph event with
          | .bind owner payload outputEq _codeEq =>
              if sender : message.sender = owner then
                if handleOwner : handle.1 = owner then
                  if vacant : state.accepted (.inr event) = none then
                    if unused : state.HandleUnused handle then
                      some (acceptBinding state event ready owner payload outputEq handle)
                    else none
                  else none
                else none
              else none
          | .resolve .. | .sample .. => none
        else none
      else none
  | .opening event handle raw =>
      if ready : state.config.cut.Ready event then
        if timely : state.WithinDeadline runtime event then
          match nodeView graph event with
          | .resolve owner payload binding checks outputEq _codeEq =>
              if sender : message.sender = owner then
                if handleOwner : handle.1 = owner then
                  if associated : state.accepted binding.field = some handle then
                    if verified : state.candidates.verify handle raw then
                      match typed : raw.as? payload with
                      | none => none
                      | some value =>
                          if stored : binding.get? state.config.store = some (.success value) then
                            acceptResolution state event ready owner payload binding checks
                              outputEq true
                          else none
                    else none
                  else none
                else none
              else none
          | .bind .. | .sample .. => none
        else none
      else none
  | .withhold event =>
      if ready : state.config.cut.Ready event then
        if timely : state.WithinDeadline runtime event then
          match nodeView graph event with
          | .resolve owner payload binding checks outputEq _codeEq =>
              if sender : message.sender = owner then
                let disclose := withholdingAction state event owner payload binding checks outputEq
                acceptResolution state event ready owner payload binding checks outputEq disclose
              else none
          | .bind .. | .sample .. => none
        else none
      else none

/-- A timely authenticated commitment installs its handle and exactly its
typed immutable meaning. The statement includes failed commitments. -/
theorem handle_commitment_eq
    (runtime : EventGraphRuntime graph) (state : State graph)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (view : nodeView graph event = .bind owner payload outputEq codeEq)
    (ready : state.config.cut.Ready event)
    (timely : state.WithinDeadline runtime event)
    (sender : id.1 = owner) (handleOwner : candidate.1 = owner)
    (vacant : state.accepted (.inr event) = none)
    (unused : state.HandleUnused candidate) :
    handle runtime state ⟨id, .commitment event candidate⟩ =
      some { (state.complete event ready
        (cast (congrArg EventField.Action outputEq.symm)
          (state.bindingResult candidate payload))
        (cast (congrArg EventField.Value outputEq.symm)
          (state.bindingResult candidate payload))) with
        accepted := Function.update state.accepted (.inr event) (some candidate)
        candidates := state.candidates.accept candidate } := by
  simp only [handle, dif_pos ready, dif_pos timely, view, Message.sender, sender,
    dif_pos, handleOwner, vacant, unused, acceptBinding]

/-- A verified opening executes the retained graph resolution kernel,
including all deferred checks. No extra validator is introduced here. -/
theorem handle_opening_eq
    (runtime : EventGraphRuntime graph) (state : State graph)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (view : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (ready : state.config.cut.Ready event)
    (timely : state.WithinDeadline runtime event)
    (sender : id.1 = owner) (handleOwner : candidate.1 = owner)
    (associated : state.accepted binding.field = some candidate)
    (value : L.Val payload)
    (verified : state.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (stored : binding.get? state.config.store = some (.success value))
    (result : PublicationResult (L.Val payload))
    (resolved : EventCode.resolveOutput? binding checks true state.config.store = some result) :
    handle runtime state ⟨id, .opening event candidate ⟨payload, value⟩⟩ =
      some (state.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) true)
        (cast (congrArg EventField.Value outputEq.symm) result)) := by
  have verification : state.candidates.verify candidate ⟨payload, value⟩ = true :=
    (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr verified
  simp only [handle, dif_pos ready, dif_pos timely, view, Message.sender, sender,
    dif_pos, handleOwner, associated, verification]
  split
  · rename_i impossible
    simp [Raw.as?] at impossible
  · rename_i decoded typed
    have decodedEq : value = decoded := by
      simpa [Raw.as?] using typed
    subst decoded
    simp [stored, acceptResolution, resolved]

/-- Canonical failure traffic preserves the owner's original disclosure
decision, even when that decision was `true` and local validation rejected it. -/
theorem handle_withhold_eq
    (runtime : EventGraphRuntime graph) (state : State graph)
    (id : MessageId Player) (event : graph.EventId)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (view : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (ready : state.config.cut.Ready event)
    (timely : state.WithinDeadline runtime event)
    (sender : id.1 = owner) (disclose : Bool)
    (remembered : state.remembered event = some
      (cast (congrArg EventField.Action outputEq.symm) disclose))
    (resolved : EventCode.resolveOutput? binding checks disclose state.config.store =
      some .failure) :
    handle runtime state ⟨id, .withhold event⟩ =
      some (state.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) disclose)
        (cast (congrArg EventField.Value outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload)))) := by
  have actionEq : withholdingAction state event owner payload binding checks outputEq =
      disclose := by
    cases disclose with
    | false => simp [withholdingAction, remembered]
    | true =>
        have falseResult := resolveOutput?_false_eq_failure_of_ready state event ready
          owner payload binding checks outputEq codeEq
        have localEq : EventCode.resolveOutput? binding checks true
            (graph.playerStore owner state.config.store) =
          EventCode.resolveOutput? binding checks false
            (graph.playerStore owner state.config.store) := by
          rw [EventCode.resolveOutput?_playerStore, EventCode.resolveOutput?_playerStore,
            resolved, falseResult]
        simp [withholdingAction, remembered, localEq]
  simp [handle, ready, timely, view, Message.sender, sender,
    actionEq, acceptResolution, resolved]

private theorem handle_commitment_config_step
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (accepted : handle runtime state ⟨id, .commitment event candidate⟩ = some next) :
    ∃ (ready : state.config.cut.Ready event) (action : graph.Action event),
      next.config ∈ (state.config.step event ready action).support ∧
        next.clock = state.clock ∧
        next.activatedAt = State.refreshActivated next.config state.clock state.activatedAt ∧
        next.remembered = state.remembered ∧ next.serviceGrant = state.serviceGrant := by
  by_cases ready : state.config.cut.Ready event
  · by_cases timely : state.WithinDeadline runtime event
    · cases view : nodeView graph event with
      | resolve owner payload binding checks outputEq codeEq =>
          simp [handle, ready, timely, view] at accepted
      | sample payload law outputEq codeEq =>
          simp [handle, ready, timely, view] at accepted
      | bind owner payload outputEq codeEq =>
          simp only [handle, dif_pos ready, dif_pos timely, view] at accepted
          split at accepted
          · simp_all only [dite_eq_ite, Option.ite_none_right_eq_some,
              Option.some.injEq, exists_true_left]
            rcases accepted with ⟨ownerEq, vacant, unused, rfl⟩
            let result : PublicationResult (L.Val payload) :=
              match state.candidates.lookup candidate with
              | .openable raw => (raw.as? payload).elim .failure .success
              | .fresh | .unopenable => .failure
            refine ⟨cast (congrArg EventField.Action outputEq.symm) result, ?_⟩
            exact ⟨bind_complete_mem_step state event ready owner payload outputEq codeEq result,
              rfl, rfl, rfl, rfl⟩
          · simp_all only [reduceCtorEq]
    · simp [handle, ready, timely] at accepted
  · simp [handle, ready] at accepted

private theorem handle_opening_config_step
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (raw : Raw L)
    (accepted : handle runtime state ⟨id, .opening event candidate raw⟩ = some next) :
    ∃ (ready : state.config.cut.Ready event) (action : graph.Action event),
      next.config ∈ (state.config.step event ready action).support ∧
        next.clock = state.clock ∧
        next.activatedAt = State.refreshActivated next.config state.clock state.activatedAt ∧
        next.remembered = state.remembered ∧ next.serviceGrant = state.serviceGrant := by
  by_cases ready : state.config.cut.Ready event
  · by_cases timely : state.WithinDeadline runtime event
    · cases view : nodeView graph event with
      | bind owner payload outputEq codeEq =>
          simp [handle, ready, timely, view] at accepted
      | sample payload law outputEq codeEq =>
          simp [handle, ready, timely, view] at accepted
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [handle, dif_pos ready, dif_pos timely, view] at accepted
          split at accepted
          · simp_all only [dite_eq_ite, Option.ite_none_right_eq_some,
              exists_true_left]
            rcases accepted with ⟨ownerEq, associated, verified, accepted⟩
            split at accepted
            · simp at accepted
            · rename_i value typed
              by_cases stored :
                  binding.get? state.config.store = some (.success value)
              · simp only [stored, if_pos] at accepted
                unfold acceptResolution at accepted
                cases resultEq : EventCode.resolveOutput? binding checks true
                    state.config.store with
                | none =>
                    simp only [resultEq, Option.pure_def, Option.bind_eq_bind,
                      Option.bind_none, reduceCtorEq] at accepted
                | some result =>
                    simp only [resultEq, Option.pure_def, Option.bind_eq_bind,
                      Option.bind_some, Option.some.injEq] at accepted
                    subst next
                    refine ⟨cast (congrArg EventField.Action outputEq.symm) true, ?_⟩
                    exact ⟨resolve_complete_mem_step state event ready owner payload binding
                      checks outputEq codeEq true result resultEq, rfl, rfl, rfl, rfl⟩
              · simp [stored] at accepted
          · simp_all only [reduceCtorEq]
    · simp [handle, ready, timely] at accepted
  · simp [handle, ready] at accepted

private theorem handle_withhold_config_step
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (id : MessageId Player) (event : graph.EventId)
    (accepted : handle runtime state ⟨id, .withhold event⟩ = some next) :
    ∃ (ready : state.config.cut.Ready event) (action : graph.Action event),
      next.config ∈ (state.config.step event ready action).support ∧
        next.clock = state.clock ∧
        next.activatedAt = State.refreshActivated next.config state.clock state.activatedAt ∧
        next.remembered = state.remembered ∧ next.serviceGrant = state.serviceGrant := by
  by_cases ready : state.config.cut.Ready event
  · by_cases timely : state.WithinDeadline runtime event
    · cases view : nodeView graph event with
      | bind owner payload outputEq codeEq =>
          simp [handle, ready, timely, view] at accepted
      | sample payload law outputEq codeEq =>
          simp [handle, ready, timely, view] at accepted
      | resolve owner payload binding checks outputEq codeEq =>
          simp only [handle, dif_pos ready, dif_pos timely, view] at accepted
          split at accepted
          · simp_all only [exists_true_left]
            let disclose := withholdingAction state event owner payload binding checks outputEq
            unfold acceptResolution at accepted
            cases resultEq : EventCode.resolveOutput? binding checks disclose
                state.config.store with
            | none =>
                dsimp only [disclose] at resultEq
                simp only [resultEq, Option.pure_def, Option.bind_eq_bind,
                  Option.bind_none, reduceCtorEq] at accepted
            | some result =>
                dsimp only [disclose] at resultEq
                simp only [resultEq, Option.pure_def, Option.bind_eq_bind,
                  Option.bind_some, Option.some.injEq] at accepted
                subst next
                refine ⟨cast (congrArg EventField.Action outputEq.symm) disclose, ?_⟩
                exact ⟨resolve_complete_mem_step state event ready owner payload binding checks
                  outputEq codeEq disclose result resultEq, rfl, rfl, rfl, rfl⟩
          · simp_all only [reduceCtorEq]
    · simp [handle, ready, timely] at accepted
  · simp [handle, ready] at accepted

/-- Commitment acceptance freezes exactly its addressed handle and installs
that handle at its event. Authentication binds it to the packet sender. -/
theorem handle_commitment_tables (runtime : EventGraphRuntime graph)
    (state next : State graph) (id : MessageId Player)
    (event : graph.EventId) (candidate : Handle graph)
    (accepted : handle runtime state ⟨id, .commitment event candidate⟩ = some next) :
    next.candidates = state.candidates.accept candidate ∧
      next.accepted = Function.update state.accepted (.inr event) (some candidate) ∧
      candidate.1 = id.1 := by
  by_cases ready : state.config.cut.Ready event
  · by_cases timely : state.WithinDeadline runtime event
    · cases view : nodeView graph event with
      | resolve | sample => simp [handle, ready, timely, view] at accepted
      | bind owner payload outputEq codeEq =>
          simp only [handle, dif_pos ready, dif_pos timely, view] at accepted
          split at accepted
          · rename_i sender
            simp_all only [dite_eq_ite, Option.ite_none_right_eq_some,
              Option.some.injEq]
            rcases accepted with ⟨handleOwner, _, _, rfl⟩
            exact ⟨rfl, rfl, sender.symm⟩
          · simp_all only [reduceCtorEq]
    · simp [handle, ready, timely] at accepted
  · simp [handle, ready] at accepted

/-- Resolution traffic never changes accepted binding handles or candidate meanings. -/
theorem handle_resolution_tables (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (noncommitment : ∀ event candidate, message.payload ≠ .commitment event candidate)
    (accepted : handle runtime state message = some next) :
    next.accepted = state.accepted ∧ next.candidates = state.candidates := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | commitment event candidate => exact (noncommitment event candidate rfl).elim
  | opening event candidate raw =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | bind owner payload outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
          | sample payload law outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
          | resolve owner payload binding checks outputEq codeEq =>
              simp only [handle, dif_pos ready, dif_pos timely, view] at accepted
              split at accepted
              · simp_all only [dite_eq_ite, Option.ite_none_right_eq_some]
                split at accepted
                · simp at accepted
                · split at accepted
                  · unfold acceptResolution at accepted
                    rcases accepted with ⟨_, _, _, accepted⟩
                    cases resolved : EventCode.resolveOutput? binding checks true
                        state.config.store with
                    | none => simp [resolved] at accepted
                    | some result =>
                        simp only [resolved, Option.pure_def, Option.bind_eq_bind,
                          Option.bind_some, Option.some.injEq] at accepted
                        subst next
                        exact ⟨rfl, rfl⟩
                  · simp at accepted
              · simp_all only [reduceCtorEq]
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted
  | withhold event =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : state.WithinDeadline runtime event
        · cases view : nodeView graph event with
          | bind owner payload outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
          | sample payload law outputEq codeEq =>
              simp [handle, ready, timely, view] at accepted
          | resolve owner payload binding checks outputEq codeEq =>
              simp only [handle, dif_pos ready, dif_pos timely, view] at accepted
              split at accepted
              · unfold acceptResolution at accepted
                cases resolved : EventCode.resolveOutput? binding checks
                    (withholdingAction state event owner payload binding checks outputEq)
                    state.config.store with
                | none => simp [resolved] at accepted
                | some result =>
                    simp only [resolved, Option.pure_def, Option.bind_eq_bind,
                      Option.bind_some, Option.some.injEq] at accepted
                    subst next
                    exact ⟨rfl, rfl⟩
              · simp_all only [reduceCtorEq]
        · simp [handle, ready, timely] at accepted
      · simp [handle, ready] at accepted

/-- Every accepted player packet performs exactly one semantic graph step at
its stable event address. The witness action is the original action retained
by the ideal configuration, including a sound rejected `true` disclosure. -/
theorem handle_config_mem_step (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next) :
    ∃ event, Payload.event? graph message.payload = some event ∧
      ∃ (ready : state.config.cut.Ready event) (action : graph.Action event),
        next.config ∈ (state.config.step event ready action).support := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | commitment event candidate =>
      obtain ⟨ready, action, member, _, _⟩ :=
        handle_commitment_config_step runtime state next id event candidate accepted
      exact ⟨event, rfl, ready, action, member⟩
  | opening event candidate raw =>
      obtain ⟨ready, action, member, _, _⟩ :=
        handle_opening_config_step runtime state next id event candidate raw accepted
      exact ⟨event, rfl, ready, action, member⟩
  | withhold event =>
      obtain ⟨ready, action, member, _, _⟩ :=
        handle_withhold_config_step runtime state next id event accepted
      exact ⟨event, rfl, ready, action, member⟩

/-- Every accepted packet preserves the clock and refreshes activation metadata
around its unique graph completion.  This structural fact complements
`handle_config_mem_step`; it exposes no private candidate or action data. -/
theorem handle_clock_activated (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next) :
    next.clock = state.clock ∧
      next.activatedAt =
        State.refreshActivated next.config state.clock state.activatedAt := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | commitment event candidate =>
      obtain ⟨_, _, _, clockEq, activatedEq, _⟩ :=
        handle_commitment_config_step runtime state next id event candidate accepted
      exact ⟨clockEq, activatedEq⟩
  | opening event candidate raw =>
      obtain ⟨_, _, _, clockEq, activatedEq, _⟩ :=
        handle_opening_config_step runtime state next id event candidate raw accepted
      exact ⟨clockEq, activatedEq⟩
  | withhold event =>
      obtain ⟨_, _, _, clockEq, activatedEq, _⟩ :=
        handle_withhold_config_step runtime state next id event accepted
      exact ⟨clockEq, activatedEq⟩

/-- Packet acceptance never overwrites a player's privately sampled action. -/
theorem handle_remembered (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next) :
    next.remembered = state.remembered := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | commitment event candidate =>
      obtain ⟨_, _, _, _, _, memory⟩ :=
        handle_commitment_config_step runtime state next id event candidate accepted
      exact memory.1
  | opening event candidate raw =>
      obtain ⟨_, _, _, _, _, memory⟩ :=
        handle_opening_config_step runtime state next id event candidate raw accepted
      exact memory.1
  | withhold event =>
      obtain ⟨_, _, _, _, _, memory⟩ :=
        handle_withhold_config_step runtime state next id event accepted
      exact memory.1

/-- Including a player packet never changes the public service grant. -/
theorem handle_serviceGrant (runtime : EventGraphRuntime graph)
    (state next : State graph) (message : Message Player (Payload graph))
    (accepted : handle runtime state message = some next) :
    next.serviceGrant = state.serviceGrant := by
  rcases message with ⟨id, packet⟩
  cases packet with
  | malformed raw => simp [handle] at accepted
  | commitment event candidate =>
      obtain ⟨_, _, _, _, _, _, grant⟩ :=
        handle_commitment_config_step runtime state next id event candidate accepted
      exact grant
  | opening event candidate raw =>
      obtain ⟨_, _, _, _, _, _, grant⟩ :=
        handle_opening_config_step runtime state next id event candidate raw accepted
      exact grant
  | withhold event =>
      obtain ⟨_, _, _, _, _, _, grant⟩ :=
        handle_withhold_config_step runtime state next id event accepted
      exact grant

/-- Replacing the private remembered-action cache cannot change the public
result of applying any pending packet. Rejected original `true` actions remain
available to the owner as ghost recall without becoming ledger information. -/
theorem handle_publicView_replaceRemembered (runtime : EventGraphRuntime graph)
    (state : State graph) (memory : RememberedActions graph)
    (message : Message Player (Payload graph)) :
    Option.map State.publicView
        (handle runtime { state with remembered := memory } message) =
      Option.map State.publicView (handle runtime state message) := by
  rcases message with ⟨sender, payload⟩
  cases payload with
  | malformed raw => rfl
  | commitment event candidate =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : State.WithinDeadline runtime state event
        · have replacedTimely :
              State.WithinDeadline runtime { state with remembered := memory } event := by
            simpa [State.WithinDeadline] using timely
          cases view : nodeView graph event <;>
            try { simp [handle, Message.sender, ready, timely, replacedTimely, view] }
          case bind owner payload outputEq codeEq =>
            by_cases senderEq : sender.1 = owner
            · by_cases ownerEq : candidate.1 = owner
              · by_cases vacant : state.accepted (.inr event) = none
                · by_cases unused : state.HandleUnused candidate
                  · have replacedUnused :
                        ({ state with remembered := memory }).HandleUnused candidate := by
                      simpa only [State.HandleUnused] using unused
                    simpa [handle, Message.sender, ready, timely, replacedTimely,
                      view, senderEq, ownerEq, vacant, unused, replacedUnused] using
                      congrArg some (acceptBinding_publicView_replaceRemembered
                        state memory event ready owner payload outputEq candidate)
                  · have replacedUsed :
                        ¬({ state with remembered := memory }).HandleUnused candidate := by
                      simpa only [State.HandleUnused] using unused
                    simp [handle, Message.sender, ready, timely, replacedTimely, view,
                      senderEq, ownerEq, vacant, unused, replacedUsed]
                · simp [handle, Message.sender, ready, timely, replacedTimely, view, senderEq,
                    ownerEq, vacant]
              · simp [handle, Message.sender, ready, timely, replacedTimely, view,
                  senderEq, ownerEq]
            · simp [handle, Message.sender, ready, timely, replacedTimely, view, senderEq]
        · have replacedLate :
              ¬State.WithinDeadline runtime { state with remembered := memory } event := by
            simpa [State.WithinDeadline] using timely
          simp [handle, ready, timely, replacedLate]
      · simp [handle, ready]
  | opening event candidate raw =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : State.WithinDeadline runtime state event
        · have replacedTimely :
              State.WithinDeadline runtime { state with remembered := memory } event := by
            simpa [State.WithinDeadline] using timely
          cases view : nodeView graph event <;>
            try { simp [handle, Message.sender, ready, timely, replacedTimely, view] }
          case resolve owner payload binding checks outputEq codeEq =>
            by_cases senderEq : sender.1 = owner
            · by_cases ownerEq : candidate.1 = owner
              · by_cases associated : state.accepted binding.field = some candidate
                · by_cases verified : state.candidates.verify candidate raw = true
                  · simp only [handle, dif_pos ready, dif_pos replacedTimely, view,
                      Message.sender, senderEq, ownerEq, associated, verified,
                      dite_eq_ite, dif_pos timely]
                    cases typed : raw.as? payload with
                    | none => rfl
                    | some value =>
                      by_cases stored :
                          binding.get? state.config.store = some (.success value)
                      · simpa [stored] using
                          acceptResolution_publicView_replaceRemembered state memory
                            event ready owner payload binding checks outputEq true
                      · simp [stored]
                  · simp [handle, Message.sender, ready, timely, replacedTimely, view, senderEq,
                      ownerEq, associated, verified]
                · simp [handle, Message.sender, ready, timely, replacedTimely, view, senderEq,
                    ownerEq, associated]
              · simp [handle, Message.sender, ready, timely, replacedTimely, view,
                  senderEq, ownerEq]
            · simp [handle, Message.sender, ready, timely, replacedTimely, view, senderEq]
        · have replacedLate :
              ¬State.WithinDeadline runtime { state with remembered := memory } event := by
            simpa [State.WithinDeadline] using timely
          simp [handle, ready, timely, replacedLate]
      · simp [handle, ready]
  | withhold event =>
      by_cases ready : state.config.cut.Ready event
      · by_cases timely : State.WithinDeadline runtime state event
        · have replacedTimely :
              State.WithinDeadline runtime { state with remembered := memory } event := by
            simpa [State.WithinDeadline] using timely
          cases view : nodeView graph event with
          | bind owner payload outputEq =>
              simp [handle, ready, timely, replacedTimely, view]
          | sample payload law outputEq codeEq =>
              simp [handle, ready, timely, replacedTimely, view]
          | resolve owner payload binding checks outputEq codeEq =>
              by_cases senderEq : sender.1 = owner
              · simp only [handle, dif_pos ready, dif_pos replacedTimely, view,
                  Message.sender, senderEq, dif_pos timely]
                let left := withholdingAction { state with remembered := memory }
                  event owner payload binding checks outputEq
                let right := withholdingAction state event owner payload binding checks outputEq
                have resultEq :
                    EventCode.resolveOutput? binding checks left state.config.store =
                      EventCode.resolveOutput? binding checks right state.config.store := by
                  exact (withholdingAction_output
                    { state with remembered := memory } event owner payload binding checks
                    outputEq).trans
                    (withholdingAction_output state event owner payload binding checks
                      outputEq).symm
                calc
                  Option.map State.publicView
                      (acceptResolution { state with remembered := memory }
                        event ready owner payload binding checks outputEq left) =
                    Option.map State.publicView
                      (acceptResolution state event ready owner payload binding checks
                        outputEq left) :=
                          acceptResolution_publicView_replaceRemembered state memory event
                            ready owner payload binding checks outputEq left
                  _ = Option.map State.publicView
                      (acceptResolution state event ready owner payload binding checks
                        outputEq right) :=
                          acceptResolution_publicView_congr state event ready owner payload
                            binding checks outputEq left right resultEq
              · simp [handle, Message.sender, ready, timely, replacedTimely, view, senderEq]
        · have replacedLate :
              ¬State.WithinDeadline runtime { state with remembered := memory } event := by
            simpa [State.WithinDeadline] using timely
          simp [handle, ready, timely, replacedLate]
      · simp [handle, ready]

/-- A sample command runs the retained chance kernel once when the addressed
event is ready. Other event kinds stutter. -/
private def executeSample (state : State graph) (event : graph.EventId) :
    FinDist (State graph) :=
  if ready : state.config.cut.Ready event then
    match nodeView graph event with
    | .sample _ _ outputEq _codeEq =>
        (state.config.step event ready
          (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)).map fun config =>
            { state with
              config
              activatedAt := State.refreshActivated config state.clock state.activatedAt }
    | .bind .. | .resolve .. => FinDist.pure state
  else FinDist.pure state

/-- Expiry is local to one ready strategic event and consumes no other event's
budget. It completes binds with failure and resolutions with `false`. -/
private def expire (runtime : EventGraphRuntime graph) (state : State graph)
    (event : graph.EventId) : State graph :=
  if ready : state.config.cut.Ready event then
    match _activated : state.activatedAt event with
    | none => state
    | some entered =>
        if _due : runtime.deadline event ≤ state.clock - entered then
          match nodeView graph event with
          | .bind _owner payload outputEq _codeEq =>
              let failed : PublicationResult (L.Val payload) := .failure
              state.complete event ready
                (cast (congrArg EventField.Action outputEq.symm) failed)
                (cast (congrArg EventField.Value outputEq.symm) failed)
          | .resolve owner payload binding checks outputEq _codeEq =>
              (acceptResolution state event ready owner payload binding checks
                outputEq false).getD state
          | .sample .. => state
        else state
  else state

def environmentStep (runtime : EventGraphRuntime graph) (state : State graph) :
    EnvironmentCommand graph → FinDist (State graph)
  | .grant event => FinDist.pure { state with serviceGrant := some event }
  | .advanceClock => FinDist.pure { state with clock := state.clock + 1 }
  | .executeSample event => executeSample state event
  | .expire event => FinDist.pure (expire runtime state event)

omit [DecidableEq Player] in
/-- Environment application operations cannot write a player's action cache. -/
theorem environmentStep_remembered (runtime : EventGraphRuntime graph)
    (before after : State graph) (command : EnvironmentCommand graph)
    (member : after ∈ (environmentStep runtime before command).support) :
    after.remembered = before.remembered := by
  cases command with
  | grant event | advanceClock =>
      simp only [environmentStep, FinDist.mem_support_pure] at member
      subst after
      rfl
  | executeSample event =>
      change after ∈ (executeSample before event).support at member
      unfold executeSample at member
      split at member
      · cases view : nodeView graph event with
        | bind | resolve =>
            simp only [view, FinDist.mem_support_pure] at member
            subst after
            rfl
        | sample =>
            simp only [view, FinDist.support_map, Set.mem_image] at member
            obtain ⟨config, _, rfl⟩ := member
            rfl
      · simp only [FinDist.mem_support_pure] at member
        subst after
        rfl
  | expire event =>
      change after ∈ (FinDist.pure (expire runtime before event)).support at member
      rw [FinDist.mem_support_pure] at member
      subst after
      unfold expire
      split
      · split
        · rfl
        · split
          · cases nodeView graph event with
            | bind | sample => rfl
            | resolve owner payload binding checks outputEq codeEq =>
                unfold acceptResolution
                cases resolved : EventCode.resolveOutput? binding checks false
                    before.config.store <;> simp only [resolved] <;> rfl
          · rfl
      · rfl

omit [DecidableEq Player] in
/-- Only a grant command changes the public service cursor. -/
theorem environmentStep_serviceGrant (runtime : EventGraphRuntime graph)
    (before after : State graph) (command : EnvironmentCommand graph)
    (member : after ∈ (environmentStep runtime before command).support) :
    after.serviceGrant = match command with
      | .grant event => some event
      | _ => before.serviceGrant := by
  cases command with
  | grant event | advanceClock =>
      simp only [environmentStep, FinDist.mem_support_pure] at member
      subst after
      rfl
  | executeSample event =>
      change after ∈ (executeSample before event).support at member
      unfold executeSample at member
      split at member
      · cases view : nodeView graph event with
        | bind | resolve =>
            simp only [view, FinDist.mem_support_pure] at member
            subst after
            rfl
        | sample =>
            simp only [view, FinDist.support_map, Set.mem_image] at member
            obtain ⟨config, _, rfl⟩ := member
            rfl
      · simp only [FinDist.mem_support_pure] at member
        subst after
        rfl
  | expire event =>
      change after ∈ (FinDist.pure (expire runtime before event)).support at member
      rw [FinDist.mem_support_pure] at member
      subst after
      change (expire runtime before event).serviceGrant = before.serviceGrant
      unfold expire
      split
      · split
        · rfl
        · split
          · cases nodeView graph event with
            | bind | sample => rfl
            | resolve owner payload binding checks outputEq codeEq =>
                unfold acceptResolution
                cases resolved : EventCode.resolveOutput? binding checks false
                    before.config.store <;> simp only [resolved] <;> rfl
          · rfl
      · rfl

omit [DecidableEq Player] in
/-- Environment service never changes commitment admission tables. -/
theorem environmentStep_tables
    (runtime : EventGraphRuntime graph)
    (state next : State graph) (command : EnvironmentCommand graph)
    (member : next ∈ (environmentStep runtime state command).support) :
    next.accepted = state.accepted ∧ next.candidates = state.candidates := by
  cases command with
  | grant event =>
      simp only [environmentStep, FinDist.mem_support_pure] at member
      subst next
      exact ⟨rfl, rfl⟩
  | advanceClock =>
      simp only [environmentStep, FinDist.mem_support_pure] at member
      subst next
      exact ⟨rfl, rfl⟩
  | executeSample event =>
      change next ∈ (executeSample state event).support at member
      unfold executeSample at member
      split at member
      · rename_i ready
        cases view : nodeView graph event with
        | bind | resolve =>
            simp only [view] at member
            simp only [FinDist.mem_support_pure] at member
            subst next
            exact ⟨rfl, rfl⟩
        | sample =>
          simp only [view] at member
          rw [FinDist.support_map, Set.mem_image] at member
          obtain ⟨config, _, rfl⟩ := member
          exact ⟨rfl, rfl⟩
      · simp only [FinDist.mem_support_pure] at member
        subst next
        exact ⟨rfl, rfl⟩
  | expire event =>
      change next ∈ (FinDist.pure (expire runtime state event)).support at member
      simp only [FinDist.mem_support_pure] at member
      subst next
      unfold expire
      split
      · split
        · exact ⟨rfl, rfl⟩
        · split
          · rename_i due
            cases view : nodeView graph event with
            | bind => exact ⟨rfl, rfl⟩
            | sample => exact ⟨rfl, rfl⟩
            | resolve owner payload binding checks outputEq codeEq =>
                unfold acceptResolution
                cases resolved : EventCode.resolveOutput? binding checks false
                    state.config.store
                · simp only [resolved]
                  exact ⟨rfl, rfl⟩
                · simp only [resolved]
                  exact ⟨rfl, rfl⟩
          · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩

omit [DecidableEq Player] in
/-- Executing a certified ready sample is exactly the graph chance step, with
only the runtime activation metadata refreshed around each sampled result. -/
theorem environmentStep_executeSample_eq
    (runtime : EventGraphRuntime graph) (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (viewEq : nodeView graph event = .sample payload law outputEq codeEq) :
    environmentStep runtime state (.executeSample event) =
      (state.config.step event ready
        (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)).map
          fun config =>
            { state with
              config
              activatedAt := State.refreshActivated config state.clock state.activatedAt } := by
  simp only [environmentStep, executeSample, dif_pos ready, viewEq]

omit [DecidableEq Player] in
theorem environmentStep_executeSample_of_not_ready
    (runtime : EventGraphRuntime graph) (state : State graph)
    (event : graph.EventId) (ready : ¬state.config.cut.Ready event) :
    environmentStep runtime state (.executeSample event) = FinDist.pure state := by
  simp only [environmentStep, executeSample, dif_neg ready]

omit [DecidableEq Player] in
theorem environmentStep_executeSample_of_nonsample
    (runtime : EventGraphRuntime graph) (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (view : ∀ payload law outputEq codeEq,
      nodeView graph event ≠ .sample payload law outputEq codeEq) :
    environmentStep runtime state (.executeSample event) = FinDist.pure state := by
  simp only [environmentStep, executeSample, dif_pos ready]
  cases actual : nodeView graph event with
  | bind | resolve => rfl
  | sample payload law outputEq codeEq =>
      exact (view payload law outputEq codeEq actual).elim

omit [DecidableEq Player] in
/-- Once a ready binding deadline is due, expiry is exactly the binding's
failure graph completion. -/
theorem environmentStep_expire_bind_eq
    (runtime : EventGraphRuntime graph) (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (entered : Nat) (activated : state.activatedAt event = some entered)
    (due : runtime.deadline event ≤ state.clock - entered)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (viewEq : nodeView graph event = .bind owner payload outputEq codeEq) :
    environmentStep runtime state (.expire event) =
      FinDist.pure (state.complete event ready
        (cast (congrArg EventField.Action outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload)))
        (cast (congrArg EventField.Value outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload)))) := by
  simp only [environmentStep, expire, dif_pos ready]
  split
  · rename_i activation
    rw [activated] at activation
    contradiction
  · rename_i actual activation
    have same : actual = entered := by simpa [activated] using activation.symm
    subst actual
    simp only [dif_pos due, viewEq]

omit [DecidableEq Player] in
/-- Once a ready resolution deadline is due, expiry is exactly its canonical
withholding step, which is total and stores publication failure. -/
theorem environmentStep_expire_resolve_eq
    (runtime : EventGraphRuntime graph) (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (entered : Nat) (activated : state.activatedAt event = some entered)
    (due : runtime.deadline event ≤ state.clock - entered)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (viewEq : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq) :
    environmentStep runtime state (.expire event) =
      FinDist.pure (state.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) false)
        (cast (congrArg EventField.Value outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload)))) := by
  have resultEq := resolveOutput?_false_eq_failure_of_ready state event ready
    owner payload binding checks outputEq codeEq
  simp only [environmentStep, expire, dif_pos ready]
  split
  · rename_i activation
    rw [activated] at activation
    contradiction
  · rename_i actual activation
    have same : actual = entered := by simpa [activated] using activation.symm
    subst actual
    simp [due, viewEq, acceptResolution, resultEq]

omit [DecidableEq Player] in
/-- A supported expiry command either stutters or performs exactly one graph
step at its addressed event. The stutter cases are not-ready, unactivated,
not-due, or sample events; ready resolution reads make withholding total. -/
theorem environmentStep_expire_config_eq_or_mem_step
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (event : graph.EventId)
    (member : next ∈ (environmentStep runtime state (.expire event)).support) :
    next.config = state.config ∨
      ∃ (ready : state.config.cut.Ready event) (action : graph.Action event),
        next.config ∈ (state.config.step event ready action).support := by
  simp only [environmentStep, FinDist.mem_support_pure] at member
  subst next
  unfold expire
  split
  · rename_i ready
    split
    · exact Or.inl rfl
    · rename_i entered activated
      split
      · rename_i due
        cases view : nodeView graph event with
        | sample payload law outputEq codeEq => exact Or.inl rfl
        | bind owner payload outputEq codeEq =>
            let failed : PublicationResult (L.Val payload) := .failure
            exact Or.inr ⟨ready,
              cast (congrArg EventField.Action outputEq.symm) failed,
              bind_complete_mem_step state event ready owner payload outputEq
                codeEq failed⟩
        | resolve owner payload binding checks outputEq codeEq =>
            have resultEq := resolveOutput?_false_eq_failure_of_ready state event ready
              owner payload binding checks outputEq codeEq
            refine Or.inr ⟨ready,
              cast (congrArg EventField.Action outputEq.symm) false, ?_⟩
            simpa only [view, acceptResolution, resultEq, bind, pure, State.complete,
              Option.bind_some, Option.getD_some] using
                resolve_complete_mem_step state event ready owner payload binding
                  checks outputEq codeEq false .failure resultEq
      · exact Or.inl rfl
  · exact Or.inl rfl

omit [DecidableEq Player] in
theorem environmentStep_expire_of_not_ready
    (runtime : EventGraphRuntime graph) (state : State graph)
    (event : graph.EventId) (ready : ¬state.config.cut.Ready event) :
    environmentStep runtime state (.expire event) = FinDist.pure state := by
  simp only [environmentStep, expire, dif_neg ready]

omit [DecidableEq Player] in
theorem environmentStep_expire_of_not_activated
    (runtime : EventGraphRuntime graph) (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (activated : state.activatedAt event = none) :
    environmentStep runtime state (.expire event) = FinDist.pure state := by
  simp only [environmentStep, expire, dif_pos ready]
  split
  · rfl
  · rename_i entered actual
    rw [activated] at actual
    contradiction

omit [DecidableEq Player] in
theorem environmentStep_expire_of_not_due
    (runtime : EventGraphRuntime graph) (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (entered : Nat) (activated : state.activatedAt event = some entered)
    (due : ¬runtime.deadline event ≤ state.clock - entered) :
    environmentStep runtime state (.expire event) = FinDist.pure state := by
  simp only [environmentStep, expire, dif_pos ready]
  split
  · rename_i actual
    rw [activated] at actual
  · rename_i actualEntered actual
    have same : actualEntered = entered := by simpa [activated] using actual.symm
    subst actualEntered
    simp only [dif_neg due]

omit [DecidableEq Player] in
theorem environmentStep_expire_sample_eq
    (runtime : EventGraphRuntime graph) (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (entered : Nat) (activated : state.activatedAt event = some entered)
    (due : runtime.deadline event ≤ state.clock - entered)
    (payload : L.Ty) (law : PublicDist graph.layout payload)
    (outputEq : graph.outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .sample payload law)
    (viewEq : nodeView graph event = .sample payload law outputEq codeEq) :
    environmentStep runtime state (.expire event) = FinDist.pure state := by
  simp only [environmentStep, expire, dif_pos ready]
  split
  · rename_i actual
    rw [activated] at actual
  · rename_i actualEntered actual
    have same : actualEntered = entered := by simpa [activated] using actual.symm
    subst actualEntered
    simp only [dif_pos due, viewEq]

omit [DecidableEq Player] in
/-- A supported sample command either stutters or performs its addressed graph
step and refreshes activation metadata. -/
theorem environmentStep_executeSample_config_activated
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (event : graph.EventId)
    (member : next ∈ (environmentStep runtime state (.executeSample event)).support) :
    next.clock = state.clock ∧
      ((next.config = state.config ∧ next.activatedAt = state.activatedAt) ∨
        ∃ (ready : state.config.cut.Ready event) (action : graph.Action event),
          next.config ∈ (state.config.step event ready action).support ∧
            next.activatedAt =
              State.refreshActivated next.config state.clock state.activatedAt) := by
  by_cases ready : state.config.cut.Ready event
  · cases view : nodeView graph event with
    | bind owner payload outputEq codeEq =>
        simp only [environmentStep, executeSample, dif_pos ready, view,
          FinDist.mem_support_pure] at member
        subst next
        exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    | resolve owner payload binding checks outputEq codeEq =>
        simp only [environmentStep, executeSample, dif_pos ready, view,
          FinDist.mem_support_pure] at member
        subst next
        exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    | sample payload law outputEq codeEq =>
        rw [environmentStep_executeSample_eq runtime state event ready payload law
          outputEq codeEq view, FinDist.support_map] at member
        obtain ⟨config, configMem, rfl⟩ := member
        exact ⟨rfl, Or.inr ⟨ready,
          cast (congrArg EventField.Action outputEq.symm) PUnit.unit,
          configMem, rfl⟩⟩
  · simp only [environmentStep, executeSample, dif_neg ready,
      FinDist.mem_support_pure] at member
    subst next
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

omit [DecidableEq Player] in
/-- A supported expiry command either stutters or performs its addressed graph
step and refreshes activation metadata. -/
theorem environmentStep_expire_config_activated
    (runtime : EventGraphRuntime graph) (state next : State graph)
    (event : graph.EventId)
    (member : next ∈ (environmentStep runtime state (.expire event)).support) :
    next.clock = state.clock ∧
      ((next.config = state.config ∧ next.activatedAt = state.activatedAt) ∨
        ∃ (ready : state.config.cut.Ready event) (action : graph.Action event),
          next.config ∈ (state.config.step event ready action).support ∧
            next.activatedAt =
              State.refreshActivated next.config state.clock state.activatedAt) := by
  by_cases ready : state.config.cut.Ready event
  · cases activated : state.activatedAt event with
    | none =>
        rw [environmentStep_expire_of_not_activated runtime state event ready activated,
          FinDist.mem_support_pure] at member
        subst next
        exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    | some entered =>
        by_cases due : runtime.deadline event ≤ state.clock - entered
        · cases view : nodeView graph event with
          | sample payload law outputEq codeEq =>
              rw [environmentStep_expire_sample_eq runtime state event ready entered
                activated due payload law outputEq codeEq view,
                FinDist.mem_support_pure] at member
              subst next
              exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
          | bind owner payload outputEq codeEq =>
              rw [environmentStep_expire_bind_eq runtime state event ready entered
                activated due owner payload outputEq codeEq view,
                FinDist.mem_support_pure] at member
              subst next
              let failed : PublicationResult (L.Val payload) := .failure
              exact ⟨rfl, Or.inr ⟨ready,
                cast (congrArg EventField.Action outputEq.symm) failed,
                bind_complete_mem_step state event ready owner payload outputEq
                  codeEq failed, rfl⟩⟩
          | resolve owner payload binding checks outputEq codeEq =>
              rw [environmentStep_expire_resolve_eq runtime state event ready entered
                activated due owner payload binding checks outputEq codeEq view,
                FinDist.mem_support_pure] at member
              subst next
              have resultEq := resolveOutput?_false_eq_failure_of_ready state event ready
                owner payload binding checks outputEq codeEq
              exact ⟨rfl, Or.inr ⟨ready,
                cast (congrArg EventField.Action outputEq.symm) false,
                resolve_complete_mem_step state event ready owner payload binding checks
                  outputEq codeEq false .failure resultEq, rfl⟩⟩
        · rw [environmentStep_expire_of_not_due runtime state event ready entered
            activated due, FinDist.mem_support_pure] at member
          subst next
          exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  · rw [environmentStep_expire_of_not_ready runtime state event ready,
      FinDist.mem_support_pure] at member
    subst next
    exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- Shared pending-message application instance. Transport, pools, receipts,
and policy histories come from `Interaction.MessageApplication`. -/
def application (runtime : EventGraphRuntime graph) : MessageApplication Player where
  Application := State graph
  Payload := Payload graph
  PrivateCommand := PrivateCommand graph
  EnvironmentCommand := EnvironmentCommand graph
  PlayerView := PlayerView graph
  EnvironmentView := PublicView graph
  privateStep := privateStep
  environmentStep := environmentStep runtime
  handle := handle runtime
  observePlayer := State.playerView
  observeEnvironment := State.publicView

end EventGraphRuntime
end Vegas
