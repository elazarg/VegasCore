/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.NormalizedPolicy
import Vegas.Pending.EventApplication
import Interaction.MessageApplicationPolicies

/-! # Prescribed event-graph policies for the pending runtime

Each strategic event uses a stable event-addressed handle and exactly three
owner opportunities: sample and remember the graph action, privately stage its
wire material, then submit.  Binding failure and success consequently differ
only in private staging, never in the public submission time.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

abbrev Entry (runtime : EventGraphRuntime graph) := runtime.application.PlayerEntry
abbrev Command (runtime : EventGraphRuntime graph) := runtime.application.PlayerCommand

namespace PublicView

/-- Readiness reconstructed from public completion identities alone. -/
def EventReady (view : PublicView graph) (event : graph.EventId) : Prop :=
  event ∉ view.observation.completionOrder ∧
    ∀ predecessor, predecessor ∈ graph.order.predecessors event →
      predecessor ∈ view.observation.completionOrder

instance (view : PublicView graph) (event : graph.EventId) :
    Decidable (view.EventReady event) := by
  unfold EventReady
  infer_instance

end PublicView

omit [DecidableEq Player] in
/-- The public readiness test is exact on every structurally coherent runtime
state; it neither consults hidden values nor assumes reachability. -/
theorem State.publicView_eventReady (state : State graph) (event : graph.EventId) :
    state.publicView.EventReady event ↔ state.config.cut.Ready event := by
  constructor
  · rintro ⟨unfinished, predecessors⟩
    constructor
    · intro completed
      exact unfinished ((state.config.history_exact event).mpr completed)
    · intro predecessor member
      exact (state.config.history_exact predecessor).mp (predecessors predecessor member)
  · rintro ⟨unfinished, predecessors⟩
    constructor
    · intro inHistory
      exact unfinished ((state.config.history_exact event).mp inHistory)
    · intro predecessor member
      exact (state.config.history_exact predecessor).mpr (predecessors member)

/-- Whether one authenticated command is a private staging operation for the
given event.  Prepared slots use the event's stable numeric identity. -/
def stagesEvent {runtime : EventGraphRuntime graph} (event : graph.EventId) :
    Command runtime → Bool
  | .privateCommand (.remember remembered _) => decide (remembered = event)
  | .privateCommand (.prepare serial _) => decide (serial = event.val)
  | _ => false

/-- Number of private staging calls already recorded for one event. -/
def stagingCount {runtime : EventGraphRuntime graph}
    (history : List (Entry runtime)) (event : graph.EventId) : Nat :=
  (history.filter fun entry => stagesEvent event entry.command).length

@[simp]
theorem stagingCount_append_remember {runtime : EventGraphRuntime graph}
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId) (action : graph.Action event) :
    stagingCount (history ++ [⟨view, .privateCommand (.remember event action)⟩]) event =
      stagingCount history event + 1 := by
  simp [stagingCount, stagesEvent]

@[simp]
theorem stagingCount_append_prepare {runtime : EventGraphRuntime graph}
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId) (raw : Raw L) :
    stagingCount (history ++ [⟨view, .privateCommand (.prepare event.val raw)⟩]) event =
      stagingCount history event + 1 := by
  simp [stagingCount, stagesEvent]

/-- Whether this player has already submitted any packet addressed to the
event.  Packet contents and application acceptance are deliberately ignored. -/
def submittedAt {runtime : EventGraphRuntime graph}
    (history : List (Entry runtime)) (event : graph.EventId) : Bool :=
  history.any fun entry =>
    match entry.command with
    | .submit payload => payload.event? graph = some event
    | _ => false

@[simp]
theorem submittedAt_append_submit {runtime : EventGraphRuntime graph}
    (history : List (Entry runtime)) (view : runtime.application.View)
    (event : graph.EventId) (payload : Payload graph) :
    submittedAt (history ++ [⟨view, .submit payload⟩]) event =
      (submittedAt history event || decide (payload.event? graph = some event)) := by
  simp [submittedAt]

/-- The canonical prepared candidate slot for an event. -/
def eventSlot (event : graph.EventId) : CandidateSlot graph :=
  .prepared event.val

/-- The fixed second private command for a binding event.  Successful actions
prepare the canonical event slot; failures repeat the opaque remembered action,
so both cases consume exactly one private service opportunity. -/
def bindingStageCommand (runtime : EventGraphRuntime graph)
    {owner : Player} (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (action : graph.Action event) : Command runtime :=
  let result : PublicationResult (L.Val payload) :=
    cast (congrArg EventField.Action outputEq) action
  match result with
  | .failure => .privateCommand (.remember event action)
  | .success value => .privateCommand (.prepare event.val ⟨payload, value⟩)

/-- Binding staging is always private, including the failure branch. -/
theorem bindingStageCommand_is_private (runtime : EventGraphRuntime graph)
    {owner : Player} (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (action : graph.Action event) :
    ∃ command, runtime.bindingStageCommand event payload outputEq action =
      .privateCommand command := by
  unfold bindingStageCommand
  generalize cast (congrArg EventField.Action outputEq) action = result
  cases result <;> simp

@[simp]
theorem stagingCount_append_bindingStageCommand (runtime : EventGraphRuntime graph)
    (history : List (Entry runtime)) (view : runtime.application.View)
    {owner : Player} (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (action : graph.Action event) :
    stagingCount
        (history ++ [⟨view, runtime.bindingStageCommand event payload outputEq action⟩])
        event = stagingCount history event + 1 := by
  unfold bindingStageCommand
  generalize cast (congrArg EventField.Action outputEq) action = result
  cases result <;> simp

@[simp]
theorem submittedAt_append_bindingStageCommand (runtime : EventGraphRuntime graph)
    (history : List (Entry runtime)) (view : runtime.application.View)
    {owner : Player} (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (action : graph.Action event) :
    submittedAt
        (history ++ [⟨view, runtime.bindingStageCommand event payload outputEq action⟩])
        event = submittedAt history event := by
  unfold bindingStageCommand
  generalize cast (congrArg EventField.Action outputEq) action = result
  cases result <;> simp [submittedAt]

/-- The event-addressed payload selected at the third opportunity of a
resolution event. Only a successful, locally validated disclosure with an
accepted owner handle opens; every other case withholds. -/
def resolutionPayload (runtime : EventGraphRuntime graph)
    {owner : Player} (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : runtime.application.View) : Payload graph :=
  let disclose : Bool := cast (congrArg EventField.Action outputEq) action
  if disclose then
    match EventCode.resolveOutput? binding checks true
        view.application.observation.store with
    | some (.success value) =>
        match view.application.publicView.accepted binding.field with
        | some handle =>
            if handle.1 = who then
              .opening event handle ⟨payload, value⟩
            else .withhold event
        | none => .withhold event
    | some .failure | none => .withhold event
  else .withhold event

/-- The public command emitted at the third opportunity of a resolution
event. -/
def resolutionSubmission (runtime : EventGraphRuntime graph)
    {owner : Player} (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : runtime.application.View) : Command runtime :=
  .submit (runtime.resolutionPayload who event payload binding checks outputEq action view)

@[simp]
theorem resolutionSubmission_false (runtime : EventGraphRuntime graph)
    {owner : Player} (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : runtime.application.View)
    (withholds : cast (congrArg EventField.Action outputEq) action = false) :
    runtime.resolutionSubmission who event payload binding checks outputEq action view =
      .submit (.withhold event) := by
  simp [resolutionSubmission, resolutionPayload, withholds]

@[simp]
theorem resolutionSubmission_rejected (runtime : EventGraphRuntime graph)
    {owner : Player} (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : runtime.application.View)
    (discloses : cast (congrArg EventField.Action outputEq) action = true)
    (rejected : EventCode.resolveOutput? binding checks true
      view.application.observation.store = some .failure) :
    runtime.resolutionSubmission who event payload binding checks outputEq action view =
      .submit (.withhold event) := by
  simp [resolutionSubmission, resolutionPayload, discloses, rejected]

/-- Resolution staging always emits one public packet addressed to the granted
event, whether it opens successfully or withholds. -/
theorem resolutionSubmission_address (runtime : EventGraphRuntime graph)
    {owner : Player} (who : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (DeferredCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : runtime.application.View) :
    ∃ packet, runtime.resolutionSubmission who event payload binding checks
      outputEq action view = .submit packet ∧
      packet.event? graph = some event := by
  refine ⟨runtime.resolutionPayload who event payload binding checks outputEq action view,
    rfl, ?_⟩
  unfold resolutionPayload
  generalize cast (congrArg EventField.Action outputEq) action = disclose
  cases disclose with
  | false => rfl
  | true =>
      simp only [if_true]
      cases resolved : EventCode.resolveOutput? binding checks true
          view.application.observation.store with
      | none => rfl
      | some result =>
          cases result with
          | failure => rfl
          | success value =>
              cases accepted : view.application.publicView.accepted binding.field with
              | none => rfl
              | some handle =>
                  by_cases owned : handle.1 = who
                  · simp [owned, Payload.event?]
                  · simp [owned, Payload.event?]

/-- Compile one normalized graph policy to the event-addressed pending
runtime.  The definition is total on malformed histories and views: it waits
when private state needed for staging is absent, and uses withholding rather
than fabricating opening material. -/
def compilePlayerPolicy (runtime : EventGraphRuntime graph) (who : Player)
    (policy : graph.BehavioralPolicy who) : runtime.application.PlayerPolicy :=
  fun history view =>
    match _grant : view.application.publicView.serviceGrant with
    | none => FinDist.pure .wait
    | some event =>
        if _already : submittedAt history event then FinDist.pure .wait
        else if viewOwner : view.application.who = who then
          if _ready : view.application.publicView.EventReady event then
            if actor : graph.actor? event = some who then
              let observation : graph.PlayerObservation who :=
                viewOwner ▸ view.application.observation
              let normalized := graph.normalizePolicy who policy
              match nodeView graph event with
              | .sample .. => FinDist.pure .wait
              | .bind _owner payload outputEq _codeEq =>
                  match stagingCount history event with
                  | 0 =>
                      (normalized event actor observation).map fun action =>
                        .privateCommand (.remember event action)
                  | 1 =>
                      match view.application.remembered event with
                      | none => FinDist.pure .wait
                      | some action =>
                          FinDist.pure
                            (bindingStageCommand runtime event payload outputEq action)
                  | _ + 2 => FinDist.pure
                      (.submit (.commitment event (who, eventSlot event)))
              | .resolve _owner payload binding checks outputEq _codeEq =>
                  match stagingCount history event with
                  | 0 =>
                      (normalized event actor observation).map fun action =>
                        .privateCommand (.remember event action)
                  | 1 =>
                      match view.application.remembered event with
                      | none => FinDist.pure .wait
                      | some action => FinDist.pure
                          (.privateCommand (.remember event action))
                  | _ + 2 =>
                      match view.application.remembered event with
                      | none => FinDist.pure (.submit (.withhold event))
                      | some action => FinDist.pure
                          (resolutionSubmission runtime who event payload binding checks
                            outputEq action view)
            else FinDist.pure .wait
          else FinDist.pure .wait
        else FinDist.pure .wait

/-- Compile every player policy independently. -/
def compileProfile (runtime : EventGraphRuntime graph)
    (profile : graph.BehavioralProfile) : Player → runtime.application.PlayerPolicy :=
  fun who => runtime.compilePlayerPolicy who (profile who)

end Vegas.EventGraphRuntime
