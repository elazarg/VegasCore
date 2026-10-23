/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketOwnerStep
import Vegas.Pending.EventActivationOrigin

/-! # Scheduler rounds of the one-packet game at a pending binding

While a binding event is pending, an included commitment of its owner fixes
the binding from the owner's candidate, which is private. The image of a state
therefore carries, besides its operational state, whether the candidate of
each pending commitment of the owner to the event succeeds
(`Vegas.commitStatuses`, `Vegas.bindingImage`). With that record, a scheduler
round from a state with the binding ready is read off the image
(`Vegas.binding_round_image_congr`): only the owner's commitment to the event
can be accepted, its acceptance reads public data, and its result is the
recorded status.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Whether a candidate binds a successful value at a binding of a payload
type. -/
def candidateSucceeds (state : EventGraphRuntime.State (graph setup))
    (candidate : Handle (graph setup)) (payload : L.Ty) : Bool :=
  match state.bindingResult candidate payload with
  | .success _ => true
  | .failure => false

/-- The status of a packet: for a commitment of the owner to the event, its
identifier and whether its candidate succeeds; nothing otherwise. -/
def commitStatus (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (state : EventGraphRuntime.State (graph setup))
    (message : Message Player (application setup leaks).Payload) :
    Option (MessageId Player × Bool) :=
  match message.payload.call with
  | .commitment named candidate =>
      if named = event ∧ message.sender = owner then
        some (message.id, candidateSucceeds state candidate payload)
      else none
  | _ => none

/-- The statuses of the owner's commitments to the event in a list of packets. -/
def commitStatuses (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (state : EventGraphRuntime.State (graph setup))
    (packets : List (Message Player (application setup leaks).Payload)) :
    List (MessageId Player × Bool) :=
  packets.filterMap (commitStatus event owner payload state)

/-- Whether a packet has a status does not depend on the contract state. -/
theorem commitStatus_isSome_congr (event : (graph setup).EventId) (owner : Player)
    (payload : L.Ty) (first second : EventGraphRuntime.State (graph setup))
    (message : Message Player (application setup leaks).Payload) :
    (commitStatus event owner payload first message).isSome =
      (commitStatus event owner payload second message).isSome := by
  unfold commitStatus
  split
  · split <;> rfl
  · rfl

/-- Equal statuses of a list are equal packet by packet. -/
theorem commitStatus_eq_of_mem {event : (graph setup).EventId} {owner : Player}
    {payload : L.Ty} {first second : EventGraphRuntime.State (graph setup)} :
    ∀ {packets : List (Message Player (application setup leaks).Payload)},
    commitStatuses event owner payload first packets =
      commitStatuses event owner payload second packets →
    ∀ message ∈ packets, commitStatus event owner payload first message =
      commitStatus event owner payload second message
  | [], _, _, member => by cases member
  | head :: rest, same, message, member => by
      have someEq := commitStatus_isSome_congr event owner payload first second head
      unfold commitStatuses at same
      cases firstHead : commitStatus event owner payload first head with
      | none =>
          cases secondHead : commitStatus event owner payload second head with
          | none =>
              rw [List.filterMap_cons_none firstHead, List.filterMap_cons_none secondHead] at same
              rcases List.mem_cons.mp member with rfl | inside
              · rw [firstHead, secondHead]
              · exact commitStatus_eq_of_mem same message inside
          | some _ => rw [firstHead, secondHead] at someEq; cases someEq
      | some firstStatus =>
          cases secondHead : commitStatus event owner payload second head with
          | none => rw [firstHead, secondHead] at someEq; cases someEq
          | some secondStatus =>
              rw [List.filterMap_cons_some firstHead, List.filterMap_cons_some secondHead]
                at same
              obtain ⟨headEq, restEq⟩ := List.cons.inj same
              rcases List.mem_cons.mp member with rfl | inside
              · rw [firstHead, secondHead, headEq]
              · exact commitStatus_eq_of_mem restEq message inside

/-- Removing a packet keeps equal statuses equal. -/
theorem commitStatuses_removeFirst_congr {event : (graph setup).EventId} {owner : Player}
    {payload : L.Ty} {first second : EventGraphRuntime.State (graph setup)}
    (id : MessageId Player) :
    ∀ {packets : List (Message Player (application setup leaks).Payload)},
    commitStatuses event owner payload first packets =
      commitStatuses event owner payload second packets →
    commitStatuses event owner payload first (MessagePool.removeFirst id packets) =
      commitStatuses event owner payload second (MessagePool.removeFirst id packets)
  | [], _ => rfl
  | head :: rest, same => by
      have headEq := commitStatus_eq_of_mem same head List.mem_cons_self
      have restEq : commitStatuses event owner payload first rest =
          commitStatuses event owner payload second rest := by
        unfold commitStatuses at same ⊢
        rw [List.filterMap_cons, List.filterMap_cons, headEq] at same
        cases status : commitStatus event owner payload second head with
        | none =>
            simp only [status] at same
            exact same
        | some _ =>
            simp only [status] at same
            exact (List.cons.inj same).2
      unfold MessagePool.removeFirst
      split
      · exact restEq
      · unfold commitStatuses at restEq ⊢
        rw [List.filterMap_cons, List.filterMap_cons, headEq]
        have tail := commitStatuses_removeFirst_congr id restEq
        unfold commitStatuses at tail
        rw [tail]

/-- Statuses read candidates only through their lookups. -/
theorem commitStatuses_congr_candidates {event : (graph setup).EventId} {owner : Player}
    {payload : L.Ty} {first second : EventGraphRuntime.State (graph setup)}
    (candidates : first.candidates = second.candidates)
    (packets : List (Message Player (application setup leaks).Payload)) :
    commitStatuses event owner payload first packets =
      commitStatuses event owner payload second packets := by
  have succeeds : ∀ candidate, candidateSucceeds first candidate payload =
      candidateSucceeds second candidate payload := fun candidate => by
    simp only [candidateSucceeds, EventGraphRuntime.State.bindingResult, candidates]
  unfold commitStatuses
  congr 1
  funext message
  unfold commitStatus
  split
  · rw [succeeds]
  · rfl

/-- The statuses of a protocol state. -/
def stateStatuses (event : (graph setup).EventId) (owner : Player) (payload : L.Ty) :
    (application setup leaks).ProtocolState → List (MessageId Player × Bool)
  | none => []
  | some control => commitStatuses event owner payload control.execution.application
      control.execution.network.pending

/-- The image at a pending binding. -/
abbrev BindingImage :=
  (Option (OperationalState setup leaks) × List (MessageId Player × Bool)) ⊕ Bool

/-- Attach statuses to a pending image. -/
def attachStatuses (statuses : List (MessageId Player × Bool)) :
    PendingImage (setup := setup) (leaks := leaks) → BindingImage (setup := setup) (leaks := leaks)
  | .inl state => .inl (state, statuses)
  | .inr failed => .inr failed

/-- **The image at a pending binding.** The pending image, with the statuses
of the owner's pending commitments to the event while it is pending. -/
def bindingImage (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (state : (application setup leaks).ProtocolState) :
    BindingImage (setup := setup) (leaks := leaks) :=
  attachStatuses (stateStatuses event owner payload state) (pendingImage event state)

/-- A step keeping the statuses is read through the pending image. -/
theorem map_bindingImage_of_statuses {X : Type} (law : PMF X)
    (state : X → (application setup leaks).ProtocolState) {event : (graph setup).EventId}
    {owner : Player} {payload : L.Ty} (statuses : List (MessageId Player × Bool))
    (kept : ∀ next ∈ law.support, stateStatuses event owner payload (state next) = statuses) :
    law.map (fun next => bindingImage event owner payload (state next)) =
      (law.map fun next => pendingImage event (state next)).map (attachStatuses statuses) := by
  rw [PMF.map_comp]
  apply map_congr_on_support
  intro next member
  simp only [bindingImage, Function.comp, kept next member]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- The failed result of a binding is a failure of its field. -/
theorem isFailure_cast_binding_failure {kind : EventGraph.EventField Player L} {owner : Player}
    {payload : L.Ty} (kindEq : kind = .binding owner payload) :
    kind.IsFailure (cast (congrArg EventGraph.EventField.Value kindEq.symm)
      (PublicationResult.failure : PublicationResult (L.Val payload))) := by
  subst kindEq
  rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A binding result fails exactly when it is the failure. -/
theorem isFailure_cast_binding_iff {kind : EventGraph.EventField Player L} {owner : Player}
    {payload : L.Ty} (kindEq : kind = .binding owner payload)
    (result : PublicationResult (L.Val payload)) :
    kind.IsFailure (cast (congrArg EventGraph.EventField.Value kindEq.symm) result) ↔
      result = .failure := by
  subst kindEq
  rfl

open Classical in
/-- Expiring a due binding fails it, read through the pending image. -/
theorem environmentStep_expire_due_bind_image (remaining : Nat)
    (execution : (application setup leaks).Execution) {event : (graph setup).EventId}
    (ready : execution.application.config.cut.Ready event) (entered : Nat)
    (activated : execution.application.activatedAt event = some entered)
    (due : (runtime setup).deadline event ≤ execution.application.clock - entered)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (view : nodeView (graph setup) event = .bind owner payload outputEq codeEq) :
    (execution.environmentStep (application setup leaks) (.application (.expire event))).map
        (fun next => pendingImage event (some ⟨remaining, none, next⟩)) = PMF.pure (.inr true) := by
  unfold ReactiveApplication.Execution.environmentStep
  change (((EventGraphRuntime.environmentStep (runtime setup) execution.application
    (.expire event)).map _).map _).map _ = _
  rw [environmentStep_expire_bind_eq (runtime setup) _ event ready entered activated due owner
    payload outputEq codeEq view]
  simp only [PMF.pure_map]
  have completed : event ∈ (execution.application.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload)))
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload)))).config.cut.completed :=
    (EventOrder.Cut.mem_complete _ event ready event).mpr (Or.inl rfl)
  have failed : StoreEventFailed (execution.application.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload)))
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload)))).config.store event :=
    ⟨_, by simp [EventGraphRuntime.State.complete, EventGraph.Config.complete,
      EventGraph.Config.store], isFailure_cast_binding_failure outputEq⟩
  simp only [pendingImage, completed, ↓reduceIte, failed, decide_true]

/-- **Contract rounds at a pending binding read off the operational state.** -/
theorem application_image_congr_bind (remaining : Nat)
    (first second : (application setup leaks).Execution)
    (same : operationalState setup leaks (some ⟨remaining + 1, none, first⟩) =
      operationalState setup leaks (some ⟨remaining + 1, none, second⟩))
    {event : (graph setup).EventId}
    (ready : first.application.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (view : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (command : EnvironmentCommand (graph setup)) :
    (first.environmentStep (application setup leaks) (.application command)).map
        (fun next => pendingImage event (some ⟨remaining, none, next⟩)) =
      (second.environmentStep (application setup leaks) (.application command)).map
        (fun next => pendingImage event (some ⟨remaining, none, next⟩)) := by
  have pending := ready.1
  have pending' : event ∉ second.application.config.cut.completed := fun completed =>
    pending ((SameOperational.completed same event).mpr completed)
  have ready' : second.application.config.cut.Ready event :=
    (SameOperational.ready same event).mp ready
  have views : first.application.publicView = second.application.publicView :=
    SameOperational.publicView same
  have readyIff : ∀ other, first.application.config.cut.Ready other ↔
      second.application.config.cut.Ready other := SameOperational.ready same
  have stutterBoth : ∀ command,
      EventGraphRuntime.environmentStep (runtime setup) first.application command =
        PMF.pure first.application →
      EventGraphRuntime.environmentStep (runtime setup) second.application command =
        PMF.pure second.application →
      (first.environmentStep (application setup leaks) (.application command)).map
          (fun next => pendingImage event (some ⟨remaining, none, next⟩)) =
        (second.environmentStep (application setup leaks) (.application command)).map
          (fun next => pendingImage event (some ⟨remaining, none, next⟩)) := by
    intro command firstStutter secondStutter
    rw [environmentStep_stutter_image remaining first pending command firstStutter,
      environmentStep_stutter_image remaining second pending' command secondStutter, same, views]
  cases command with
  | advanceClock =>
      rw [environmentStep_contract_image remaining first pending _ (by
          intro next member
          simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at member
          rw [member]),
        environmentStep_contract_image remaining second pending' _ (by
          intro next member
          simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at member
          rw [member])]
      simp only [EventGraphRuntime.environmentStep, PMF.pure_map]
      rw [same]
      have ticked : ({ first.application with clock := first.application.clock + 1 } :
          EventGraphRuntime.State (graph setup)).publicView =
          ({ second.application with clock := second.application.clock + 1 } :
            EventGraphRuntime.State (graph setup)).publicView := by
        change ({ first.application.publicView with
            clock := first.application.publicView.clock + 1 } : PublicView (graph setup)) =
          { second.application.publicView with clock := second.application.publicView.clock + 1 }
        rw [views]
      rw [ticked]
  | executeSample sampled =>
      by_cases sampledReady : first.application.config.cut.Ready sampled
      · have sameEvent : sampled = event := ready_unique (setup := setup) _ sampledReady ready
        subst sameEvent
        exact stutterBoth _
          (environmentStep_executeSample_of_nonsample (runtime setup) _ sampled ready
            (fun _ _ _ _ other => by rw [view] at other; cases other))
          (environmentStep_executeSample_of_nonsample (runtime setup) _ sampled ready'
            (fun _ _ _ _ other => by rw [view] at other; cases other))
      · exact stutterBoth _
          (environmentStep_executeSample_of_not_ready (runtime setup) _ sampled sampledReady)
          (environmentStep_executeSample_of_not_ready (runtime setup) _ sampled
            (fun other => sampledReady ((readyIff sampled).mpr other)))
  | expire expired =>
      by_cases expiredReady : first.application.config.cut.Ready expired
      · have sameEvent : expired = event := ready_unique (setup := setup) _ expiredReady ready
        subst sameEvent
        have activations : first.application.activatedAt = second.application.activatedAt :=
          congrArg PublicView.activatedAt views
        have clocks : first.application.clock = second.application.clock :=
          congrArg PublicView.clock views
        cases activated : first.application.activatedAt expired with
        | none =>
            exact stutterBoth _
              (environmentStep_expire_of_not_activated (runtime setup) _ expired ready activated)
              (environmentStep_expire_of_not_activated (runtime setup) _ expired ready'
                (by rw [← activations]; exact activated))
        | some entered =>
            by_cases due : (runtime setup).deadline expired ≤ first.application.clock - entered
            · rw [environmentStep_expire_due_bind_image remaining first ready entered activated
                  due view,
                environmentStep_expire_due_bind_image remaining second ready' entered
                  (by rw [← activations]; exact activated) (by rw [← clocks]; exact due) view]
            · exact stutterBoth _
                (environmentStep_expire_of_not_due (runtime setup) _ expired ready entered
                  activated due)
                (environmentStep_expire_of_not_due (runtime setup) _ expired ready' entered
                  (by rw [← activations]; exact activated) (by rw [← clocks]; exact due))
      · exact stutterBoth _
          (environmentStep_expire_of_not_ready (runtime setup) _ expired expiredReady)
          (environmentStep_expire_of_not_ready (runtime setup) _ expired
            (fun other => expiredReady ((readyIff expired).mpr other)))

/-- **Only the owner's commitment is accepted while a binding is ready.** -/
theorem handle_of_binding_ready (state : EventGraphRuntime.State (graph setup))
    {event : (graph setup).EventId} (ready : state.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (view : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (id : MessageId Player) (call : Payload (graph setup))
    {next : EventGraphRuntime.State (graph setup)}
    (accepted : EventGraphRuntime.handle (runtime setup) state ⟨id, call⟩ = some next) :
    ∃ candidate, call = .commitment event candidate ∧ id.1 = owner := by
  cases call with
  | malformed raw => simp [EventGraphRuntime.handle] at accepted
  | commitment named candidate =>
      by_cases namedReady : state.config.cut.Ready named
      · have same : named = event := ready_unique (setup := setup) _ namedReady ready
        subst same
        refine ⟨candidate, rfl, ?_⟩
        by_contra foreign
        by_cases timely : state.WithinDeadline (runtime setup) named
        · simp [EventGraphRuntime.handle, namedReady, timely, view, Message.sender, foreign]
            at accepted
        · simp [EventGraphRuntime.handle, namedReady, timely] at accepted
      · simp [EventGraphRuntime.handle, namedReady] at accepted
  | opening named candidate raw =>
      by_cases namedReady : state.config.cut.Ready named
      · have same : named = event := ready_unique (setup := setup) _ namedReady ready
        subst same
        by_cases timely : state.WithinDeadline (runtime setup) named
        · simp [EventGraphRuntime.handle, namedReady, timely, view] at accepted
        · simp [EventGraphRuntime.handle, namedReady, timely] at accepted
      · simp [EventGraphRuntime.handle, namedReady] at accepted

/-- An accepted commitment to a ready binding was timely, sent by its owner for
an unused own handle while the binding was vacant, and completes the binding
with the handle's typed meaning. -/
theorem handle_commitment_accepted_facts (state : EventGraphRuntime.State (graph setup))
    {event : (graph setup).EventId} (ready : state.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (view : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (id : MessageId Player) (candidate : Handle (graph setup))
    {next : EventGraphRuntime.State (graph setup)}
    (accepted : EventGraphRuntime.handle (runtime setup) state
      ⟨id, .commitment event candidate⟩ = some next) :
    state.WithinDeadline (runtime setup) event ∧ id.1 = owner ∧ candidate.1 = owner ∧
      state.accepted (.inr event) = none ∧ state.HandleUnused candidate := by
  by_cases timely : state.WithinDeadline (runtime setup) event
  · by_cases sender : id.1 = owner
    · by_cases owned : candidate.1 = owner
      · by_cases vacant : state.accepted (.inr event) = none
        · by_cases unused : state.HandleUnused candidate
          · exact ⟨timely, sender, owned, vacant, unused⟩
          · simp [EventGraphRuntime.handle, ready, timely, view, Message.sender, sender, owned,
              vacant, unused] at accepted
        · simp [EventGraphRuntime.handle, ready, timely, view, Message.sender, sender, owned,
            vacant] at accepted
      · simp [EventGraphRuntime.handle, ready, timely, view, Message.sender, sender, owned]
          at accepted
    · simp [EventGraphRuntime.handle, ready, timely, view, Message.sender, sender] at accepted
  · simp [EventGraphRuntime.handle, ready, timely] at accepted

/-- **An accepted commitment transfers across equal public data.** Two contract
states with the same public view, whose candidates for a handle agree on
success, accept the same commitment to a ready binding together; both
acceptances complete the binding, failed in one exactly when failed in the
other. -/
theorem handle_commitment_accepted_transfer
    (first second : EventGraphRuntime.State (graph setup))
    (publics : first.publicView = second.publicView)
    {event : (graph setup).EventId} (ready : first.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (view : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (id : MessageId Player) (candidate : Handle (graph setup))
    (succeeds : candidateSucceeds first candidate payload =
      candidateSucceeds second candidate payload)
    {next : EventGraphRuntime.State (graph setup)}
    (accepted : EventGraphRuntime.handle (runtime setup) first
      ⟨id, .commitment event candidate⟩ = some next) :
    ∃ next', EventGraphRuntime.handle (runtime setup) second
        ⟨id, .commitment event candidate⟩ = some next' ∧
      event ∈ next.config.cut.completed ∧ event ∈ next'.config.cut.completed ∧
      (StoreEventFailed next.config.store event ↔ StoreEventFailed next'.config.store event) := by
  obtain ⟨timely, sender, owned, vacant, unused⟩ :=
    handle_commitment_accepted_facts first ready view id candidate accepted
  have ready' : second.config.cut.Ready event := by
    rw [← EventGraphRuntime.State.publicView_eventReady, ← publics,
      EventGraphRuntime.State.publicView_eventReady]
    exact ready
  have acceptedEq : first.accepted = second.accepted := congrArg PublicView.accepted publics
  have activations : first.activatedAt = second.activatedAt :=
    congrArg PublicView.activatedAt publics
  have clocks : first.clock = second.clock := congrArg PublicView.clock publics
  have timely' : second.WithinDeadline (runtime setup) event := by
    unfold EventGraphRuntime.State.WithinDeadline at timely ⊢
    rw [← activations, ← clocks]
    exact timely
  have vacant' : second.accepted (.inr event) = none := by rw [← acceptedEq]; exact vacant
  have unused' : second.HandleUnused candidate := by
    unfold EventGraphRuntime.State.HandleUnused at unused ⊢
    rw [← acceptedEq]
    exact unused
  rw [EventGraphRuntime.handle_commitment_eq (runtime setup) first id event candidate owner payload
    outputEq codeEq view ready timely sender owned vacant unused] at accepted
  cases accepted
  refine ⟨_, EventGraphRuntime.handle_commitment_eq (runtime setup) second id event candidate owner
    payload outputEq codeEq view ready' timely' sender owned vacant' unused',
    (EventOrder.Cut.mem_complete _ event ready event).mpr (Or.inl rfl),
    (EventOrder.Cut.mem_complete _ event ready' event).mpr (Or.inl rfl), ?_⟩
  have firstStore := complete_store_output first ready
    (cast (congrArg EventGraph.EventField.Action outputEq.symm)
      (first.bindingResult candidate payload))
    (cast (congrArg EventGraph.EventField.Value outputEq.symm)
      (first.bindingResult candidate payload))
  have secondStore := complete_store_output second ready'
    (cast (congrArg EventGraph.EventField.Action outputEq.symm)
      (second.bindingResult candidate payload))
    (cast (congrArg EventGraph.EventField.Value outputEq.symm)
      (second.bindingResult candidate payload))
  have failedIff : ∀ result : PublicationResult (L.Val payload),
      ((graph setup).layout (.inr event)).IsFailure
        (cast (congrArg EventGraph.EventField.Value outputEq.symm) result) ↔
        result = .failure := isFailure_cast_binding_iff outputEq
  have successIff : ∀ state : EventGraphRuntime.State (graph setup),
      state.bindingResult candidate payload = .failure ↔
        candidateSucceeds state candidate payload = false := by
    intro state
    unfold candidateSucceeds
    cases state.bindingResult candidate payload <;> simp
  change StoreEventFailed (first.complete event ready _ _).config.store event ↔
    StoreEventFailed (second.complete event ready' _ _).config.store event
  simp only [StoreEventFailed, firstStore, secondStore, Option.some.injEq, exists_eq_left',
    failedIff, successIff, succeeds]

open Classical in
/-- **Inclusions at a pending binding read off the image.** Two executions with
the same operational state and the same statuses, with a binding ready, give
every inclusion the same law of images. -/
theorem include_bindingImage_congr (remaining : Nat)
    (first second : (application setup leaks).Execution)
    (same : operationalState setup leaks (some ⟨remaining + 1, none, first⟩) =
      operationalState setup leaks (some ⟨remaining + 1, none, second⟩))
    {event : (graph setup).EventId} {owner : Player} {payload : L.Ty}
    (statuses : commitStatuses event owner payload first.application first.network.pending =
      commitStatuses event owner payload second.application second.network.pending)
    (ready : first.application.config.cut.Ready event)
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (view : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (id : MessageId Player) :
    (first.environmentStep (application setup leaks) (.include id)).map
        (fun next => bindingImage event owner payload (some ⟨remaining, none, next⟩)) =
      (second.environmentStep (application setup leaks) (.include id)).map
        (fun next => bindingImage event owner payload (some ⟨remaining, none, next⟩)) := by
  have pending := ready.1
  have ready' : second.application.config.cut.Ready event :=
    (SameOperational.ready same event).mp ready
  have networks : first.network = second.network := SameOperational.network same
  have publics : first.application.publicView = second.application.publicView :=
    SameOperational.publicView same
  have statuses' : commitStatuses event owner payload first.application first.network.pending =
      commitStatuses event owner payload second.application first.network.pending := by
    rw [statuses, networks]
  have rejectedBoth (message : Message Player (application setup leaks).Payload)
      (found : first.network.lookup id = some message)
      (firstRejected : (application setup leaks).handle first.application message = none)
      (secondRejected : (application setup leaks).handle second.application message = none) :
      (first.environmentStep (application setup leaks) (.include id)).map
          (fun next => bindingImage event owner payload (some ⟨remaining, none, next⟩)) =
        (second.environmentStep (application setup leaks) (.include id)).map
          (fun next => bindingImage event owner payload (some ⟨remaining, none, next⟩)) := by
    have found' : second.network.lookup id = some message := by rw [← networks]; exact found
    have kept (execution : (application setup leaks).Execution)
        (lookup : execution.network.lookup id = some message)
        (rejected : (application setup leaks).handle execution.application message = none) :
        ∀ next ∈ (execution.environmentStep (application setup leaks) (.include id)).support,
          stateStatuses event owner payload (some ⟨remaining, none, next⟩) =
            commitStatuses event owner payload execution.application
              (MessagePool.removeFirst id execution.network.pending) := by
      intro next member
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at member
      subst member
      simp only [stateStatuses, ReactiveApplication.Execution.includePending,
        MessageNetwork.includePending, lookup, rejected, Option.getD_none]
    rw [map_bindingImage_of_statuses _ _ _ (kept first found firstRejected),
      map_bindingImage_of_statuses _ _ _ (kept second found' secondRejected),
      include_image_congr remaining first second same pending id (fun other member => by
        rw [found] at member
        cases member
        exact ⟨firstRejected, secondRejected⟩),
      ← networks, commitStatuses_removeFirst_congr id statuses']
  cases found : first.network.lookup id with
  | none =>
      have found' : second.network.lookup id = none := by rw [← networks]; exact found
      have kept (execution : (application setup leaks).Execution)
          (lookup : execution.network.lookup id = none) :
          ∀ next ∈ (execution.environmentStep (application setup leaks) (.include id)).support,
            stateStatuses event owner payload (some ⟨remaining, none, next⟩) =
              commitStatuses event owner payload execution.application
                execution.network.pending := by
        intro next member
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
          PMF.mem_support_pure_iff] at member
        subst member
        simp only [stateStatuses, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, lookup]
      rw [map_bindingImage_of_statuses _ _ _ (kept first found),
        map_bindingImage_of_statuses _ _ _ (kept second found'),
        include_image_congr remaining first second same pending id (fun other member => by
          rw [found] at member
          cases member), ← networks, statuses']
  | some message =>
      have member : message ∈ first.network.pending := List.mem_of_find?_eq_some found
      have transfer (one other : EventGraphRuntime.State (graph setup))
          (publicsEq : one.publicView = other.publicView)
          (oneReady : one.config.cut.Ready event)
          (succeeds : ∀ candidate, message.payload.call = .commitment event candidate →
            message.sender = owner →
            candidateSucceeds one candidate payload = candidateSucceeds other candidate payload)
          {next : EventGraphRuntime.State (graph setup)}
          (accepted : (application setup leaks).handle one message = some next) :
          ∃ next', (application setup leaks).handle other message = some next' ∧
            event ∈ next.config.cut.completed ∧ event ∈ next'.config.cut.completed ∧
            (StoreEventFailed next.config.store event ↔
              StoreEventFailed next'.config.store event) := by
        obtain ⟨valid, handled⟩ :=
          reactiveApplication_handle_eq_some (runtime setup) leaks one next message accepted
        obtain ⟨candidate, call, sender⟩ :=
          handle_of_binding_ready one oneReady view message.id message.payload.call handled
        rw [call] at handled
        obtain ⟨next', handled', facts⟩ := handle_commitment_accepted_transfer one other
          publicsEq oneReady view message.id candidate (succeeds candidate call sender) handled
        refine ⟨next', ?_, facts⟩
        rw [reactiveApplication_handle_of_tokenValid (runtime setup) leaks _ _ valid, call]
        exact handled'
      have succeeds : ∀ candidate, message.payload.call = .commitment event candidate →
          message.sender = owner →
          candidateSucceeds first.application candidate payload =
            candidateSucceeds second.application candidate payload := by
        intro candidate call sender
        have statusEq := commitStatus_eq_of_mem statuses' message member
        unfold commitStatus at statusEq
        rw [call] at statusEq
        simp only [true_and, sender, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at statusEq
        exact statusEq
      have found' : second.network.lookup id = some message := by rw [← networks]; exact found
      cases firstHandle : (application setup leaks).handle first.application message with
      | none =>
          cases secondHandle : (application setup leaks).handle second.application message with
          | none => exact rejectedBoth message found firstHandle secondHandle
          | some _ =>
              obtain ⟨_, back, _⟩ := transfer second.application first.application publics.symm
                ready' (fun candidate call sender => (succeeds candidate call sender).symm)
                secondHandle
              rw [firstHandle] at back
              cases back
      | some _ =>
          obtain ⟨_, secondHandle, completed, completed', failed⟩ :=
            transfer first.application second.application publics ready succeeds firstHandle
          unfold ReactiveApplication.Execution.environmentStep
          simp only [PMF.pure_map]
          congr 1
          unfold ReactiveApplication.Execution.includePending
          simp only [MessageNetwork.includePending, found, found', firstHandle, secondHandle,
            Option.getD_some]
          simp only [bindingImage, pendingImage, completed, completed', ↓reduceIte,
            attachStatuses, Sum.inr.injEq, decide_eq_decide]
          exact failed

variable (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler) in
/-- **Scheduler rounds at a pending binding read off the image.** Two
executions with the same operational state and statuses, with a binding
ready, give a scheduler round the same law of images. -/
theorem binding_round_image_congr (remaining : Nat)
    (first second : (application setup leaks).Execution)
    (same : operationalState setup leaks (some ⟨remaining + 1, none, first⟩) =
      operationalState setup leaks (some ⟨remaining + 1, none, second⟩))
    {event : (graph setup).EventId} {owner : Player} {payload : L.Ty}
    (statuses : commitStatuses event owner payload first.application first.network.pending =
      commitStatuses event owner payload second.application second.network.pending)
    (ready : first.application.config.cut.Ready event)
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload}
    (view : nodeView (graph setup) event = .bind owner payload outputEq codeEq) :
    ((application setup leaks).transition initial horizon scheduler
        (some ⟨remaining + 1, none, first⟩) (fun _ => none)).map
        (bindingImage event owner payload) =
      ((application setup leaks).transition initial horizon scheduler
        (some ⟨remaining + 1, none, second⟩) (fun _ => none)).map
        (bindingImage event owner payload) := by
  have pending := ready.1
  have pending' : event ∉ second.application.config.cut.completed := fun completed =>
    pending ((SameOperational.completed same event).mpr completed)
  have networks : first.network = second.network := SameOperational.network same
  have recalls : first.environmentRecall = second.environmentRecall :=
    SameOperational.environmentRecall same
  have views : first.observeEnvironment (application setup leaks) =
      second.observeEnvironment (application setup leaks) :=
    SameOperational.observeEnvironment same
  change ((scheduler first.environmentRecall (first.observeEnvironment _)).bind fun command =>
      (first.environmentStep _ command).map fun next =>
        some (⟨remaining, command.actor? (application setup leaks), next⟩ :
          (application setup leaks).Control)).map (bindingImage event owner payload) =
    ((scheduler second.environmentRecall (second.observeEnvironment _)).bind fun command =>
      (second.environmentStep _ command).map fun next =>
        some (⟨remaining, command.actor? (application setup leaks), next⟩ :
          (application setup leaks).Control)).map (bindingImage event owner payload)
  rw [recalls, views, PMF.map_bind, PMF.map_bind]
  congr 1
  funext command
  rw [PMF.map_comp, PMF.map_comp]
  cases command with
  | activate who =>
      change (first.environmentStep _ (.activate who)).map
          (fun next => bindingImage event owner payload (some ⟨remaining, some who, next⟩)) =
        (second.environmentStep _ (.activate who)).map
          (fun next => bindingImage event owner payload (some ⟨remaining, some who, next⟩))
      have kept (execution : (application setup leaks).Execution) :
          ∀ next ∈ (execution.environmentStep (application setup leaks) (.activate who)).support,
            stateStatuses event owner payload (some ⟨remaining, some who, next⟩) =
              commitStatuses event owner payload execution.application
                execution.network.pending := by
        intro next member
        unfold ReactiveApplication.Execution.environmentStep at member
        rw [PMF.support_map] at member
        obtain ⟨updated, supported, rfl⟩ := member
        rw [PMF.support_map] at supported
        obtain ⟨_, _, rfl⟩ := supported
        rfl
      rw [map_bindingImage_of_statuses _ _ _ (kept first),
        map_bindingImage_of_statuses _ _ _ (kept second),
        environmentStep_activate_image remaining first pending who,
        environmentStep_activate_image remaining second pending' who, statuses, networks, same]
  | wait =>
      change (first.environmentStep _ .wait).map
          (fun next => bindingImage event owner payload (some ⟨remaining, none, next⟩)) =
        (second.environmentStep _ .wait).map
          (fun next => bindingImage event owner payload (some ⟨remaining, none, next⟩))
      have kept (execution : (application setup leaks).Execution) :
          ∀ next ∈ (execution.environmentStep (application setup leaks) .wait).support,
            stateStatuses event owner payload (some ⟨remaining, none, next⟩) =
              commitStatuses event owner payload execution.application
                execution.network.pending := by
        intro next member
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
          PMF.mem_support_pure_iff] at member
        subst member
        rfl
      rw [map_bindingImage_of_statuses _ _ _ (kept first),
        map_bindingImage_of_statuses _ _ _ (kept second),
        environmentStep_wait_image remaining first pending,
        environmentStep_wait_image remaining second pending', same, statuses]
  | «include» id =>
      exact include_bindingImage_congr remaining first second same statuses ready view id
  | application command =>
      change (first.environmentStep _ (.application command)).map
          (fun next => bindingImage event owner payload (some ⟨remaining, none, next⟩)) =
        (second.environmentStep _ (.application command)).map
          (fun next => bindingImage event owner payload (some ⟨remaining, none, next⟩))
      have kept (execution : (application setup leaks).Execution) :
          ∀ next ∈ (execution.environmentStep (application setup leaks)
            (.application command)).support,
            stateStatuses event owner payload (some ⟨remaining, none, next⟩) =
              commitStatuses event owner payload execution.application
                execution.network.pending := by
        intro next member
        unfold ReactiveApplication.Execution.environmentStep at member
        rw [PMF.support_map] at member
        obtain ⟨updated, supported, rfl⟩ := member
        rw [PMF.support_map] at supported
        obtain ⟨contract, stepped, rfl⟩ := supported
        exact commitStatuses_congr_candidates
          (EventGraphRuntime.environmentStep_tables (runtime setup) _ contract command
            stepped).2 _
      rw [map_bindingImage_of_statuses _ _ _ (kept first),
        map_bindingImage_of_statuses _ _ _ (kept second),
        application_image_congr_bind remaining first second same ready view command, statuses]

end Vegas
