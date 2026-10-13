/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketOwnerStep

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

end Vegas
