/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceCanonicalConformance
import Vegas.Pending.ReactiveServiceAudit
import Vegas.Pending.ReactiveSettledStability
import GameTheory.Analysis.Protocol.CounterfactualDecomposition
import Interaction.ReactiveReceipts

/-! # Good packets and retained play

A packet is on track while its ready event is unfinished, or accepted with
its authenticated content recorded. Packet certificates and canonical binding
counts persist along finite graph paths. Responses preserve this property;
protected inclusion supplies acceptance for each prescribed owner's sole call.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Content

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The content a packet will settle with if accepted at this state is what the
record accepts. -/
def PendingContent (state : EventGraphRuntime.State (serviceGraph setup mode))
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop :=
  match message.payload.call with
  | .commitment _ candidate =>
      message.payload.evidence = none ∧
        candidate = (message.sender, .prepared (state.publicView.bindingCount message.sender))
  | .opening _ _ _ => certifiedOpening message.payload = true
  | .malformed _ => False

/-- A retained packet is on track, or accepted with the content the record
accepts. -/
def SettledGood (execution : (serviceApplication setup mode duration leaks).Execution)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode))) : Prop :=
  ∃ event, message.payload.call.event? (serviceGraph setup mode) = some event ∧
    ((execution.application.config.cut.Ready event ∧ (message.id, true) ∉ execution.receipts ∧
        PendingContent setup execution.application message) ∨
      ((message.id, true) ∈ execution.receipts ∧
        event ∈ execution.application.config.cut.completed ∧
        ((settledRecord (serviceTimeouts setup mode duration)) leaks execution).SettledContent
        message))

variable {setup leaks}

/-- A conforming packet's content is what the record accepts. -/
theorem pendingContent_of_fresh (state : EventGraphRuntime.State (serviceGraph setup mode))
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (fresh : (freshServiceEnvelope (serviceTimeouts setup mode duration)) state.publicView
      message) :
    PendingContent setup state message := by
  rcases message with ⟨id, ⟨call, evidence, token⟩⟩
  cases call with
  | commitment event candidate =>
      obtain ⟨_, canonical, empty, _⟩ :=
          ((freshServiceEnvelope_binding_iff (serviceTimeouts setup mode duration))
            state.publicView id
              event candidate evidence token).mp fresh
      exact ⟨empty, canonical⟩
  | opening event candidate raw =>
      unfold EventGraphRuntime.freshServiceEnvelope at fresh
      exact fresh.2.2.1
  | malformed raw => exact fresh.elim

/-- Accepting a packet whose pending content the record accepts settles that
content. -/
theorem settledContent_of_pending (before after : EventGraphRuntime.State (serviceGraph setup mode))
    (receipts : List (MessageId Player × Bool))
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (event : (serviceGraph setup mode).EventId)
    (named : message.payload.call.event? (serviceGraph setup mode) = some event)
    (ready : before.config.cut.Ready event) (action : (serviceGraph setup mode).Action event)
    (member : after.config ∈ (before.config.step event ready action).support)
    (pending : PendingContent setup before message) :
    (⟨after.publicView, receipts⟩ : SettledRecord (serviceGraph setup mode)).SettledContent
    message := by
  obtain ⟨value, _chosen, history⟩ := before.config.step_completion event ready action
    after.config member
  have orderEq : after.publicView.observation.completionOrder =
      before.publicView.observation.completionOrder ++ [event] := by
    change after.config.history.map EventCompletion.event = _
    rw [history, List.map_append, List.map_singleton]
    rfl
  have absent : event ∉ before.publicView.observation.completionOrder :=
    fun inside => ready.1 ((before.config.history_exact event).mp inside)
  rcases message with ⟨id, ⟨call, evidence, token⟩⟩
  cases call with
  | malformed raw => exact pending.elim
  | commitment actual candidate =>
      change some actual = some event at named
      cases Option.some.inj named
      obtain ⟨empty, canonical⟩ := pending
      refine ⟨empty, ?_⟩
      change candidate = (id.1, .prepared (before.publicView.bindingCount id.1)) at canonical
      change candidate = (id.1, .prepared (after.publicView.bindingCountBefore id.1 event))
      rw [canonical, PublicView.bindingCountBefore_complete before.publicView after.publicView
        id.1 event absent [] orderEq]
  | opening actual candidate raw => exact pending

/-- A good packet is permitted by the settled record. -/
theorem SettledGood.permits {execution : (serviceApplication setup mode duration leaks).Execution}
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (good : SettledGood setup leaks execution message) :
    ((settledRecord (serviceTimeouts setup mode duration)) leaks execution).permits message =
    true := by
  obtain ⟨event, named, ⟨ready, _, _⟩ | ⟨accepted, _, content⟩⟩ := good
  · exact SettledRecord.permits_of_unsettled _ message event named fun inside =>
      ready.1 ((execution.application.config.history_exact event).mp inside)
  · exact SettledRecord.permits_of_accepted _ message event named accepted content

/-- Pending content reads only the public observation. -/
theorem pendingContent_congr {first second : EventGraphRuntime.State (serviceGraph setup mode)}
    (same : second.publicView.observation = first.publicView.observation)
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (pending : PendingContent setup first message) : PendingContent setup second message := by
  unfold PendingContent at pending ⊢
  cases call : message.payload.call with
  | commitment event candidate =>
      simp only [call] at pending ⊢
      rw [PublicView.bindingCount_eq_countP, same, ← PublicView.bindingCount_eq_countP]
      exact pending
  | opening event candidate raw => simpa only [call] using pending
  | malformed raw => simp only [call] at pending

/-- Pending content is kept when another event, ready together with the
packet's event of the packet's author, completes: the author's binding count is
unchanged and authentic opening certificates are immutable. -/
theorem pendingContent_of_other_step
    {before after : EventGraphRuntime.State (serviceGraph setup mode)}
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    {event other : (serviceGraph setup mode).EventId}
    (owned : (serviceGraph setup mode).actor? event = some message.sender)
    (ready : before.config.cut.Ready event) (otherReady : before.config.cut.Ready other)
    (different : other ≠ event) {action : (serviceGraph setup mode).Action other}
    (member : after.config ∈ (before.config.step other otherReady action).support)
    (pending : PendingContent setup before message) : PendingContent setup after message := by
  obtain ⟨value, _chosen, historyEq⟩ := before.config.step_completion other otherReady action
    after.config member
  have orderEq : after.publicView.observation.completionOrder =
      before.publicView.observation.completionOrder ++ [other] := by
    change after.config.history.map EventCompletion.event = _
    rw [historyEq, List.map_append, List.map_singleton]
    rfl
  unfold PendingContent at pending ⊢
  cases call : message.payload.call with
  | commitment actual candidate =>
      simp only [call] at pending ⊢
      refine ⟨pending.1, pending.2.trans ?_⟩
      have foreign : bindingOwnedBy (serviceGraph setup mode) message.sender other = false := by
        obtain ⟨otherOwner, eventOwner, otherActor, eventActor, owners⟩ :=
          (serviceGraph_revealRelaxedOrdered setup mode).ready_pair_actors otherReady ready
            different
        rw [owned] at eventActor
        unfold bindingOwnedBy
        cases kind : (serviceGraph setup mode).outputLayout other with
        | binding owner payload =>
            have actorIs := (serviceGraph setup mode).actor?_of_outputLayout_binding kind
            rw [otherActor] at actorIs
            simp only [decide_eq_false_iff_not]
            intro same
            exact owners ((Option.some.inj actorIs).trans
              (same.trans (Option.some.inj eventActor)))
        | publicData _ => rfl
        | privateInput _ _ => rfl
        | publication _ => rfl
      rw [PublicView.bindingCount_eq_countP, PublicView.bindingCount_eq_countP, orderEq,
        List.countP_append]
      simp [foreign]
  | opening actual candidate raw => simpa only [call] using pending
  | malformed raw => simp only [call] at pending

/-- Pending content persists along any graph path that leaves its owner's
ready event unfinished. -/
theorem pendingContent_of_path
    {before after : EventGraphRuntime.State (serviceGraph setup mode)}
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    {event : (serviceGraph setup mode).EventId}
    (owned : (serviceGraph setup mode).actor? event = some message.sender)
    (ready : before.config.cut.Ready event)
    (path : Relation.ReflTransGen EventGraph.Config.Step before.config after.config)
    (unfinished : event ∉ after.config.cut.completed)
    (pending : PendingContent setup before message) : PendingContent setup after message := by
  have keep : ∀ {start finish : (serviceGraph setup mode).Config},
      Relation.ReflTransGen EventGraph.Config.Step start finish →
      start.cut.Ready event → event ∉ finish.cut.completed →
      PendingContent setup { before with config := start } message →
      PendingContent setup { before with config := finish } message := by
    intro start finish steps
    induction steps using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun _ _ content => content
    | @head start middle moved rest ih =>
        intro currentReady notDone content
        have unfinishedMiddle : event ∉ middle.cut.completed :=
          fun done => notDone (EventGraph.Config.Step.path_completed_mono rest done)
        obtain ⟨other, otherReady, action, supported⟩ := moved
        have different : other ≠ event := by
          intro equal
          subst other
          apply unfinishedMiddle
          rw [start.step_cut event otherReady action middle supported]
          exact Finset.mem_insert_self _ _
        have middleReady : middle.cut.Ready event :=
          ⟨unfinishedMiddle, fun predecessor member =>
            EventGraph.Config.Step.completed_mono ⟨other, otherReady, action, supported⟩
              (currentReady.2 member)⟩
        exact ih middleReady notDone
          (pendingContent_of_other_step
            (before := { before with config := start })
            (after := { before with config := middle })
            owned currentReady otherReady different supported content)
  exact pendingContent_congr rfl (keep path ready unfinished pending)

/-- A submission names the event its emitted packet addresses. -/
theorem submittedEvent_of_issued
    {entry : (serviceApplication setup mode duration leaks).PlayerEntry}
    {material : (serviceApplication setup mode duration leaks).Submission}
    (transmission : entry.action.transmission = some material)
    {state : EventGraphRuntime.State (serviceGraph setup mode)} {who : Player}
    {known : List (Message Player (WitnessedPacket (serviceGraph setup mode)))}
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (packet : (serviceApplication setup mode duration leaks).packet state who known material =
        message.payload) : (submittedEvent? (serviceTimeouts setup mode duration)) leaks
          entry.action =
      message.payload.call.event? (serviceGraph setup mode) := by
  unfold EventGraphRuntime.submittedEvent?
  rw [transmission, ← packet]
  rfl

end Content

section Retained

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

variable {setup leaks}

/-- A response keeps a packet good: it changes no contract state or receipt. -/
theorem SettledGood.respond {execution : (serviceApplication setup mode duration leaks).Execution}
    {message : Message Player (WitnessedPacket (serviceGraph setup mode))}
    (good : SettledGood setup leaks execution message) (who : Player)
    (action : (serviceApplication setup mode duration leaks).Action) :
    SettledGood setup leaks
        (execution.respond (serviceApplication setup mode duration leaks) who action) message := by
  obtain ⟨configEq, publicEq⟩ := (reactive_respond_application (serviceTimeouts setup mode
    duration))
      leaks execution who action
  have receiptsEq := (serviceApplication setup mode duration leaks).respond_receipts execution
      who action
  obtain ⟨event, named, ⟨ready, unaccepted, pending⟩ | ⟨accepted, completed, content⟩⟩ := good
  · refine ⟨event, named, Or.inl ⟨configEq ▸ ready, receiptsEq ▸ unaccepted, ?_⟩⟩
    exact pendingContent_congr (congrArg PublicView.observation publicEq) pending
  · refine ⟨event, named, Or.inr ⟨receiptsEq ▸ accepted, configEq ▸ completed, ?_⟩⟩
    unfold settledRecord at content ⊢
    rw [publicEq, receiptsEq]
    exact content

end Retained

end Vegas
