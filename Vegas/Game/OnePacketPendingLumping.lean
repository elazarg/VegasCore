/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketPathwise
import Vegas.Game.OnePacketActorRecord
import Vegas.Game.OnePacketEventFailure
import Vegas.Pending.ReactiveAssociationEvidence

/-! # One step of the native kernel while a forced owner's event is pending

**Decoded policies stay in the menu.** The native policy decoded from a
behavioral policy of a response menu chooses only actions of the menu
(`Interaction.ReactiveApplication.ResponseMenu.decodeProfile_support`).

**Silent responses.** A silent response changes the operational state only by
clearing the actor and appending the responder's current operational view,
with no emission, to its recalled views (`Vegas.operationalState_silent`).
While a forced owner's event is pending, another player's control step is that
silent response surely (`Vegas.controlStep_other_of_pending`).
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

/-- The decoded native policy of a menu policy chooses only menu actions. -/
theorem decodeProfile_support
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Principal) (past : List app.PlayerEntry) (view : app.PlayerView)
    (action : app.Action)
    (chosen : action ∈ (menu.decodeProfile initial horizon scheduler profile who past
      view).support) :
    action ∈ menu.actions who past view := by
  unfold decodeProfile ReactiveApplication.decodePolicy embedPolicy at chosen
  rw [PMF.map_comp, PMF.support_map] at chosen
  obtain ⟨choice, _, rfl⟩ := chosen
  obtain ⟨action, member, same⟩ := choice.2
  change (choice.1.getD ⟨none⟩) ∈ _
  rw [same]
  exact member

end Interaction.ReactiveApplication.ResponseMenu

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Append a responder's current operational view, with no emission, to its
recalled views, and clear the actor. -/
def OperationalState.silent (responder : Player) (state : OperationalState setup runtime leaks) :
    OperationalState setup runtime leaks :=
  { state with
    actor := none
    keys := fun who => if who = responder then (state.keys who).map fun key =>
      { key with recalled := key.recalled ++
        [(key.current, none)] } else state.keys who }

/-- **A silent response on the operational state.** -/
theorem operationalState_silent (control : (application setup runtime leaks).Control)
    (responder : Player) :
    operationalState setup runtime leaks (some { control with
      actor := none
      execution := control.execution.respond (application setup runtime leaks) responder ⟨none⟩ }) =
      (operationalState setup runtime leaks (some control)).map
        (OperationalState.silent (runtime := runtime) responder) := by
  simp only [operationalState, Option.map_some, OperationalState.silent, Option.some.injEq,
    OperationalState.mk.injEq]
  refine ⟨trivial, trivial, rfl, rfl, rfl, ?_⟩
  funext who
  by_cases same : who = responder
  · subst same
    simp only [↓reduceIte, Option.map_some, lateKey, ReactiveApplication.Execution.respond,
      List.map_append, List.map_cons, List.map_nil]
    rfl
  · simp only [same, ↓reduceIte]
    rw [(application setup runtime leaks).respond_recall_other control.execution responder who same]
    rfl

/-- A scheduler round on the operational state: the remaining rounds and actor
are set, and the round's command is recorded with the scheduler's view. -/
def OperationalState.round (remaining : Nat) (actor : Option Player)
    (command : (application setup runtime leaks).Command) (state : OperationalState setup runtime
      leaks) :
    OperationalState setup runtime leaks :=
  { state with
    remaining := remaining
    actor := actor
    environmentRecall := state.environmentRecall ++
      [⟨state.environment, command⟩] }

/-- An activation's observation on the operational state: the activated player
learns the selected pending packets, and every player's current operational
view reads the new network. -/
def OperationalState.learn (who : Player) (selected : Finset (MessageId Player))
    (state : OperationalState setup runtime leaks) : OperationalState setup runtime leaks :=
  { state with
    leaked := (state.network.learn who selected).leaked
    keys := fun observer => (state.keys observer).map
      fun key =>
      { key with current := (key.current.1,
        (state.network.learn who selected).observe observer,
        key.current.2.2) } }

/-- **An activation on the operational state.** -/
theorem operationalState_activate (remaining : Nat)
    (execution : (application setup runtime leaks).Execution)
    (who : Player) (selected : Finset (MessageId Player)) :
    operationalState setup runtime leaks (some ⟨remaining, some who,
      { execution with
        network := execution.network.learn who selected
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment (application setup runtime leaks), .activate who⟩] }⟩) =
      (operationalState setup runtime leaks (some ⟨remaining + 1, none, execution⟩)).map fun state
        =>
        (state.learn who selected).round remaining (some
          who) (.activate who) := by
  simp only [operationalState, Option.map_some, OperationalState.round, OperationalState.learn,
    Option.some.injEq, OperationalState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

/-- **Waiting on the operational state.** -/
theorem operationalState_wait (remaining : Nat)
    (execution : (application setup runtime leaks).Execution) :
    operationalState setup runtime leaks (some ⟨remaining, none,
      { execution with
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment (application setup runtime leaks), .wait⟩] }⟩) =
      (operationalState setup runtime leaks (some ⟨remaining + 1, none, execution⟩)).map fun state
        =>
        state.round remaining none .wait := by
  simp only [operationalState, Option.map_some, OperationalState.round, Option.some.injEq,
    OperationalState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

/-- A player's turn is read from the completion order alone. -/
private theorem publicView_ownTurn?_congr {first second : PublicView (graph setup)}
    (same : first.observation = second.observation) (who : Player) :
    first.ownTurn? who = second.ownTurn? who := by
  simp only [PublicView.ownTurn?, PublicView.EventReady, same]

/-- The delivered value of a view is read from the player's turn and its own
observation. -/
theorem deliveredValue_congr (who : Player) {first second : (application setup runtime
  leaks).PlayerView}
    (turn : first.application.publicView.ownTurn? who =
      second.application.publicView.ownTurn? who)
    (store : first.application.observation.store = second.application.observation.store) :
    deliveredValue setup runtime leaks who first = deliveredValue setup runtime leaks who second
      := by
  unfold deliveredValue
  rw [turn, store]

/-- A new public contract view on the operational state: the scheduler's view
and every player's current operational view read it. -/
def OperationalState.contract (view : PublicView (graph setup))
    (state : OperationalState setup runtime leaks) : OperationalState setup runtime leaks :=
  { state with
    environment := { state.environment with application
      := view }
    keys := fun observer => (state.keys observer).map
      fun key =>
      { key with current := (view, key.current.2) } }

/-- **A contract step that keeps the configuration, on the operational
state.** -/
theorem operationalState_contract (remaining : Nat)
    (execution : (application setup runtime leaks).Execution) (next : EventGraphRuntime.State
      (graph setup))
    (config : next.config = execution.application.config)
    (command : EnvironmentCommand (graph setup)) :
    operationalState setup runtime leaks (some ⟨remaining, none,
      { execution with
        application := next
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment (application setup runtime leaks), .application command⟩]
            }⟩) =
      (operationalState setup runtime leaks (some ⟨remaining + 1, none, execution⟩)).map fun state
        =>
        (state.round remaining none (.application command)).contract (runtime
          := runtime) next.publicView := by
  simp only [operationalState, Option.map_some, OperationalState.round,
    OperationalState.contract, Option.some.injEq, OperationalState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try trivial
  funext observer
  simp only [Option.map_some, lateKey, Option.some.injEq]
  have turn := publicView_ownTurn?_congr (first := next.publicView)
    (second := execution.application.publicView)
    (by change (graph setup).publicObserve next.config = _; rw [config]; rfl) observer
  congr 1
  exact deliveredValue_congr (runtime := runtime) observer turn (by
    change ((graph setup).playerObserve observer next.config).store = _
    rw [config]
    rfl)

section Congruence

variable {first second : (application setup runtime leaks).Control}
  (same : operationalState setup runtime leaks (some first) = operationalState setup runtime leaks
    (some second))
include same

theorem SameOperational.remaining : first.remaining = second.remaining :=
  congrArg OperationalState.remaining (Option.some.inj same)

theorem SameOperational.actor : first.actor = second.actor :=
  congrArg OperationalState.actor (Option.some.inj same)

theorem SameOperational.environmentRecall :
    first.execution.environmentRecall = second.execution.environmentRecall :=
  congrArg OperationalState.environmentRecall (Option.some.inj same)

theorem SameOperational.observeEnvironment :
    first.execution.observeEnvironment (application setup runtime leaks) =
      second.execution.observeEnvironment (application setup runtime leaks) :=
  congrArg OperationalState.environment (Option.some.inj same)

theorem SameOperational.network : first.execution.network = second.execution.network :=
  congrArg (OperationalState.network setup runtime leaks) (Option.some.inj same)

theorem SameOperational.publicView :
    first.execution.application.publicView = second.execution.application.publicView :=
  congrArg ReactiveApplication.EnvironmentView.application (SameOperational.observeEnvironment
    (runtime := runtime) same)

theorem SameOperational.receipts : first.execution.receipts = second.execution.receipts :=
  congrArg ReactiveApplication.EnvironmentView.receipts (SameOperational.observeEnvironment
    (runtime := runtime) same)

theorem SameOperational.completed (event : (graph setup).EventId) :
    event ∈ first.execution.application.config.cut.completed ↔
      event ∈ second.execution.application.config.cut.completed := by
  have order := congrArg (fun view : PublicView (graph setup) => view.observation.completionOrder)
    (SameOperational.publicView same)
  change first.execution.application.config.history.map EventGraph.Completion.event =
    second.execution.application.config.history.map EventGraph.Completion.event at order
  rw [← first.execution.application.config.history_exact,
    ← second.execution.application.config.history_exact, order]

end Congruence

section Image

variable (event : (graph setup).EventId)

open Classical in
/-- **The image of a protocol state.** While `event` is pending, the
operational state; once it has completed, whether its output failed. -/
def pendingImage : (application setup runtime leaks).ProtocolState →
    Option (OperationalState setup runtime leaks) ⊕ Bool
  | none => .inl none
  | some control =>
      if event ∈ control.execution.application.config.cut.completed then
        .inr (decide (StoreEventFailed control.execution.application.config.store event))
      else .inl (operationalState setup runtime leaks (some control))

variable {event}

open Classical in
theorem pendingImage_of_pending (control : (application setup runtime leaks).Control)
    (pending : event ∉ control.execution.application.config.cut.completed) :
    pendingImage (runtime := runtime) event (some control) = .inl (operationalState setup runtime
      leaks (some control)) := by
  simp only [pendingImage, pending, ↓reduceIte]

/-- An activation round from a pending state, read through the image. -/
theorem environmentStep_activate_image (remaining : Nat)
    (execution : (application setup runtime leaks).Execution)
    (pending : event ∉ execution.application.config.cut.completed) (who : Player) :
    (execution.environmentStep (application setup runtime leaks) (.activate who)).map
        (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, some who, next⟩)) =
      (leaks who execution.network.pending).map fun selected =>
        .inl ((operationalState setup runtime leaks (some ⟨remaining + 1, none, execution⟩)).map
          fun state => (state.learn who selected).round
            remaining (some who) (.activate who)) := by
  unfold ReactiveApplication.Execution.environmentStep
  simp only [PMF.map_comp]
  congr 1
  funext selected
  simp only [Function.comp]
  rw [pendingImage_of_pending (runtime := runtime) _ pending, ← operationalState_activate]

/-- A waiting round from a pending state, read through the image. -/
theorem environmentStep_wait_image (remaining : Nat)
    (execution : (application setup runtime leaks).Execution)
    (pending : event ∉ execution.application.config.cut.completed) :
    (execution.environmentStep (application setup runtime leaks) .wait).map
        (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) =
      PMF.pure (.inl ((operationalState setup runtime leaks (some ⟨remaining + 1, none,
        execution⟩)).map
        fun state => state.round remaining none .wait)) := by
  unfold ReactiveApplication.Execution.environmentStep
  simp only [PMF.pure_map]
  rw [pendingImage_of_pending (runtime := runtime) _ pending, ← operationalState_wait]

/-- A contract round that completes nothing, read through the image: the
operational state records the round and reads the new public contract view. -/
theorem environmentStep_contract_image (remaining : Nat)
    (execution : (application setup runtime leaks).Execution)
    (pending : event ∉ execution.application.config.cut.completed)
    (command : EnvironmentCommand (graph setup))
    (stays : ∀ next ∈ (EventGraphRuntime.environmentStep runtime execution.application
      command).support, next.config = execution.application.config) :
    (execution.environmentStep (application setup runtime leaks) (.application command)).map
        (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) =
      (EventGraphRuntime.environmentStep runtime execution.application command).map
        fun next => .inl ((operationalState setup runtime leaks (some ⟨remaining + 1, none,
          execution⟩)).map
          fun state => (state.round remaining none (.application
            command)).contract
            next.publicView) := by
  unfold ReactiveApplication.Execution.environmentStep
  simp only [PMF.map_comp]
  apply map_congr_on_support
  intro next member
  simp only [Function.comp]
  have config := stays next member
  rw [pendingImage_of_pending (runtime := runtime) _ (by
      change event ∉ next.config.cut.completed
      rw [config]
      exact pending),
    ← operationalState_contract remaining execution next config command]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- The withheld result of a publication event is a failure of its field. -/
theorem isFailure_cast_failure {kind : EventGraph.EventField Player L} {payload : L.Ty}
    (kindEq : kind = .publication payload) :
    kind.IsFailure (cast (congrArg EventGraph.EventField.Value kindEq.symm)
      (PublicationResult.failure : PublicationResult (L.Val payload))) := by
  subst kindEq
  rfl

open Classical in
/-- Expiring a due publication event fails it, read through the image. -/
theorem pendingImage_expire_resolve (remaining : Nat) (actor : Option Player)
    (execution : (application setup runtime leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    {payload : L.Ty} (outputEq : (graph setup).outputLayout event = .publication payload)
    (entries : List (application setup runtime leaks).EnvironmentEntry) :
    pendingImage (runtime := runtime) event (some ⟨remaining, actor, { execution with
      application := execution.application.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload)))
      environmentRecall := entries }⟩) = .inr true := by
  have completed : event ∈ (execution.application.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload)))).config.cut.completed :=
    (EventOrder.Cut.mem_complete _ event ready event).mpr (Or.inl rfl)
  have failed : StoreEventFailed (execution.application.complete event ready
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)
      (cast (congrArg EventGraph.EventField.Value outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload)))).config.store event :=
    ⟨_, by simp [EventGraphRuntime.State.complete, EventGraph.Config.complete,
      EventGraph.Config.store], isFailure_cast_failure outputEq⟩
  simp only [pendingImage, completed, ↓reduceIte, failed, decide_true]

/-- A contract round that leaves the contract state unchanged, read through the
image. -/
theorem environmentStep_stutter_image (remaining : Nat)
    (execution : (application setup runtime leaks).Execution)
    (pending : event ∉ execution.application.config.cut.completed)
    (command : EnvironmentCommand (graph setup))
    (stutter : EventGraphRuntime.environmentStep runtime execution.application command =
      PMF.pure execution.application) :
    (execution.environmentStep (application setup runtime leaks) (.application command)).map
        (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) =
      PMF.pure (.inl ((operationalState setup runtime leaks (some ⟨remaining + 1, none,
        execution⟩)).map
        fun state => (state.round remaining none (.application
          command)).contract
          execution.application.publicView)) := by
  rw [environmentStep_contract_image (runtime := runtime) remaining execution pending command (by
    rw [stutter]
    intro next member
    rw [(PMF.mem_support_pure_iff _ _).mp member]), stutter, PMF.pure_map]

/-- Readiness is read off equal operational states. -/
theorem SameOperational.ready {first second : (application setup runtime leaks).Control}
    (same : operationalState setup runtime leaks (some first) = operationalState setup runtime
      leaks (some second))
    (event : (graph setup).EventId) :
    first.execution.application.config.cut.Ready event ↔
      second.execution.application.config.cut.Ready event := by
  unfold EventOrder.Cut.Ready
  constructor
  · rintro ⟨open_, before⟩
    exact ⟨fun completed => open_ ((SameOperational.completed same event).mpr completed),
      fun predecessor member => (SameOperational.completed same predecessor).mp (before member)⟩
  · rintro ⟨open_, before⟩
    exact ⟨fun completed => open_ ((SameOperational.completed same event).mp completed),
      fun predecessor member => (SameOperational.completed same predecessor).mpr (before member)⟩

/-- Expiring a due publication event, read through the image, is the failure
image surely. -/
theorem environmentStep_expire_due_image (remaining : Nat)
    (execution : (application setup runtime leaks).Execution)
    (ready : execution.application.config.cut.Ready event) (entered : Nat)
    (activated : execution.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ execution.application.clock - entered)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq) :
    (execution.environmentStep (application setup runtime leaks) (.application (.expire event))).map
        (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) =
          PMF.pure (.inr true) := by
  unfold ReactiveApplication.Execution.environmentStep
  change (((EventGraphRuntime.environmentStep runtime execution.application
    (.expire event)).map _).map _).map _ = _
  rw [environmentStep_expire_resolve_eq runtime _ event ready entered activated due owner
    payload binding checks outputEq codeEq view]
  simp only [PMF.pure_map]
  rw [pendingImage_expire_resolve (runtime := runtime) remaining none execution ready outputEq]

/-- **Contract rounds read off the operational state.** While a publication
event is pending and ready, two executions with the same operational state
give every contract command the same law of images. -/
theorem application_image_congr (remaining : Nat)
    (first second : (application setup runtime leaks).Execution)
    (same : operationalState setup runtime leaks (some ⟨remaining + 1, none, first⟩) =
      operationalState setup runtime leaks (some ⟨remaining + 1, none, second⟩))
    (pending : event ∉ first.application.config.cut.completed)
    (ready : first.application.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (command : EnvironmentCommand (graph setup)) :
    (first.environmentStep (application setup runtime leaks) (.application command)).map
        (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) =
      (second.environmentStep (application setup runtime leaks) (.application command)).map
        (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) := by
  have pending' : event ∉ second.application.config.cut.completed := fun completed =>
    pending ((SameOperational.completed same event).mpr completed)
  have ready' : second.application.config.cut.Ready event :=
    (SameOperational.ready (runtime := runtime) same event).mp ready
  have views : first.application.publicView = second.application.publicView :=
    SameOperational.publicView same
  have readyIff : ∀ other, first.application.config.cut.Ready other ↔
      second.application.config.cut.Ready other := SameOperational.ready (runtime := runtime) same
  have stutterBoth : ∀ command,
      EventGraphRuntime.environmentStep runtime first.application command =
        PMF.pure first.application →
      EventGraphRuntime.environmentStep runtime second.application command =
        PMF.pure second.application →
      (first.environmentStep (application setup runtime leaks) (.application command)).map
          (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) =
        (second.environmentStep (application setup runtime leaks) (.application command)).map
          (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) := by
    intro command firstStutter secondStutter
    rw [environmentStep_stutter_image (runtime := runtime) remaining first pending command
      firstStutter,
      environmentStep_stutter_image (runtime := runtime) remaining second pending' command
        secondStutter, same, views]
  cases command with
  | advanceClock =>
      rw [environmentStep_contract_image (runtime := runtime) remaining first pending _ (by
          intro next member
          simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at member
          rw [member]),
        environmentStep_contract_image (runtime := runtime) remaining second pending' _ (by
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
          (environmentStep_executeSample_of_nonsample runtime _ sampled ready
            (fun _ _ _ _ other => by rw [view] at other; cases other))
          (environmentStep_executeSample_of_nonsample runtime _ sampled ready'
            (fun _ _ _ _ other => by rw [view] at other; cases other))
      · exact stutterBoth _
          (environmentStep_executeSample_of_not_ready runtime _ sampled sampledReady)
          (environmentStep_executeSample_of_not_ready runtime _ sampled
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
              (environmentStep_expire_of_not_activated runtime _ expired ready activated)
              (environmentStep_expire_of_not_activated runtime _ expired ready'
                (by rw [← activations]; exact activated))
        | some entered =>
            by_cases due : runtime.deadline expired ≤ first.application.clock - entered
            · rw [environmentStep_expire_due_image (runtime := runtime) remaining first ready
                entered activated due view,
                environmentStep_expire_due_image (runtime := runtime) remaining second ready'
                  entered
                  (by rw [← activations]; exact activated) (by rw [← clocks]; exact due) view]
            · exact stutterBoth _
                (environmentStep_expire_of_not_due runtime _ expired ready entered
                  activated due)
                (environmentStep_expire_of_not_due runtime _ expired ready' entered
                  (by rw [← activations]; exact activated) (by rw [← clocks]; exact due))
      · exact stutterBoth _
          (environmentStep_expire_of_not_ready runtime _ expired expiredReady)
          (environmentStep_expire_of_not_ready runtime _ expired
            (fun other => expiredReady ((readyIff expired).mpr other)))

/-- Late-delivery keys of views that differ only in their network part and
receipts agree when the earlier keys agree and the network parts and receipts
agree. -/
theorem lateKey_network_congr (who : Player) (firstPast secondPast :
      List (application setup runtime leaks).PlayerEntry)
    {first first' second second' : (application setup runtime leaks).PlayerView}
    (old : lateKey setup runtime leaks who (some (firstPast, first)) =
      lateKey setup runtime leaks who (some (secondPast, second)))
    (firstContract : first'.application = first.application)
    (secondContract : second'.application = second.application)
    (messages : first'.messages = second'.messages)
    (receipts : first'.receipts = second'.receipts) :
    lateKey setup runtime leaks who (some (firstPast, first')) =
      lateKey setup runtime leaks who (some (secondPast, second')) := by
  simp only [lateKey, Option.some.injEq, LateKey.mk.injEq, operationalView] at old ⊢
  obtain ⟨_, current, recalled, delivered⟩ := old
  refine ⟨trivial, ?_, recalled, ?_⟩
  · rw [firstContract, secondContract, messages, receipts]
    rw [(Prod.mk.inj current).1]
  · have firstDelivered : deliveredValue setup runtime leaks who first' =
        deliveredValue setup runtime leaks who first := by
      unfold deliveredValue
      rw [firstContract]
    have secondDelivered : deliveredValue setup runtime leaks who second' =
        deliveredValue setup runtime leaks who second := by
      unfold deliveredValue
      rw [secondContract]
    rw [firstDelivered, secondDelivered, delivered]

/-- **An inclusion the contract rejects, read off the operational state.**
While an event is pending, two executions with the same operational state give
an inclusion the same image when the contract rejects the included packet in
both, or there is none to include. -/
theorem include_image_congr (remaining : Nat)
    (first second : (application setup runtime leaks).Execution)
    (same : operationalState setup runtime leaks (some ⟨remaining + 1, none, first⟩) =
      operationalState setup runtime leaks (some ⟨remaining + 1, none, second⟩))
    (pending : event ∉ first.application.config.cut.completed) (id : MessageId Player)
    (rejected : ∀ message, first.network.lookup id = some message →
      (application setup runtime leaks).handle first.application message = none ∧
        (application setup runtime leaks).handle second.application message = none) :
    (first.environmentStep (application setup runtime leaks) (.include id)).map
        (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) =
      (second.environmentStep (application setup runtime leaks) (.include id)).map
        (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) := by
  have networks : first.network = second.network := SameOperational.network same
  have pending' : event ∉ second.application.config.cut.completed := fun completed =>
    pending ((SameOperational.completed same event).mpr completed)
  have fields := Option.some.inj same
  simp only [OperationalState.mk.injEq] at fields
  obtain ⟨_, _, recalls, views, _, keys⟩ := fields
  unfold ReactiveApplication.Execution.environmentStep
  simp only [PMF.pure_map]
  congr 1
  unfold ReactiveApplication.Execution.includePending
  cases found : first.network.lookup id with
  | none =>
      have found' : second.network.lookup id = none := by rw [← networks]; exact found
      simp only [MessageNetwork.includePending, found, found']
      rw [pendingImage_of_pending (runtime := runtime) _ pending, pendingImage_of_pending (runtime
        := runtime) _ pending']
      simp only [operationalState, Sum.inl.injEq, Option.some.injEq, OperationalState.mk.injEq]
      refine ⟨trivial, trivial, ?_, ?_, ?_, ?_⟩
      · rw [recalls, views]
      · exact views
      · rw [networks]
      · funext who
        exact congrFun keys who
  | some message =>
      obtain ⟨firstRejected, secondRejected⟩ := rejected message found
      have found' : second.network.lookup id = some message := by rw [← networks]; exact found
      simp only [MessageNetwork.includePending, found, found', firstRejected, secondRejected,
        Option.getD_none, Option.isSome_none]
      rw [pendingImage_of_pending (runtime := runtime) _ pending, pendingImage_of_pending (runtime
        := runtime) _ pending']
      simp only [operationalState, Sum.inl.injEq, Option.some.injEq, OperationalState.mk.injEq]
      have receipts : first.receipts = second.receipts :=
        congrArg ReactiveApplication.EnvironmentView.receipts views
      refine ⟨trivial, trivial, ?_, ?_, ?_, ?_⟩
      · rw [recalls, views]
      · unfold ReactiveApplication.Execution.observeEnvironment
        rw [networks, receipts]
        congr 1
        exact congrArg ReactiveApplication.EnvironmentView.application views
      · rw [networks]
      · funext who
        exact lateKey_network_congr (runtime := runtime) who _ _ (congrFun keys who) rfl rfl
          (by change MessageNetwork.observe _ who = MessageNetwork.observe _ who; rw [networks])
          (by change first.receipts ++ _ = second.receipts ++ _; rw [receipts])

/-- While only a publication event is ready, the contract rejects every
commitment. -/
theorem handle_commitment_of_publication_ready (state : EventGraphRuntime.State (graph setup))
    (ready : state.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (message : Message Player (application setup runtime leaks).Payload) {committed : (graph
      setup).EventId}
    {candidate : Handle (graph setup)}
    (call : message.payload.call = .commitment committed candidate) :
    (application setup runtime leaks).handle state message = none := by
  apply reactiveHandle_none
  rw [call]
  by_cases committedReady : state.config.cut.Ready committed
  · have same : committed = event := ready_unique (setup := setup) _ committedReady ready
    subst same
    simp only [handle, dite_eq_left committedReady, view]
    split <;> rfl
  · simp only [handle, dite_eq_right committedReady]

variable (initial : PMF (application setup runtime leaks).State) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler) in
/-- **Scheduler rounds read off the operational state.** While a publication
event is pending and is the only ready event, two executions with the same
operational state give a scheduler round the same law of images, provided the
inclusions of packets other than commitments do. -/
theorem round_image_congr (remaining : Nat)
    (first second : (application setup runtime leaks).Execution)
    (same : operationalState setup runtime leaks (some ⟨remaining + 1, none, first⟩) =
      operationalState setup runtime leaks (some ⟨remaining + 1, none, second⟩))
    (pending : event ∉ first.application.config.cut.completed)
    (ready : first.application.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (inclusion : ∀ id message, first.network.lookup id = some message →
      (∃ committed candidate, message.payload.call = .commitment committed candidate) ∨
        (first.environmentStep (application setup runtime leaks) (.include id)).map
            (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) =
          (second.environmentStep (application setup runtime leaks) (.include id)).map
            (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩))) :
    ((application setup runtime leaks).transition initial horizon scheduler
        (some ⟨remaining + 1, none, first⟩) (fun _ => none)).map (pendingImage (runtime :=
          runtime) event) =
      ((application setup runtime leaks).transition initial horizon scheduler
        (some ⟨remaining + 1, none, second⟩) (fun _ => none)).map (pendingImage (runtime :=
          runtime) event) := by
  have pending' : event ∉ second.application.config.cut.completed := fun completed =>
    pending ((SameOperational.completed same event).mpr completed)
  have ready' : second.application.config.cut.Ready event :=
    (SameOperational.ready (runtime := runtime) same event).mp ready
  have networks : first.network = second.network := SameOperational.network same
  have recalls : first.environmentRecall = second.environmentRecall :=
    SameOperational.environmentRecall same
  have views : first.observeEnvironment (application setup runtime leaks) =
      second.observeEnvironment (application setup runtime leaks) :=
        SameOperational.observeEnvironment (runtime := runtime) same
  change ((scheduler first.environmentRecall (first.observeEnvironment _)).bind fun command =>
      (first.environmentStep _ command).map fun next =>
        some (⟨remaining, command.actor? (application setup runtime leaks), next⟩ :
          (application setup runtime leaks).Control)).map (pendingImage (runtime := runtime)
            event) =
    ((scheduler second.environmentRecall (second.observeEnvironment _)).bind fun command =>
      (second.environmentStep _ command).map fun next =>
        some (⟨remaining, command.actor? (application setup runtime leaks), next⟩ :
          (application setup runtime leaks).Control)).map (pendingImage (runtime := runtime) event)
  rw [recalls, views, PMF.map_bind, PMF.map_bind]
  congr 1
  funext command
  rw [PMF.map_comp, PMF.map_comp]
  cases command with
  | activate who =>
      change (first.environmentStep _ (.activate who)).map
          (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, some who, next⟩)) =
        (second.environmentStep _ (.activate who)).map
          (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, some who, next⟩))
      rw [environmentStep_activate_image (runtime := runtime) remaining first pending who,
        environmentStep_activate_image (runtime := runtime) remaining second pending' who,
          networks, same]
  | wait =>
      change (first.environmentStep _ .wait).map
          (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) =
        (second.environmentStep _ .wait).map
          (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩))
      rw [environmentStep_wait_image (runtime := runtime) remaining first pending,
        environmentStep_wait_image (runtime := runtime) remaining second pending', same]
  | «include» id =>
      change (first.environmentStep _ (.include id)).map
          (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) =
        (second.environmentStep _ (.include id)).map
          (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩))
      cases found : first.network.lookup id with
      | none =>
          exact include_image_congr (runtime := runtime) remaining first second same pending id
            (fun message member => by rw [found] at member; cases member)
      | some message =>
          rcases inclusion id message found with ⟨committed, candidate, call⟩ | equal
          · exact include_image_congr (runtime := runtime) remaining first second same pending id
              (fun other member => by
                rw [found] at member
                cases member
                exact ⟨handle_commitment_of_publication_ready (runtime := runtime) _ ready view _
                  call,
                  handle_commitment_of_publication_ready (runtime := runtime) _ ready' view _ call⟩)
          · exact equal
  | application command =>
      exact application_image_congr (runtime := runtime) remaining first second same pending ready
        view command

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem raw_eq_of_as {raw : Raw L} {payload : L.Ty} {value : L.Val payload}
    (typed : raw.as? payload = some value) : raw = ⟨payload, value⟩ := by
  rcases raw with ⟨kind, input⟩
  unfold Raw.as? at typed
  split at typed
  · rename_i same
    change kind = payload at same
    subst kind
    cases Option.some.inj typed
    rfl
  · cases typed

/-- An accepted opening of a ready publication event was timely, was sent by
the event's owner for one of its own handles associated with the event's
binding, and carried the bound successful value. -/
theorem handle_opening_accepted_facts (state next : EventGraphRuntime.State (graph setup))
    (ready : state.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (id : MessageId Player) (candidate : Handle (graph setup)) (raw : Raw L)
    (accepted : EventGraphRuntime.handle runtime state
      ⟨id, .opening event candidate raw⟩ = some next) :
    state.WithinDeadline runtime event ∧ id.1 = owner ∧ candidate.1 = owner ∧
      state.accepted binding.field = some candidate ∧
      ∃ value, raw = ⟨payload, value⟩ ∧
        binding.get? state.config.store = some (.success value) := by
  by_cases timely : state.WithinDeadline runtime event
  · simp only [EventGraphRuntime.handle, dite_eq_left ready, dite_eq_left timely, view]
      at accepted
    split at accepted
    · rename_i sender
      split at accepted
      · rename_i owned
        split at accepted
        · rename_i associated
          split at accepted
          · split at accepted
            · cases accepted
            · rename_i value typed
              split at accepted
              · rename_i stored
                exact ⟨timely, sender, owned, associated, value, raw_eq_of_as typed, stored⟩
              · cases accepted
          · cases accepted
        · cases accepted
      · cases accepted
    · cases accepted
  · simp [EventGraphRuntime.handle, ready, timely] at accepted

/-- Completing an event stores its output. -/
theorem complete_store_output (state : EventGraphRuntime.State (graph setup))
    (ready : state.config.cut.Ready event) (action : (graph setup).Action event)
    (value : ((graph setup).outputLayout event).Value) :
    (state.complete event ready action value).config.store (.inr event) = some value := by
  simp [EventGraphRuntime.State.complete, EventGraph.Config.complete, EventGraph.Config.store]

/-- **An accepted opening transfers across equal public data.** Two contract
states with the same public view and the same binding of a ready publication
event, both satisfying the binding invariant, accept the same opening of that
event together; both acceptances complete the event, failed in one exactly
when failed in the other. -/
theorem handle_opening_accepted_transfer (first second : EventGraphRuntime.State (graph setup))
    (publics : first.publicView = second.publicView)
    (firstValid : first.BindingInvariant) (secondValid : second.BindingInvariant)
    (ready : first.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (bindings : binding.get? first.config.store = binding.get? second.config.store)
    (id : MessageId Player) (candidate : Handle (graph setup)) (raw : Raw L)
    {next : EventGraphRuntime.State (graph setup)}
    (accepted : EventGraphRuntime.handle runtime first
      ⟨id, .opening event candidate raw⟩ = some next) :
    ∃ next', EventGraphRuntime.handle runtime second
        ⟨id, .opening event candidate raw⟩ = some next' ∧
      event ∈ next.config.cut.completed ∧ event ∈ next'.config.cut.completed ∧
      (StoreEventFailed next.config.store event ↔ StoreEventFailed next'.config.store event) := by
  obtain ⟨timely, sender, owned, associated, value, rawEq, stored⟩ :=
    handle_opening_accepted_facts (runtime := runtime) first next ready view id candidate raw
      accepted
  subst rawEq
  have secondStored : binding.get? second.config.store = some (.success value) :=
    bindings ▸ stored
  obtain ⟨provenance, provenanceAccepted, _, fixed⟩ :=
    firstValid.success_provenance binding value stored
  rw [Option.some.inj (provenanceAccepted.symm.trans associated)] at fixed
  have available : (EventGraph.EventCode.resolveOutput? binding checks true
      first.config.store).isSome = true := by
    apply EventGraph.EventCode.resolveOutput?_isSome
    intro field member
    apply first.config.read_available ready
    rw [← EventGraph.EventCode.readFields_cast outputEq ((graph setup).nodes event), codeEq]
    exact member
  obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp available
  obtain ⟨ready', secondTimely, secondAssociated, secondResolved⟩ :=
    EventGraphRuntime.opening_right_facts runtime first second publics event owner payload
      binding checks candidate ready timely associated value stored secondStored result resolved
  obtain ⟨secondProvenance, secondProvenanceAccepted, _, secondFixed⟩ :=
    secondValid.success_provenance binding value secondStored
  rw [Option.some.inj (secondProvenanceAccepted.symm.trans secondAssociated)] at secondFixed
  rw [EventGraphRuntime.handle_opening_eq runtime first id event candidate owner payload
    binding checks outputEq codeEq view ready timely sender owned associated value fixed stored
    result resolved] at accepted
  cases accepted
  refine ⟨_, EventGraphRuntime.handle_opening_eq runtime second id event candidate owner
    payload binding checks outputEq codeEq view ready' secondTimely sender owned secondAssociated
    value secondFixed secondStored result secondResolved,
    (EventOrder.Cut.mem_complete _ event ready event).mpr (Or.inl rfl),
    (EventOrder.Cut.mem_complete _ event ready' event).mpr (Or.inl rfl), ?_⟩
  simp only [StoreEventFailed, complete_store_output]

open Classical in
/-- **An opening of the pending event, read off the operational state.** While
a publication event is pending and ready, two executions with the same
operational state, both satisfying the binding invariant and holding the same
binding of the event, give the inclusion of an opening of the event the same
image. -/
theorem include_opening_image_congr (remaining : Nat)
    (first second : (application setup runtime leaks).Execution)
    (same : operationalState setup runtime leaks (some ⟨remaining + 1, none, first⟩) =
      operationalState setup runtime leaks (some ⟨remaining + 1, none, second⟩))
    (pending : event ∉ first.application.config.cut.completed)
    (ready : first.application.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (firstValid : first.application.BindingInvariant)
    (secondValid : second.application.BindingInvariant)
    (bindings : binding.get? first.application.config.store =
      binding.get? second.application.config.store)
    (id : MessageId Player) {message : Message Player (application setup runtime leaks).Payload}
    (found : first.network.lookup id = some message)
    {candidate : Handle (graph setup)} {raw : Raw L}
    (call : message.payload.call = .opening event candidate raw) :
    (first.environmentStep (application setup runtime leaks) (.include id)).map
        (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) =
      (second.environmentStep (application setup runtime leaks) (.include id)).map
        (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) := by
  have publics : first.application.publicView = second.application.publicView :=
    SameOperational.publicView same
  have ready' : second.application.config.cut.Ready event :=
    (SameOperational.ready (runtime := runtime) same event).mp ready
  have found' : second.network.lookup id = some message := by
    rw [← SameOperational.network same]
    exact found
  have bothRejected
      (firstRejected : EventGraphRuntime.handle runtime first.application
        ⟨message.id, message.payload.call⟩ = none ∨ message.payload.tokenValid = false)
      (secondRejected : EventGraphRuntime.handle runtime second.application
        ⟨message.id, message.payload.call⟩ = none ∨ message.payload.tokenValid = false) :
      (first.environmentStep (application setup runtime leaks) (.include id)).map
          (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) =
        (second.environmentStep (application setup runtime leaks) (.include id)).map
          (fun next => pendingImage (runtime := runtime) event (some ⟨remaining, none, next⟩)) := by
    apply include_image_congr (runtime := runtime) remaining first second same pending id
    intro other member
    rw [found] at member
    cases member
    constructor
    · rcases firstRejected with rejected | invalid
      · exact reactiveHandle_none rejected
      · exact reactiveApplication_handle_of_not_tokenValid runtime leaks _ _ invalid
    · rcases secondRejected with rejected | invalid
      · exact reactiveHandle_none rejected
      · exact reactiveApplication_handle_of_not_tokenValid runtime leaks _ _ invalid
  cases firstHandle : EventGraphRuntime.handle runtime first.application
      ⟨message.id, .opening event candidate raw⟩ with
  | none =>
      cases secondHandle : EventGraphRuntime.handle runtime second.application
          ⟨message.id, .opening event candidate raw⟩ with
      | none =>
          exact bothRejected (Or.inl (by rw [call]; exact firstHandle))
            (Or.inl (by rw [call]; exact secondHandle))
      | some _ =>
          obtain ⟨_, accepted, _⟩ := handle_opening_accepted_transfer (runtime := runtime)
            second.application
            first.application publics.symm secondValid firstValid ready' view bindings.symm
            message.id candidate raw secondHandle
          rw [firstHandle] at accepted
          cases accepted
  | some next =>
      obtain ⟨next', secondHandle, completed, completed', failed⟩ :=
        handle_opening_accepted_transfer (runtime := runtime) first.application second.application
          publics firstValid
          secondValid ready view bindings message.id candidate raw firstHandle
      cases valid : message.payload.tokenValid with
      | false => exact bothRejected (Or.inr valid) (Or.inr valid)
      | true =>
          have firstAccepted : (application setup runtime leaks).handle first.application message =
              some next :=
            (reactiveApplication_handle_of_tokenValid runtime leaks _ _ valid).trans
              (by rw [call]; exact firstHandle)
          have secondAccepted : (application setup runtime leaks).handle second.application
            message =
              some next' :=
            (reactiveApplication_handle_of_tokenValid runtime leaks _ _ valid).trans
              (by rw [call]; exact secondHandle)
          unfold ReactiveApplication.Execution.environmentStep
          simp only [PMF.pure_map]
          congr 1
          unfold ReactiveApplication.Execution.includePending
          simp only [MessageNetwork.includePending, found, found', firstAccepted, secondAccepted,
            Option.getD_some]
          simp only [pendingImage, completed, completed', ↓reduceIte, Sum.inr.injEq,
            decide_eq_decide]
          exact failed

/-- A player reads its own binding through its own view of the store. -/
private theorem get?_playerStore_own (store : EventGraph.Store (graph setup).layout)
    {owner : Player} {payload : L.Ty}
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)) :
    binding.get? ((graph setup).playerStore owner store) = binding.get? store := by
  rcases binding with ⟨field, layoutEq⟩
  apply EventGraph.FieldRef.get?_congr
  apply EventGraph.playerStore_of_visible
  change ((graph setup).layout field).VisibleTo owner
  rw [layoutEq]
  rfl

/-- At a ready publication event, the owner's delivered value is its binding
of the event. -/
theorem deliveredValue_of_ready (execution : (application setup runtime leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq) :
    deliveredValue setup runtime leaks owner (execution.observe (application setup runtime leaks)
      owner) =
      some (⟨.binding owner payload, binding.get? execution.application.config.store⟩ :
        Σ kind : EventGraph.EventField Player L, Option kind.Value) := by
  have turn : execution.application.publicView.ownTurn? owner = some event :=
    ownTurn?_of_ready setup _ ready (nodeView_resolve_actor outputEq codeEq)
  unfold deliveredValue
  change (match execution.application.publicView.ownTurn? owner with
    | none => none
    | some event => _) = _
  rw [turn]
  simp only [view]
  rw [← get?_playerStore_own execution.application.config.store]
  rfl

/-- **The owner's binding of the ready event is operational.** Two protocol
states with the same operational state hold the same binding of a ready
publication event: the owner's late-delivery key carries it. -/
theorem SameOperational.binding {first second : (application setup runtime leaks).Control}
    (same : operationalState setup runtime leaks (some first) = operationalState setup runtime
      leaks (some second))
    (ready : first.execution.application.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq) :
    binding.get? first.execution.application.config.store =
      binding.get? second.execution.application.config.store := by
  have ready' : second.execution.application.config.cut.Ready event :=
    (SameOperational.ready (runtime := runtime) same event).mp ready
  have keys := congrFun (congrArg OperationalState.keys (Option.some.inj
    same)) owner
  simp only [lateKey, Option.some.injEq] at keys
  have delivered := congrArg LateKey.delivered keys
  change deliveredValue setup runtime leaks owner
      (first.execution.observe (application setup runtime leaks) owner) =
    deliveredValue setup runtime leaks owner
      (second.execution.observe (application setup runtime leaks) owner) at delivered
  rw [deliveredValue_of_ready (runtime := runtime) first.execution ready view,
    deliveredValue_of_ready (runtime := runtime) second.execution ready' view] at delivered
  simp only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at delivered
  exact delivered

end Image

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

/-- **Other players respond silently while the event is pending.** At a history
of the one-packet game in a forced state of `owner`, while an event of `owner`
is ready, the control step of any profile at another player's activation is
that player's silent response, surely. -/
theorem controlStep_other_of_pending
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    (owner : Player)
    (history : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
    (forced : ForcedState setup runtime leaks owner history.state)
    {control : (application setup runtime leaks).Control} (current : history.state = some control)
    {event : (graph setup).EventId} (ready : control.execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner) {other : Player}
    (acting : control.actor = some other) (different : other ≠ owner) :
    (application setup runtime leaks).controlStep (initialLaw setup) horizon scheduler
        ((bounds.onePacketMenu runtime leaks).decodeProfile (initialLaw setup) horizon
          scheduler profile) (some control) =
      PMF.pure (some { control with
        actor := none
        execution := control.execution.respond (application setup runtime leaks) other ⟨none⟩ })
          := by
  have silent : ((bounds.onePacketMenu runtime leaks).decodeProfile (initialLaw setup)
      horizon scheduler profile other (control.execution.recall other)
      (control.execution.observe (application setup runtime leaks) other)) = PMF.pure ⟨none⟩ := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro action chosen
    have member := (bounds.onePacketMenu runtime leaks).decodeProfile_support
      (initialLaw setup) horizon scheduler profile other _ _ action chosen
    have quiet := onePacket_silent_of_pending (runtime := runtime) bounds horizon scheduler owner
      history forced
      current ready owned other different action member
    rcases action with ⟨transmission⟩
    change transmission = none at quiet
    subst quiet
    rfl
  unfold ReactiveApplication.controlStep
  rcases control with ⟨remaining, current', execution⟩
  change current' = some other at acting
  subst acting
  simp only [ReactiveApplication.actor, Option.bind_some]
  rw [silent, PMF.pure_bind,
    transition_respond (runtime := runtime) (horizon := horizon) (scheduler := scheduler)
      ⟨remaining, some other, execution⟩ rfl]
  simp only [↓reduceIte, Option.getD_some]

/-- **The control step stays on histories.** Every state the control step of a
decoded profile reaches from the state of a history of the one-packet game is
the state of a history of the one-packet game. -/
theorem controlStep_history
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    (history : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
    {next : (application setup runtime leaks).ProtocolState}
    (member : next ∈ ((application setup runtime leaks).controlStep (initialLaw setup) horizon
      scheduler
      ((bounds.onePacketMenu runtime leaks).decodeProfile (initialLaw setup) horizon
        scheduler profile) history.state).support) :
    ∃ extended : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History,
      extended.state = next := by
  let protocol := onePacketProtocol setup runtime leaks bounds horizon scheduler
  by_cases stopped : (application setup runtime leaks).terminal history.state
  · rcases history with ⟨state, trace⟩
    cases state with
    | none => exact stopped.elim
    | some control =>
        obtain ⟨remaining, idle⟩ := stopped
        rcases control with ⟨remaining', current, execution⟩
        change remaining' = 0 at remaining
        change current = none at idle
        subst remaining idle
        refine ⟨⟨_, trace⟩, ?_⟩
        have law : (application setup runtime leaks).controlStep (initialLaw setup) horizon
          scheduler
            ((bounds.onePacketMenu runtime leaks).decodeProfile (initialLaw setup) horizon
              scheduler profile) (some ⟨0, none, execution⟩) =
            PMF.pure (some ⟨0, none, execution⟩) := rfl
        change next ∈ ((application setup runtime leaks).controlStep (initialLaw setup) horizon
          scheduler
          _ (some ⟨0, none, execution⟩)).support at member
        rw [law, PMF.mem_support_pure_iff] at member
        exact member.symm
  · cases acting : (application setup runtime leaks).actor history.state with
    | none =>
        have legal : protocol.Legal history.state (fun _ => none) := by
          refine ⟨stopped, fun who => ?_⟩
          change ¬ (application setup runtime leaks).actor history.state = some who
          rw [acting]
          exact (Option.some_ne_none _).symm
        have reached : next ∈ (protocol.step history.state ⟨fun _ => none, legal⟩).support := by
          unfold ReactiveApplication.controlStep at member
          rw [acting] at member
          exact member
        exact ⟨history.extend legal reached, rfl⟩
    | some who =>
        rcases history with ⟨state, trace⟩
        cases state with
        | none => cases acting
        | some control =>
            unfold ReactiveApplication.controlStep at member
            rw [acting] at member
            simp only at member
            rw [PMF.mem_support_bind_iff] at member
            obtain ⟨action, chosen, reached⟩ := member
            have menu := (bounds.onePacketMenu runtime leaks).decodeProfile_support
              (initialLaw setup) horizon scheduler profile who _ _ action chosen
            have legal : protocol.Legal (some control)
                (fun observer => if observer = who then some action else none) := by
              refine ⟨stopped, fun observer => ?_⟩
              by_cases same : observer = who
              · subst same
                simp only [↓reduceIte]
                exact ⟨acting, menu⟩
              · simp only [same, ↓reduceIte]
                change ¬ (application setup runtime leaks).actor (some control) = some observer
                rw [acting]
                exact fun equal => same (Option.some.inj equal).symm
            exact ⟨(⟨some control, trace⟩ : protocol.History).extend legal reached, rfl⟩

/-- Every contract state of a one-packet history satisfies the binding
invariant. -/
theorem bindingInvariant_of_history
    (history : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
    {control : (application setup runtime leaks).Control} (current : history.state = some control) :
    control.execution.application.BindingInvariant := by
  have raw := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon
    scheduler history.trace
  have binding := (runtime.reactiveBindingInvariant leaks).history (initialLaw setup)
    horizon scheduler (fun state member => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
      exact State.initial_bindingInvariant _) raw
  rw [current] at binding
  exact binding

/-- **Scheduler rounds at forced histories read off the operational state.**
While a publication event is pending and ready at a forced one-packet history,
a scheduler round from any one-packet history with the same operational state
has the same law of images: every pending packet is a commitment, which the
contract rejects, or an opening of the ready event, whose inclusion reads only
public data and the owner's binding. -/
theorem round_image_congr_of_forced (who : Player) (remaining : Nat)
    (firstHistory secondHistory : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).History)
    {first second : (application setup runtime leaks).Execution}
    (firstCurrent : firstHistory.state = some ⟨remaining + 1, none, first⟩)
    (secondCurrent : secondHistory.state = some ⟨remaining + 1, none, second⟩)
    (forced : ForcedState setup runtime leaks who firstHistory.state)
    (same : operationalState setup runtime leaks (some ⟨remaining + 1, none, first⟩) =
      operationalState setup runtime leaks (some ⟨remaining + 1, none, second⟩))
    {event : (graph setup).EventId}
    (pending : event ∉ first.application.config.cut.completed)
    (ready : first.application.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq) :
    ((application setup runtime leaks).transition (initialLaw setup) horizon scheduler
        (some ⟨remaining + 1, none, first⟩) (fun _ => none)).map (pendingImage (runtime :=
          runtime) event) =
      ((application setup runtime leaks).transition (initialLaw setup) horizon scheduler
        (some ⟨remaining + 1, none, second⟩) (fun _ => none)).map (pendingImage (runtime :=
          runtime) event) := by
  have firstValid := bindingInvariant_of_history (runtime := runtime) bounds horizon scheduler
    firstHistory firstCurrent
  have secondValid :=
    bindingInvariant_of_history (runtime := runtime) bounds horizon scheduler secondHistory
      secondCurrent
  have bindings := SameOperational.binding (runtime := runtime) same ready view
  apply round_image_congr (runtime := runtime) (initialLaw setup) horizon scheduler remaining
    first second same pending
    ready view
  intro id message found
  have member : message ∈ first.network.pending := List.mem_of_find?_eq_some found
  rcases onePacket_pending_of_forced (runtime := runtime) bounds horizon scheduler who
    firstHistory forced firstCurrent
      message member with ⟨committed, candidate, call, _⟩ |
      ⟨opened, candidate, raw, call, _, openedReady, _⟩
  · exact Or.inl ⟨committed, candidate, call⟩
  · right
    rw [ready_unique (setup := setup) _ openedReady ready] at call
    exact include_opening_image_congr (runtime := runtime) remaining first second same pending
      ready view firstValid
      secondValid bindings id found call

omit [Fintype Player] in
/-- **The control step changes the configuration by one step.** -/
theorem controlStep_configStep (players : Player → (application setup runtime leaks).Policy)
    (control : (application setup runtime leaks).Control) {next : (application setup runtime
      leaks).ProtocolState}
    (member : next ∈ ((application setup runtime leaks).controlStep (initialLaw setup) horizon
      scheduler
      players (some control)).support) :
    ∃ control' : (application setup runtime leaks).Control, next = some control' ∧
      ConfigStep setup control.execution.application.config
        control'.execution.application.config := by
  rcases control with ⟨remaining, actor, execution⟩
  unfold ReactiveApplication.controlStep at member
  cases actor with
  | none =>
      cases remaining with
      | zero => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp member, Or.inl rfl⟩
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ member)
          obtain ⟨next', supported, rfl⟩ := PMF.support_map .. ▸ moved
          exact ⟨_, rfl, environmentStep_configStep setup leaks execution next' command
            supported⟩
  | some who =>
      simp only [ReactiveApplication.actor, Option.bind_some] at member
      rw [PMF.mem_support_bind_iff] at member
      obtain ⟨action, _, reached⟩ := member
      exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached,
        Or.inl (runtime.reactive_respond_application leaks execution who _).1⟩

omit [Fintype Player] in
/-- A forced state is forced at every state with the same configuration. -/
theorem forcedState_of_config_eq {who : Player}
    {control control' : (application setup runtime leaks).Control}
    (forced : ForcedState setup runtime leaks who (some control))
    (same : control'.execution.application.config = control.execution.application.config) :
    ForcedState setup runtime leaks who (some control') := by
  obtain ⟨rank, point, ordered, decoded, forcedPoint⟩ := forced
  refine ⟨rank, point, ?_, ?_, forcedPoint⟩
  · rw [same]
    exact ordered
  · rw [same]
    exact decoded

omit [Fintype Player] in
/-- One configuration step keeps a completed event completed. -/
theorem completed_of_configStep {config next : (graph setup).Config}
    (step : ConfigStep setup config next) {event : (graph setup).EventId}
    (completed : event ∈ config.cut.completed) : event ∈ next.cut.completed := by
  rcases step with same | ⟨other, ready, action, member⟩
  · rw [same]
    exact completed
  · rw [config.step_cut other ready action next member]
    exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inr completed)

omit [Fintype Player] in
/-- One configuration step keeps the output of a completed event. -/
theorem output_of_configStep {config next : (graph setup).Config}
    (step : ConfigStep setup config next) {event : (graph setup).EventId}
    (completed : event ∈ config.cut.completed) :
    next.store (.inr event) = config.store (.inr event) := by
  rcases step with same | ⟨other, ready, action, member⟩
  · rw [same]
  · have present : (config.store (.inr event)).isSome := by
      rw [EventGraph.Config.store_output]
      exact (config.output_available event).mpr completed
    obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp present
    rw [stored]
    exact config.step_store_of_some next other ready action member _ value stored

omit [Fintype Player] in
open Classical in
/-- Once an event has completed, one configuration step leaves its image
unchanged. -/
theorem pendingImage_of_configStep {control control' : (application setup runtime leaks).Control}
    (step : ConfigStep setup control.execution.application.config
      control'.execution.application.config)
    {event : (graph setup).EventId}
    (completed : event ∈ control.execution.application.config.cut.completed) :
    pendingImage (runtime := runtime) event (some control') = pendingImage (runtime := runtime)
      event (some control) := by
  have completed' := completed_of_configStep step completed
  have output := output_of_configStep step completed
  simp only [pendingImage, completed, completed', ↓reduceIte, StoreEventFailed, output,
    Sum.inr.injEq, decide_eq_decide]

omit [Fintype Player] in
/-- **While the event is ready at a forced state, one configuration step
either completes it or keeps the state forced with the event ready.** -/
theorem forced_or_completed_of_configStep {who : Player}
    {control control' : (application setup runtime leaks).Control}
    (step : ConfigStep setup control.execution.application.config
      control'.execution.application.config)
    (forced : ForcedState setup runtime leaks who (some control))
    {event : (graph setup).EventId} (ready : control.execution.application.config.cut.Ready event) :
    event ∈ control'.execution.application.config.cut.completed ∨
      (ForcedState setup runtime leaks who (some control') ∧
        control'.execution.application.config.cut.Ready event) := by
  rcases step with same | ⟨other, otherReady, action, member⟩
  · right
    refine ⟨forcedState_of_config_eq (runtime := runtime) forced same, ?_⟩
    rw [same]
    exact ready
  · left
    have sameEvent : other = event := ready_unique (setup := setup) _ otherReady ready
    subst sameEvent
    rw [control.execution.application.config.step_cut other otherReady action _ member]
    exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)

end Vegas
