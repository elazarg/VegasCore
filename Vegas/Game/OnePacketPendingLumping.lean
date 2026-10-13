/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketPathwise
import Vegas.Game.OnePacketActorRecord
import Vegas.Game.OnePacketEventFailure

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
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Append a responder's current operational view, with no emission, to its
recalled views, and clear the actor. -/
def OperationalState.silent (responder : Player) (state : OperationalState setup leaks) :
    OperationalState setup leaks :=
  { state with
    actor := none
    keys := fun who => if who = responder then (state.keys who).map fun key =>
      { key with recalled := key.recalled ++ [(key.current, none)] } else state.keys who }

/-- **A silent response on the operational state.** -/
theorem operationalState_silent (control : (application setup leaks).Control)
    (responder : Player) :
    operationalState setup leaks (some { control with
      actor := none
      execution := control.execution.respond (application setup leaks) responder ⟨none⟩ }) =
      (operationalState setup leaks (some control)).map
        (OperationalState.silent responder) := by
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
    rw [(application setup leaks).respond_recall_other control.execution responder who same]
    rfl

/-- A scheduler round on the operational state: the remaining rounds and actor
are set, and the round's command is recorded with the scheduler's view. -/
def OperationalState.round (remaining : Nat) (actor : Option Player)
    (command : (application setup leaks).Command) (state : OperationalState setup leaks) :
    OperationalState setup leaks :=
  { state with
    remaining := remaining
    actor := actor
    environmentRecall := state.environmentRecall ++ [⟨state.environment, command⟩] }

/-- An activation's observation on the operational state: the activated player
learns the selected pending packets, and every player's current operational
view reads the new network. -/
def OperationalState.learn (who : Player) (selected : Finset (MessageId Player))
    (state : OperationalState setup leaks) : OperationalState setup leaks :=
  { state with
    leaked := (state.network.learn who selected).leaked
    keys := fun observer => (state.keys observer).map fun key =>
      { key with current := (key.current.1, (state.network.learn who selected).observe observer,
        key.current.2.2) } }

/-- **An activation on the operational state.** -/
theorem operationalState_activate (remaining : Nat)
    (execution : (application setup leaks).Execution)
    (who : Player) (selected : Finset (MessageId Player)) :
    operationalState setup leaks (some ⟨remaining, some who,
      { execution with
        network := execution.network.learn who selected
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment (application setup leaks), .activate who⟩] }⟩) =
      (operationalState setup leaks (some ⟨remaining + 1, none, execution⟩)).map fun state =>
        (state.learn who selected).round remaining (some who) (.activate who) := by
  simp only [operationalState, Option.map_some, OperationalState.round, OperationalState.learn,
    Option.some.injEq, OperationalState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

/-- **Waiting on the operational state.** -/
theorem operationalState_wait (remaining : Nat)
    (execution : (application setup leaks).Execution) :
    operationalState setup leaks (some ⟨remaining, none,
      { execution with
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment (application setup leaks), .wait⟩] }⟩) =
      (operationalState setup leaks (some ⟨remaining + 1, none, execution⟩)).map fun state =>
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
theorem deliveredValue_congr (who : Player) {first second : (application setup leaks).PlayerView}
    (turn : first.application.publicView.ownTurn? who =
      second.application.publicView.ownTurn? who)
    (store : first.application.observation.store = second.application.observation.store) :
    deliveredValue setup leaks who first = deliveredValue setup leaks who second := by
  unfold deliveredValue
  rw [turn, store]

/-- A new public contract view on the operational state: the scheduler's view
and every player's current operational view read it. -/
def OperationalState.contract (view : PublicView (graph setup))
    (state : OperationalState setup leaks) : OperationalState setup leaks :=
  { state with
    environment := { state.environment with application := view }
    keys := fun observer => (state.keys observer).map fun key =>
      { key with current := (view, key.current.2) } }

/-- **A contract step that keeps the configuration, on the operational
state.** -/
theorem operationalState_contract (remaining : Nat)
    (execution : (application setup leaks).Execution) (next : EventGraphRuntime.State (graph setup))
    (config : next.config = execution.application.config)
    (command : EnvironmentCommand (graph setup)) :
    operationalState setup leaks (some ⟨remaining, none,
      { execution with
        application := next
        environmentRecall := execution.environmentRecall ++
          [⟨execution.observeEnvironment (application setup leaks), .application command⟩] }⟩) =
      (operationalState setup leaks (some ⟨remaining + 1, none, execution⟩)).map fun state =>
        (state.round remaining none (.application command)).contract next.publicView := by
  simp only [operationalState, Option.map_some, OperationalState.round,
    OperationalState.contract, Option.some.injEq, OperationalState.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try trivial
  funext observer
  simp only [Option.map_some, lateKey, Option.some.injEq]
  have turn := publicView_ownTurn?_congr (first := next.publicView)
    (second := execution.application.publicView)
    (by change (graph setup).publicObserve next.config = _; rw [config]; rfl) observer
  congr 1
  exact deliveredValue_congr observer turn (by
    change ((graph setup).playerObserve observer next.config).store = _
    rw [config]
    rfl)

section Congruence

variable {first second : (application setup leaks).Control}
  (same : operationalState setup leaks (some first) = operationalState setup leaks (some second))
include same

theorem SameOperational.remaining : first.remaining = second.remaining :=
  congrArg OperationalState.remaining (Option.some.inj same)

theorem SameOperational.actor : first.actor = second.actor :=
  congrArg OperationalState.actor (Option.some.inj same)

theorem SameOperational.environmentRecall :
    first.execution.environmentRecall = second.execution.environmentRecall :=
  congrArg OperationalState.environmentRecall (Option.some.inj same)

theorem SameOperational.observeEnvironment :
    first.execution.observeEnvironment (application setup leaks) =
      second.execution.observeEnvironment (application setup leaks) :=
  congrArg OperationalState.environment (Option.some.inj same)

theorem SameOperational.network : first.execution.network = second.execution.network :=
  congrArg (OperationalState.network setup leaks) (Option.some.inj same)

theorem SameOperational.publicView :
    first.execution.application.publicView = second.execution.application.publicView :=
  congrArg ReactiveApplication.EnvironmentView.application (SameOperational.observeEnvironment same)

theorem SameOperational.receipts : first.execution.receipts = second.execution.receipts :=
  congrArg ReactiveApplication.EnvironmentView.receipts (SameOperational.observeEnvironment same)

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
def pendingImage : (application setup leaks).ProtocolState →
    Option (OperationalState setup leaks) ⊕ Bool
  | none => .inl none
  | some control =>
      if event ∈ control.execution.application.config.cut.completed then
        .inr (decide (StoreEventFailed control.execution.application.config.store event))
      else .inl (operationalState setup leaks (some control))

variable {event}

open Classical in
theorem pendingImage_of_pending (control : (application setup leaks).Control)
    (pending : event ∉ control.execution.application.config.cut.completed) :
    pendingImage event (some control) = .inl (operationalState setup leaks (some control)) := by
  simp only [pendingImage, pending, ↓reduceIte]

/-- An activation round from a pending state, read through the image. -/
theorem environmentStep_activate_image (remaining : Nat)
    (execution : (application setup leaks).Execution)
    (pending : event ∉ execution.application.config.cut.completed) (who : Player) :
    (execution.environmentStep (application setup leaks) (.activate who)).map
        (fun next => pendingImage event (some ⟨remaining, some who, next⟩)) =
      (leaks who execution.network.pending).map fun selected =>
        .inl ((operationalState setup leaks (some ⟨remaining + 1, none, execution⟩)).map
          fun state => (state.learn who selected).round remaining (some who) (.activate who)) := by
  unfold ReactiveApplication.Execution.environmentStep
  simp only [PMF.map_comp]
  congr 1
  funext selected
  simp only [Function.comp]
  rw [pendingImage_of_pending _ pending, ← operationalState_activate]

/-- A waiting round from a pending state, read through the image. -/
theorem environmentStep_wait_image (remaining : Nat)
    (execution : (application setup leaks).Execution)
    (pending : event ∉ execution.application.config.cut.completed) :
    (execution.environmentStep (application setup leaks) .wait).map
        (fun next => pendingImage event (some ⟨remaining, none, next⟩)) =
      PMF.pure (.inl ((operationalState setup leaks (some ⟨remaining + 1, none, execution⟩)).map
        fun state => state.round remaining none .wait)) := by
  unfold ReactiveApplication.Execution.environmentStep
  simp only [PMF.pure_map]
  rw [pendingImage_of_pending _ pending, ← operationalState_wait]

end Image

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- **Other players respond silently while the event is pending.** At a history
of the one-packet game in a forced state of `owner`, while an event of `owner`
is ready, the control step of any profile at another player's activation is
that player's silent response, surely. -/
theorem controlStep_other_of_pending
    (profile : ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    (owner : Player)
    (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    (forced : ForcedState setup leaks owner history.state)
    {control : (application setup leaks).Control} (current : history.state = some control)
    {event : (graph setup).EventId} (ready : control.execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner) {other : Player}
    (acting : control.actor = some other) (different : other ≠ owner) :
    (application setup leaks).controlStep (initialLaw setup) horizon scheduler
        ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon
          scheduler profile) (some control) =
      PMF.pure (some { control with
        actor := none
        execution := control.execution.respond (application setup leaks) other ⟨none⟩ }) := by
  have silent : ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup)
      horizon scheduler profile other (control.execution.recall other)
      (control.execution.observe (application setup leaks) other)) = PMF.pure ⟨none⟩ := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro action chosen
    have member := (bounds.onePacketMenu (runtime setup) leaks).decodeProfile_support
      (initialLaw setup) horizon scheduler profile other _ _ action chosen
    have quiet := onePacket_silent_of_pending bounds horizon scheduler owner history forced
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
    transition_respond (horizon := horizon) (scheduler := scheduler)
      ⟨remaining, some other, execution⟩ rfl]
  simp only [↓reduceIte, Option.getD_some]

/-- **The control step stays on histories.** Every state the control step of a
decoded profile reaches from the state of a history of the one-packet game is
the state of a history of the one-packet game. -/
theorem controlStep_history
    (profile : ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    {next : (application setup leaks).ProtocolState}
    (member : next ∈ ((application setup leaks).controlStep (initialLaw setup) horizon scheduler
      ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon
        scheduler profile) history.state).support) :
    ∃ extended : (onePacketProtocol setup leaks bounds horizon scheduler).History,
      extended.state = next := by
  let protocol := onePacketProtocol setup leaks bounds horizon scheduler
  by_cases stopped : (application setup leaks).terminal history.state
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
        have law : (application setup leaks).controlStep (initialLaw setup) horizon scheduler
            ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon
              scheduler profile) (some ⟨0, none, execution⟩) =
            PMF.pure (some ⟨0, none, execution⟩) := rfl
        change next ∈ ((application setup leaks).controlStep (initialLaw setup) horizon scheduler
          _ (some ⟨0, none, execution⟩)).support at member
        rw [law, PMF.mem_support_pure_iff] at member
        exact member.symm
  · cases acting : (application setup leaks).actor history.state with
    | none =>
        have legal : protocol.Legal history.state (fun _ => none) := by
          refine ⟨stopped, fun who => ?_⟩
          change ¬ (application setup leaks).actor history.state = some who
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
            have menu := (bounds.onePacketMenu (runtime setup) leaks).decodeProfile_support
              (initialLaw setup) horizon scheduler profile who _ _ action chosen
            have legal : protocol.Legal (some control)
                (fun observer => if observer = who then some action else none) := by
              refine ⟨stopped, fun observer => ?_⟩
              by_cases same : observer = who
              · subst same
                simp only [↓reduceIte]
                exact ⟨acting, menu⟩
              · simp only [same, ↓reduceIte]
                change ¬ (application setup leaks).actor (some control) = some observer
                rw [acting]
                exact fun equal => same (Option.some.inj equal).symm
            exact ⟨(⟨some control, trace⟩ : protocol.History).extend legal reached, rfl⟩

end Vegas
