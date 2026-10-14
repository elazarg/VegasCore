/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCountedSurvivor
import Vegas.Pending.ReactiveCountedBindingService
import Vegas.Pending.ReactiveCountedOpeningAcceptance
import Vegas.Pending.ReactiveLocalSeedService

/-! # Concrete local seed service on genuine clean histories -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => runtime.reactiveApplication leaks

/-- The service reads only the selected event's own emitted prefix and elapsed time. -/
def countedSeedService (event : graph.EventId) (input : LocalSeedInput graph) :
    Option (app).Command :=
  if input.elapsed < runtime.deadline event then
    input.emitted.head?.map fun message => .include message.id
  else some (.application (.expire event))

omit [Fintype Player] in
private theorem authentic_pending_lookup
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (message : Message Player (WitnessedPacket graph))
    (pending : message ∈ control.execution.network.pending) :
    control.execution.network.lookup message.id = some message := by
  have unique := (app).uniqueIds_history scheduler initial horizon control trace
  cases found : control.execution.network.lookup message.id with
  | none =>
      exact (List.find?_eq_none.mp found message pending (by simp)).elim
  | some selected =>
      have member := List.mem_of_find?_eq_some found
      have identified : selected.id = message.id := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      exact congrArg some ((unique.pending message pending).pending selected member identified)

/-- Selecting an authentic packet from the event's local emitted prefix really
resolves that event on a genuine clean history; expiry resolves it at its deadline. -/
theorem countedSeedService_resolves (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (owner : Player) (event : graph.EventId) (owned : graph.actor? event = some owner)
    (unmissed : control.execution.application.publicView.missedBindingBy owner = false)
    (input : LocalSeedInput graph)
    (inputEq : runtime.environmentSeedInput leaks owner event
      (control.execution.observeEnvironment app) = input)
    (ready : control.execution.application.publicView.EventReady event)
    (command : (app).Command)
    (selected : runtime.countedSeedService leaks event input = some command) :
    runtime.ResolvingSeedCommand leaks event control.execution command := by
  have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (inputs.map State.initial)
    horizon scheduler trace
  have clean := (bounds.onePacketMenu_countClean runtime leaks scheduler).history
    (inputs.map State.initial) horizon (fun state _ => runtime.countClean_initial leaks state) trace
  obtain ⟨setup, _, invariant⟩ := runtime.reactive_history_invariant leaks inputs horizon scheduler
    rawTrace
  have readyNative := (control.execution.application.publicView_eventReady event).mp ready
  obtain ⟨entered, activated⟩ := Option.isSome_iff_exists.mp
    ((invariant.activated_iff event).mpr ⟨readyNative, by rw [owned]; rfl⟩)
  have elapsed : input.elapsed = control.execution.application.clock - entered := by
    rw [← inputEq]
    change control.execution.application.clock -
      (control.execution.application.activatedAt event).getD control.execution.application.clock = _
    rw [activated, Option.getD_some]
  unfold countedSeedService at selected
  split at selected
  · rename_i timely
    cases head : input.emitted.head? with
    | none => simp only [head, Option.map_none] at selected; cases selected
    | some message =>
        simp only [head, Option.map_some] at selected
        cases Option.some.inj selected
        have localMember : message ∈ input.emitted := by
          obtain ⟨rest, emitted⟩ := List.head?_eq_some_iff.mp head
          rw [emitted]
          exact List.mem_cons_self
        rw [← inputEq] at localMember
        change message ∈ ((control.execution.network.inputs.filter fun packet =>
          packet.sender = owner).filter fun packet =>
          packet.payload.call.event? graph = some event) at localMember
        obtain ⟨authored, named⟩ := List.mem_filter.mp localMember
        obtain ⟨authentic, sender⟩ := List.mem_filter.mp authored
        have named' : message.payload.call.event? graph = some event := of_decide_eq_true named
        have sender' : message.sender = owner := of_decide_eq_true sender
        have timelyNative : control.execution.application.WithinDeadline runtime event := by
          simp only [State.WithinDeadline, activated]
          rwa [elapsed] at timely
        have pending := runtime.counted_survivor_pending leaks bounds inputs horizon scheduler
          control trace message authentic event named' (sender' ▸ unmissed) readyNative.1
          timelyNative
        have found := authentic_pending_lookup runtime leaks (inputs.map State.initial) horizon
          scheduler control rawTrace message pending
        have handled : ∃ next, (app).handle control.execution.application message = some next ∧
            event ∈ next.config.cut.completed := by
          cases call : message.payload.call with
          | malformed raw => rw [call] at named'; cases named'
          | commitment addressed candidate =>
              rw [call] at named'
              cases named'
              exact runtime.counted_binding_resolves_of_history leaks inputs horizon scheduler
                control rawTrace clean message authentic event candidate call readyNative
                timelyNative
          | opening addressed candidate raw =>
              rw [call] at named'
              cases named'
              obtain ⟨next, accepted⟩ := runtime.counted_opening_accepted leaks
                (inputs.map State.initial) (fun state supported => by
                  obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
                  exact ⟨initial, rfl⟩) horizon scheduler rawTrace clean message authentic event
                  candidate raw call (sender' ▸ unmissed) readyNative timelyNative
              refine ⟨next, accepted, ?_⟩
              obtain ⟨resolved, addressed, _, completed⟩ := handle_completes runtime _ _ _
                (reactiveHandle_call accepted)
              rw [call] at addressed
              change some event = some resolved at addressed
              rwa [Option.some.inj addressed]
        obtain ⟨result, accepted, completed⟩ := handled
        exact runtime.resolvingSeedCommand_include leaks event control.execution message.id message
          result found accepted completed
  · rename_i due
    cases Option.some.inj selected
    refine ⟨rfl, ?_⟩
    intro next moved
    obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
    obtain ⟨state, reached, rfl⟩ := PMF.support_map .. ▸ supported
    exact environmentStep_expire_complete runtime control.execution.application state event
      readyNative (by rw [owned]; rfl) entered activated (by rw [← elapsed]; omega) reached

/-- Genuine initialized actor-free one-packet histories with a binding-miss-free owner.
This is an endpoint domain, without a claim of preservation after that owner's timeout. -/
def CountedSeedDomain (bounds : MessageBounds graph) (inputs : PMF graph.Inputs)
    (owner : Player) (execution : (app).Execution) : Prop :=
  ∃ horizon scheduler remaining,
    Nonempty (((bounds.onePacketMenu runtime leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some ⟨remaining, none, execution⟩)) ∧
      execution.application.publicView.missedBindingBy owner = false

/-- Any actual clean history with no owner binding miss satisfies the concrete domain. -/
theorem countedSeedDomain_of_history (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control)) (owner : Player)
    (actorFree : control.actor = none)
    (unmissed : control.execution.application.publicView.missedBindingBy owner = false) :
    runtime.CountedSeedDomain leaks bounds inputs owner control.execution := by
  rcases control with ⟨remaining, actor, execution⟩
  cases actorFree
  exact ⟨horizon, scheduler, remaining, ⟨trace⟩, unmissed⟩

/-- Finite activation calendars and the choice to serve before a scheduled activation
remain seed parameters. Actual service acceptance follows from genuine clean traffic. -/
def countedLocalSeedController {Seed : Type} (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (owner : Player) (event : graph.EventId)
    (owned : graph.actor? event = some owner) (calendar : Seed → List Nat)
    (ordered : ∀ seed, (calendar seed).Pairwise (· ≤ ·))
    (serviceFirst : Seed → LocalSeedInput graph → Bool) :
    LocalSeedController runtime leaks Seed owner event where
  calendar := calendar
  ordered := ordered
  service _ input := runtime.countedSeedService leaks event input
  serviceFirst := serviceFirst
  domain := runtime.CountedSeedDomain leaks bounds inputs owner
  resolves := by
    rintro seed query execution command ⟨horizon, scheduler, remaining, ⟨trace⟩, unmissed⟩
      inputEq ready selected
    exact runtime.countedSeedService_resolves leaks bounds inputs horizon scheduler
      ⟨remaining, none, execution⟩ trace owner event owned unmissed query.input inputEq ready
      command
      selected

end Vegas.EventGraphRuntime
