/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedInput

/-! # A current-event seed controller inside the actual reactive scheduler

Queries read only the current readiness-relative clock, the next activation
index and this event's emitted prefix. A reply activates this owner, resolves
this event, or closes the current clock. The remainder never receives the
local seed or query log. Repeated current-clock activations are permitted.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- One current-clock activation/survival query, with no independent future clock argument. -/
structure CurrentSeedQuery (graph : Vegas.EventGraph Player L) where
  input : LocalSeedInput graph
  activationIndex : Nat

/-- The only outputs of the local seed channel. -/
inductive LocalSeedReply (Command : Type) where
  | activation
  | resolution (command : Command)
  | exhausted

/-- A private record of an actual local query and its reply. -/
structure LocalSeedEntry (graph : Vegas.EventGraph Player L) (Command : Type) where
  query : CurrentSeedQuery graph
  reply : LocalSeedReply Command

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => runtime.reactiveApplication leaks

/-- A service output is an inclusion or this event's expiry, and actually
completes the event at this genuine execution. It cannot signal via a
rejected inclusion or another event. -/
def ResolvingSeedCommand (event : graph.EventId) (execution : (app).Execution)
    (command : (app).Command) : Prop :=
  (match command with
    | .include _ => True
    | .application (.expire named) => named = event
    | _ => False) ∧
  ∀ next : (app).Execution,
    next ∈ (execution.environmentStep app command).support →
      event ∈ next.application.config.cut.completed

/-- A local calendar can contain arbitrarily many entries at the same clock.
Service reads only the exact local query and must resolve this event whenever
it emits a command on its genuine operational domain. Establishing this domain
on all lawful histories is a separate runtime obligation. -/
structure LocalSeedController (Seed : Type) (owner : Player) (event : graph.EventId) where
  calendar : Seed → List Nat
  ordered : ∀ seed, (calendar seed).Pairwise (· ≤ ·)
  service : Seed → LocalSeedInput graph → Option (app).Command
  serviceFirst : Seed → LocalSeedInput graph → Bool
  /-- An operational invariant of genuine executions, with no probabilistic premise. -/
  domain : (app).Execution → Prop
  resolves : ∀ seed (query : CurrentSeedQuery graph) execution command, domain execution →
    runtime.environmentSeedInput leaks owner event
      (execution.observeEnvironment app) = query.input →
    execution.application.publicView.EventReady event → service seed query.input = some command →
      runtime.ResolvingSeedCommand leaks event execution command

/-- Rejected traffic and all other nonresolving commands remain available to
the remainder. It cannot supply an owner activation or resolve the selected
ready event using a private local-seed signal. -/
def SeedRemainderCommand (owner : Player) (event : graph.EventId)
    (view : (app).EnvironmentView) (command : (app).Command) : Prop :=
  (view.application.EventReady event → command ≠ .activate owner) ∧
  ∀ execution next : (app).Execution, execution.observeEnvironment app = view →
    event ∉ execution.application.config.cut.completed →
    next ∈ (execution.environmentStep app command).support →
      event ∉ next.application.config.cut.completed

/-- Remainder input is its own seed and actual history, with no local query log. -/
structure SeedRemainderController (Seed : Type) (owner : Player) (event : graph.EventId) where
  choose : Seed → List (app).EnvironmentEntry → (app).EnvironmentView → Bool × (app).Command
  safe : ∀ seed past view,
    runtime.SeedRemainderCommand leaks owner event view (choose seed past view).2

/-- Private seed state and the actual query log, absent from runtime state. -/
structure LocalSeedMemory (LocalSeed RestSeed : Type) where
  localSeed : LocalSeed
  remainderSeed : RestSeed
  activationIndex : Nat
  closedAt : Option Nat
  log : List (LocalSeedEntry graph (app).Command)

namespace LocalSeedMemory

variable {runtime leaks} {LocalSeed RestSeed : Type}

/-- Substitute the local seed while retaining every other private component. -/
def replaceLocal (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (seed : LocalSeed) : LocalSeedMemory runtime leaks LocalSeed RestSeed :=
  { memory with localSeed := seed }

end LocalSeedMemory

namespace LocalSeedController

variable {runtime leaks} {LocalSeed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks LocalSeed owner event)

/-- Read the current calendar head and service status, never a future clock.
A service reply ends the event; exhausted means no current activation remains. -/
def reply (seed : LocalSeed) (query : CurrentSeedQuery graph) : LocalSeedReply (app).Command :=
  let service := controller.service seed query.input
  if (controller.calendar seed)[query.activationIndex]? = some query.input.elapsed then
    if controller.serviceFirst seed query.input then
      match service with
      | some command => .resolution command
      | none => .activation
    else .activation
  else match service with
    | some command => .resolution command
    | none => .exhausted

/-- Commit the local reply to private memory and emit only its corresponding command. -/
def finishReply (owner : Player) (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (fallback : (app).Command) (query : CurrentSeedQuery graph)
    (answer : LocalSeedReply (app).Command) :
    (app).Command × LocalSeedMemory runtime leaks LocalSeed RestSeed :=
  let recorded := { memory with log := memory.log ++ [⟨query, answer⟩] }
  match answer with
  | .activation =>
      (.activate owner, { recorded with activationIndex := memory.activationIndex + 1 })
  | .resolution command => (command, recorded)
  | .exhausted => (fallback, { recorded with closedAt := some query.input.elapsed })

theorem finishReply_log (owner : Player) (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (fallback : (app).Command) (query : CurrentSeedQuery graph)
    (answer : LocalSeedReply (app).Command) :
    (finishReply owner memory fallback query answer).2.log =
      memory.log ++ [⟨query, answer⟩] := by
  cases answer <;> rfl

private def advancesClock : (app).Command → Bool
  | .application .advanceClock => true
  | _ => false

open Classical in
/-- Polling or a proposed clock advance asks the current local calendar once.
An exhausted reply is memoized until the clock changes; the fixed fallback
was chosen without seeing that reply. -/
def step (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView) :
    (app).Command × LocalSeedMemory runtime leaks LocalSeed RestSeed :=
  let plan := remainder.choose memory.remainderSeed past view
  let input := runtime.environmentSeedInput leaks owner event view
  if view.application.EventReady event then
    if memory.closedAt = some input.elapsed then (plan.2, memory)
    else if plan.1 || advancesClock plan.2 then
      let query : CurrentSeedQuery graph := ⟨input, memory.activationIndex⟩
      finishReply owner memory plan.2 query (controller.reply memory.localSeed query)
    else (plan.2, memory)
  else (plan.2, memory)

/-- Every actual step retains its previous query log verbatim. -/
theorem step_log_prefix (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView) :
    memory.log <+: (controller.step remainder memory past view).2.log := by
  classical
  dsimp only [step]
  split_ifs
  · exact List.prefix_refl _
  · rw [finishReply_log]
    exact List.prefix_append _ _
  · exact List.prefix_refl _
  · exact List.prefix_refl _

/-- Replacing a seed leaves the bookkeeping for a fixed local reply unchanged. -/
theorem finishReply_replaceLocal (owner : Player)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) (seed : LocalSeed)
    (fallback : (app).Command) (query : CurrentSeedQuery graph)
    (answer : LocalSeedReply (app).Command) :
    finishReply owner (memory.replaceLocal seed) fallback query answer =
      ((finishReply owner memory fallback query answer).1,
        (finishReply owner memory fallback query answer).2.replaceLocal seed) := by
  cases answer <;> rfl

/-- The actual selected command depends on the local seed only through the
answer to its single current query. All other private components are retained. -/
theorem step_replaceLocal
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) (seed : LocalSeed)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (agrees : controller.reply seed
        ⟨runtime.environmentSeedInput leaks owner event view, memory.activationIndex⟩ =
      controller.reply memory.localSeed
        ⟨runtime.environmentSeedInput leaks owner event view, memory.activationIndex⟩) :
    controller.step remainder (memory.replaceLocal seed) past view =
      ((controller.step remainder memory past view).1,
        (controller.step remainder memory past view).2.replaceLocal seed) := by
  classical
  dsimp only [step, LocalSeedMemory.replaceLocal]
  split_ifs
  · rfl
  · rw [agrees]
    exact finishReply_replaceLocal owner memory seed _ _ _
  · rfl
  · rfl

/-- Agreement on the actual appended log suffices for a one-step seed splice. -/
theorem step_replaceLocal_of_log
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks LocalSeed RestSeed) (seed : LocalSeed)
    (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView)
    (agrees : ∀ entry ∈ (controller.step remainder memory past view).2.log,
      controller.reply seed entry.query = entry.reply) :
    controller.step remainder (memory.replaceLocal seed) past view =
      ((controller.step remainder memory past view).1,
        (controller.step remainder memory past view).2.replaceLocal seed) := by
  classical
  dsimp only [step, LocalSeedMemory.replaceLocal] at agrees ⊢
  split_ifs at agrees ⊢ with ready closed queried
  · rfl
  · have answer := agrees
      ⟨⟨runtime.environmentSeedInput leaks owner event view, memory.activationIndex⟩,
        controller.reply memory.localSeed
          ⟨runtime.environmentSeedInput leaks owner event view, memory.activationIndex⟩⟩
      (by rw [finishReply_log]; exact List.mem_append_right _ (by simp))
    rw [answer]
    exact finishReply_replaceLocal owner memory seed _ _ _
  · rfl
  · rfl

/-- Every resolution answer is an actual successful service lookup. -/
theorem service_of_resolution (seed : LocalSeed) (query : CurrentSeedQuery graph)
    (command : (app).Command) (answer : controller.reply seed query = .resolution command) :
    controller.service seed query.input = some command := by
  unfold reply at answer
  split_ifs at answer <;>
    cases serviceEq : controller.service seed query.input <;> simp_all

/-- A service answer completes the selected event on its genuine operational domain. -/
theorem resolution_completes (seed : LocalSeed) (query : CurrentSeedQuery graph)
    (execution next : (app).Execution) (command : (app).Command)
    (genuine : controller.domain execution)
    (inputEq : runtime.environmentSeedInput leaks owner event
      (execution.observeEnvironment app) = query.input)
    (ready : execution.application.publicView.EventReady event)
    (answer : controller.reply seed query = .resolution command)
    (reached : next ∈ (execution.environmentStep app command).support) :
    event ∈ next.application.config.cut.completed :=
  (controller.resolves seed query execution command genuine inputEq ready
    (controller.service_of_resolution seed query command answer)).2 next reached

/-- Install the local channel as an actual private scheduler implementation.
The fixed seed law is sampled independently of the initial application state. -/
def implementation (localLaw : PMF LocalSeed) (remainderLaw : PMF RestSeed)
    (remainder : SeedRemainderController runtime leaks RestSeed owner event) :
    (app).SchedulerImplementation (LocalSeedMemory runtime leaks LocalSeed RestSeed) where
  initial := localLaw.bind fun localSeed => remainderLaw.map fun remainderSeed =>
    ⟨localSeed, remainderSeed, 0, none, []⟩
  respond memory input := PMF.pure (controller.step remainder memory input.1 input.2)

end LocalSeedController
end Vegas.EventGraphRuntime
