/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedOperationalInput

/-! # A finite all-event calendar driver with fresh retry coordinates

At a clock tick the driver processes every ready coordinate before advancing
the clock. Activation leaves that coordinate open for its response and service;
a nonactivation reply closes it for this tick. Namespace changes retain the old
closed log and immediately make the fresh attempt coordinates available.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

namespace PhaseSeedCalendar


def clockLimit (delay : graph.EventId → Nat) : Nat :=
  Finset.univ.sum (fun event : graph.EventId => delay event + runtime.deadline event)

abbrev Seed (delay : graph.EventId → Nat) :=
  Fin (clockLimit runtime delay + 1) × (Fin (clockLimit runtime delay + 1) → Bool)

omit [Fintype Player] [DecidableEq Player] in
theorem delay_le_limit (delay : graph.EventId → Nat) (event : graph.EventId) :
    delay event ≤ clockLimit runtime delay := by
  exact (Nat.le_add_right (delay event) (runtime.deadline event)).trans
    (Finset.single_le_sum (f := fun event => delay event + runtime.deadline event)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ event))

omit [Fintype Player] [DecidableEq Player] in
theorem deadline_le_limit (delay : graph.EventId → Nat) (event : graph.EventId) :
    runtime.deadline event ≤ clockLimit runtime delay := by
  exact (Nat.le_add_left (runtime.deadline event) (delay event)).trans
    (Finset.single_le_sum (f := fun event => delay event + runtime.deadline event)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ event))

/-- Each event's delay and late-inclusion coins are sampled independently.
The same event law is used at every fresh phase/attempt address. -/
def eventLaw (delay : graph.EventId → Nat)
    (delayLaw : (event : graph.EventId) → PMF (Fin (delay event + 1)))
    (coinLaw : graph.EventId → Fin (clockLimit runtime delay + 1) → PMF Bool)
    (event : graph.EventId) : PMF (Seed runtime delay) :=
  (delayLaw event).bind fun first => (independentProduct (coinLaw event)).map fun coins =>
    (⟨first.val, first.isLt.trans_le (Nat.succ_le_succ (delay_le_limit runtime delay event))⟩,
      coins)

def laws (delay : graph.EventId → Nat)
    (delayLaw : (event : graph.EventId) → PMF (Fin (delay event + 1)))
    (coinLaw : graph.EventId → Fin (clockLimit runtime delay + 1) → PMF Bool) :
    PhaseSeedAddress graph → PMF (Seed runtime delay) :=
  fun coordinate => eventLaw runtime delay delayLaw coinLaw coordinate.1.event

def decision (delay bound : graph.EventId → Nat) (coordinate : PhaseSeedAddress graph)
    (seed : Seed runtime delay) (input : PhaseSeedOperationalInput graph) : PhaseSeedDecision :=
  if runtime.deadline coordinate.1.event ≤ input.elapsed then .expiry
  else if seed.1.val ≤ input.elapsed ∧ input.elapsed ∉ input.activationClocks then .activation
  else
    let permitted := input.emissions.zipIdx |>.find? fun entry =>
      entry.1.authorized &&
        (entry.1.clock + bound coordinate.1.event < runtime.deadline coordinate.1.event ||
          seed.2 (Fin.ofNat (clockLimit runtime delay + 1) input.elapsed))
    match permitted with
    | none => .wait
    | some entry => .inclusion entry.2

def openRoster (closed : Finset (Nat × PhaseSeedAddress graph)) (view : (app).EnvironmentView) :
    Finset (PhaseSeedAddress graph) :=
  (PhaseSeedScheduler.eligible runtime leaks view).filter fun coordinate =>
    (view.application.native.clock, coordinate) ∉ closed

def selectOpen (closed : Finset (Nat × PhaseSeedAddress graph))
    (view : (app).EnvironmentView) (priority : Nat) : Option (PhaseSeedAddress graph) :=
  (openRoster runtime leaks closed view).toList[priority]?.or
    (openRoster runtime leaks closed view).toList.head?

theorem selectOpen_mem {closed : Finset (Nat × PhaseSeedAddress graph)}
    {view : (app).EnvironmentView} {priority : Nat} {coordinate : PhaseSeedAddress graph}
    (selected : selectOpen runtime leaks closed view priority = some coordinate) :
    coordinate ∈ openRoster runtime leaks closed view := by
  unfold selectOpen at selected
  cases indexed : (openRoster runtime leaks closed view).toList[priority]? with
  | none =>
      simp only [indexed, Option.none_or] at selected
      exact Finset.mem_toList.mp (List.mem_of_mem_head? selected)
  | some value =>
      simp only [indexed, Option.some_or, Option.some.injEq] at selected
      subst value
      exact Finset.mem_toList.mp (List.mem_of_getElem? indexed)

def closeAfter (closed : Finset (Nat × PhaseSeedAddress graph))
    (view : (app).EnvironmentView) (selected : Option (PhaseSeedAddress graph))
    (command : (app).Command) : Finset (Nat × PhaseSeedAddress graph) :=
  if (command.actor? app).isNone then
    selected.elim closed fun coordinate => insert (view.application.native.clock, coordinate) closed
  else closed

def orderInput (view : (app).EnvironmentView) : Nat × CommitAttemptId :=
  (view.application.native.clock, view.application.attempt)

def clockAttemptPriority
    (priority : RestSeed → List (Nat × CommitAttemptId) → Nat × CommitAttemptId → Nat)
    (rest : RestSeed) (past : List (app).EnvironmentEntry) (view : (app).EnvironmentView) : Nat :=
  priority rest (past.map fun entry => orderInput runtime leaks entry.beforeView)
    (orderInput runtime leaks view)

def replayClosedFrom
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (closed : Finset (Nat × PhaseSeedAddress graph))
    (earlier : List (app).EnvironmentEntry) : List (app).EnvironmentEntry →
      Finset (Nat × PhaseSeedAddress graph)
  | [] => closed
  | entry :: later =>
      replayClosedFrom priority rest
        (closeAfter runtime leaks closed entry.beforeView
          (selectOpen runtime leaks closed entry.beforeView
            (priority rest earlier entry.beforeView))
          entry.command) (earlier ++ [entry]) later

def replayClosed
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (past : List (app).EnvironmentEntry) :=
  replayClosedFrom runtime leaks priority rest ∅ [] past

/-- Remainder operations cannot activate an owner or consume a packet. Samples
and clock changes use the actual application's ordinary environment commands. -/
def fallback (view : (app).EnvironmentView) : (app).Command :=
  match view.application.phase with
  | some (.sample, low, _) =>
      if bounded : low < graph.order.eventCount then .application (.executeSample ⟨low, bounded⟩)
      else .wait
  | some (.commitment, _, _) | some (.reveal, _, _) => .application .advanceClock
  | none => .wait

def reply (delay bound : graph.EventId → Nat) (coordinate : PhaseSeedAddress graph)
    (seed : Seed runtime delay) (input : PhaseSeedOperationalInput graph) : (app).Command :=
  match decision runtime delay bound coordinate seed input with
  | .activation => (graph.actor? coordinate.1.event).map
      (fun owner => (.activate owner : (app).Command)) |>.getD .wait
  | .inclusion index => (input.emissions[index]?).map
      (fun emission => (.include emission.identifier : (app).Command)) |>.getD .wait
  | .expiry => .application (.expire coordinate.1.event)
  | .wait => .wait

def controller (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat) :
    (app).AddressedScheduler (PhaseSeedAddress graph) (Seed runtime delay) RestSeed
      (PhaseSeedOperationalInput graph) where
  request rest past view :=
    (selectOpen runtime leaks (replayClosed runtime leaks priority rest past) view
      (priority rest past view)).bind fun coordinate =>
        (graph.actor? coordinate.1.event).map fun owner =>
          (coordinate, PhaseSeedInput.operational coordinate.1.attempt
            (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner past view))
  fallback _ _ view := fallback runtime leaks view
  reply := reply runtime leaks delay bound

/-- Every seed read by the finite calendar driver is for a genuine current,
ready, nonexcluded owned event in the installed phase. -/
theorem request_sound (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (execution : (app).Execution) {inputs : graph.Inputs}
    (valid : execution.application.Invariant inputs) {coordinate : PhaseSeedAddress graph}
    {query : PhaseSeedOperationalInput graph}
    (requested : (controller runtime leaks delay bound priority).request rest
      execution.environmentRecall (execution.observeEnvironment app) = some (coordinate, query)) :
    ∃ owner, execution.application.SeedRequest owner coordinate.1 := by
  unfold controller at requested
  cases chosen : selectOpen runtime leaks (replayClosed runtime leaks priority rest
      execution.environmentRecall) (execution.observeEnvironment app)
        (priority rest execution.environmentRecall
          (execution.observeEnvironment app)) with
  | none =>
      simp only [chosen, Option.bind_none] at requested
      cases requested
  | some selected =>
      cases acting : graph.actor? selected.1.event with
      | none =>
          simp only [chosen, Option.bind_some, acting, Option.map_none] at requested
          cases requested
      | some owner =>
          have same : selected = coordinate := by
            exact (Prod.mk.inj (Option.some.inj (by
              simpa only [chosen, Option.bind_some, acting, Option.map_some] using requested))).1
          subst selected
          have member := (Finset.mem_filter.mp (selectOpen_mem runtime leaks chosen)).1
          obtain ⟨owner, ready⟩ := (PhaseSeedScheduler.mem_eligible runtime leaks _ _).mp member
          exact ⟨owner, (PhaseRuntimeState.requests_publicView _ valid _ _).mp ready⟩

/-- Closing a tick never removes a previous address record, including records
from attempts whose source outputs have been voided. -/
theorem closeAfter_mono (closed : Finset (Nat × PhaseSeedAddress graph))
    (view : (app).EnvironmentView) (selected : Option (PhaseSeedAddress graph))
    (command : (app).Command) : closed ⊆ closeAfter runtime leaks closed view selected command := by
  unfold closeAfter
  split
  · cases selected with
    | none => exact Finset.Subset.refl _
    | some coordinate => exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

/-- No coordinate closed at this actual global clock can be queried again
before a clock change or a fresh attempt address. -/
theorem request_unclosed (closed : Finset (Nat × PhaseSeedAddress graph))
    (view : (app).EnvironmentView) (priority : Nat) (coordinate : PhaseSeedAddress graph)
    (selected : selectOpen runtime leaks closed view priority = some coordinate) :
    (view.application.native.clock, coordinate) ∉ closed :=
  (Finset.mem_filter.mp (selectOpen_mem runtime leaks selected)).2

variable {PrivateInput : Type}

/-- Nature and arbitrary original private randomization are drawn independently
of the full original event-seed vector. Behavioralization preserves their joint
law with the actual complete phase execution and every retained original seed. -/
theorem realize_private_joint (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (delayLaw : (event : graph.EventId) → PMF (Fin (delay event + 1)))
    (coinLaw : graph.EventId → Fin (clockLimit runtime delay + 1) → PMF Bool)
    (restLaw : PMF RestSeed) (privateLaw : PMF PrivateInput)
    (state : PrivateInput → PhaseRuntimeState graph)
    (players : PrivateInput → Player → (app).Policy) (count : Nat) :
    (privateLaw.bind fun privateInput =>
      (PMF.bind
        (ReactiveApplication.AddressedScheduler.prior (laws runtime delay delayLaw coinLaw) restLaw)
        fun seeds =>
          ((app).runRounds ((controller runtime leaks delay bound priority).family seeds)
            (players privateInput) count (ReactiveApplication.Execution.initial app
              (state privateInput))).map fun execution => (privateInput, execution, seeds))) =
      privateLaw.bind fun privateInput =>
        ((app).runRounds ((controller runtime leaks delay bound priority).implementation
          (laws runtime delay delayLaw coinLaw) restLaw).scheduler (players privateInput) count
            (ReactiveApplication.Execution.initial app (state privateInput))).bind fun execution =>
          (((controller runtime leaks delay bound priority).implementation
            (laws runtime delay delayLaw coinLaw) restLaw).posterior
              execution.environmentRecall).map
              fun seeds => (privateInput, execution, seeds) := by
  apply congrArg privateLaw.bind
  funext privateInput
  have same := congrArg (fun law => law.map fun pair => (privateInput, pair.1, pair.2))
    ((controller runtime leaks delay bound priority).realize_joint
      (laws runtime delay delayLaw coinLaw) restLaw (players privateInput) count
        (state privateInput))
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using same

end PhaseSeedCalendar
end Vegas.EventGraphRuntime
