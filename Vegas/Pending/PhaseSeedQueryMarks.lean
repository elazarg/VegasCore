/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedServiceMarks

/-! # Each actual local query consumes a new service ticket -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

def selectedAt
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (execution : (app).Execution) : Option (PhaseSeedAddress graph) :=
  selectOpen runtime leaks (replayClosed runtime leaks priority rest execution.environmentRecall)
    (execution.observeEnvironment app) (priority rest
      execution.environmentRecall (execution.observeEnvironment app))

def queryAt (execution : (app).Execution) (coordinate : PhaseSeedAddress graph) (owner : Player) :=
  PhaseSeedInput.operational coordinate.1.attempt
    (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner execution.environmentRecall
      (execution.observeEnvironment app))

theorem selected_request
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) {inputs : graph.Inputs} (execution : (app).Execution)
    (valid : execution.application.Invariant inputs) (coordinate : PhaseSeedAddress graph)
    (selected : selectedAt runtime leaks priority rest execution = some coordinate) :
    ∃ owner, execution.application.SeedRequest owner coordinate.1 := by
  have member := (Finset.mem_filter.mp (selectOpen_mem runtime leaks selected)).1
  obtain ⟨owner, requested⟩ := (PhaseSeedScheduler.mem_eligible runtime leaks _ _).mp member
  exact ⟨owner, (PhaseRuntimeState.requests_publicView _ valid owner coordinate.1).mp requested⟩

theorem choose_eq_reply
    (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (execution : (app).Execution) (coordinate : PhaseSeedAddress graph)
    (selected : selectedAt runtime leaks priority seeds.1 execution = some coordinate)
    (owner : Player) (actor : graph.actor? coordinate.1.event = some owner) :
    (controller runtime leaks delay bound priority).choose seeds execution.environmentRecall
      (execution.observeEnvironment app) =
        reply runtime leaks delay bound coordinate (seeds.2 coordinate)
          (queryAt runtime leaks execution coordinate owner) := by
  simp only [ReactiveApplication.AddressedScheduler.choose, controller, selectedAt] at selected ⊢
  rw [selected]
  simp only [Option.bind_some, actor, Option.map_some, queryAt]

theorem activation_owner
    (delay bound : graph.EventId → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (coordinate : PhaseSeedAddress graph)
    (input : PhaseSeedOperationalInput graph) (owner expected : Player)
    (actor : graph.actor? coordinate.1.event = some expected)
    (activated : reply runtime leaks delay bound coordinate (seeds.2 coordinate) input =
      .activate owner) : owner = expected := by
  unfold reply at activated
  cases chosen : decision runtime delay bound coordinate (seeds.2 coordinate) input with
  | activation =>
      simpa only [chosen, actor, Option.map_some, Option.getD_some,
        ReactiveApplication.Command.activate.injEq, eq_comm] using activated
  | inclusion index =>
      cases emitted : input.emissions[index]? <;> simp [chosen, emitted] at activated
  | expiry => simp only [chosen] at activated; cases activated
  | wait => simp only [chosen] at activated; cases activated

omit [Fintype Player] in
private theorem activation_application (execution next : (app).Execution) (owner : Player)
    (reached : next ∈ (execution.environmentStep app (.activate owner)).support) :
    next.application = execution.application := by
  obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
  obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ supported
  rfl

/-- A selected activation is attributed to its actual ready owner and retained
in the full physical recall; original activation clocks remain immutable. -/
theorem activation_mark_valid
    (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    {inputs : graph.Inputs} (execution next : (app).Execution)
    (valid : execution.application.Invariant inputs) (ordered : execution.application.Ordered)
    (coordinate : PhaseSeedAddress graph)
    (selected : selectedAt runtime leaks priority seeds.1 execution = some coordinate)
    (owner : Player)
    (chosen : (.activate owner : (app).Command) =
      (controller runtime leaks delay bound priority).choose seeds execution.environmentRecall
        (execution.observeEnvironment app))
    (reached : next ∈ (execution.environmentStep app (.activate owner)).support) :
    (ServiceMark.queried true execution.application.current.native.clock coordinate).Valid
      runtime leaks priority seeds.1 next := by
  obtain ⟨expected, request⟩ := selected_request runtime leaks priority seeds.1 execution valid
    coordinate selected
  have replyEq := (choose_eq_reply runtime leaks delay bound priority seeds execution coordinate
    selected expected request.2.2.2.1).symm.trans chosen.symm
  have ownerEq := activation_owner runtime leaks delay bound seeds coordinate _ owner expected
    request.2.2.2.1 replyEq
  subst expected
  obtain ⟨entered, closed⟩ := selected_bound runtime leaks delay bound priority seeds execution next
    valid ordered (.activate owner) chosen reached coordinate selected
  have applicationEq := activation_application runtime leaks execution next owner reached
  have beforeBound := closed
  rw [applicationEq] at beforeBound
  rcases beforeBound.event request.1 with completed | active
  · exact False.elim (request.2.2.1.1 completed)
  · refine ⟨entered, closed, owner,
      ⟨execution.observeEnvironment app, .activate owner⟩, ?_, rfl,
      (PhaseRuntimeState.requests_publicView _ valid owner coordinate.1).mpr request, ?_⟩
    · rw [(app).environmentStep_environmentRecall execution next (.activate owner) reached]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · change execution.application.current.native.clock -
        (execution.application.current.native.activatedAt coordinate.1.event).getD
          execution.application.current.native.clock = _
      rw [active.2.1, Option.getD_some]

/-- A nonactivation reply closes exactly this original physical coordinate at
this clock, including rejected packets and immediate retry installation. -/
theorem closure_mark_valid
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (execution next : (app).Execution)
    (coordinate : PhaseSeedAddress graph)
    (selected : selectedAt runtime leaks priority rest execution = some coordinate)
    (command : (app).Command) (idle : (command.actor? app).isNone = true)
    (reached : next ∈ (execution.environmentStep app command).support) :
    (ServiceMark.queried false execution.application.current.native.clock coordinate).Valid
      runtime leaks priority rest next := by
  refine ⟨(phaseApplication_clock_monotone runtime leaks).environmentStep execution next command
    reached, ?_⟩
  rw [(app).environmentStep_environmentRecall execution next command reached]
  exact closed_after_nonactivation runtime leaks priority rest _ _ coordinate command
    selected idle

/-- Current roster selection excludes all previously closed tickets. -/
theorem closure_mark_fresh
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (execution : (app).Execution)
    (coordinate : PhaseSeedAddress graph)
    (selected : selectedAt runtime leaks priority rest execution = some coordinate)
    (old : ServiceMark graph) (valid : old.Valid runtime leaks priority rest execution) :
    old.ticket ≠ (ServiceMark.queried false execution.application.current.native.clock
      coordinate).ticket := by
  cases old with
  | advanced tick =>
      simp only [ServiceMark.ticket, ne_eq, reduceCtorEq, not_false_eq_true]
  | sampled attempt =>
      simp only [ServiceMark.ticket, ne_eq, reduceCtorEq, not_false_eq_true]
  | queried activation tick prior =>
      cases activation with
      | true =>
          intro same
          have impossible : true = false := congrArg Prod.fst (Sum.inl.inj same)
          cases impossible
      | false =>
          intro same
          have samePair : (tick, prior) =
              (execution.application.current.native.clock, coordinate) :=
            (congrArg Prod.snd (Sum.inl.inj same))
          apply request_unclosed runtime leaks _ _ _ coordinate selected
          change (execution.application.current.native.clock, coordinate) ∈ _
          rw [← samePair]
          exact valid.2

/-- A previous activation at this physical tick is visible in the genuine own
clock word, so the concrete erased query cannot activate again. -/
theorem activation_mark_fresh
    (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    {inputs : graph.Inputs} (execution : (app).Execution)
    (invariant : execution.application.Invariant inputs) (coordinate : PhaseSeedAddress graph)
    (selected : selectedAt runtime leaks priority seeds.1 execution = some coordinate)
    (owner : Player)
    (chosen : (.activate owner : (app).Command) =
      (controller runtime leaks delay bound priority).choose seeds execution.environmentRecall
        (execution.observeEnvironment app))
    (old : ServiceMark graph) (valid : old.Valid runtime leaks priority seeds.1 execution) :
    old.ticket ≠ (ServiceMark.queried true execution.application.current.native.clock
      coordinate).ticket := by
  cases old with
  | advanced tick => simp only [ServiceMark.ticket, ne_eq, reduceCtorEq, not_false_eq_true]
  | sampled attempt => simp only [ServiceMark.ticket, ne_eq, reduceCtorEq, not_false_eq_true]
  | queried activation tick prior =>
      cases activation with
      | false =>
          intro same
          have impossible : false = true := congrArg Prod.fst (Sum.inl.inj same)
          cases impossible
      | true =>
          intro same
          have samePair : (tick, prior) =
              (execution.application.current.native.clock, coordinate) :=
            (congrArg Prod.snd (Sum.inl.inj same))
          have tickEq : tick = execution.application.current.native.clock :=
            congrArg Prod.fst samePair
          have coordinateEq : prior = coordinate := congrArg Prod.snd samePair
          subst tick
          subst prior
          obtain ⟨entered, closed, oldOwner, entry, member, activated, requested, elapsed⟩ := valid
          obtain ⟨expected, request⟩ := selected_request runtime leaks priority seeds.1 execution
            invariant coordinate selected
          have replyEq := (choose_eq_reply runtime leaks delay bound priority seeds execution
            coordinate selected expected request.2.2.2.1).symm.trans chosen.symm
          have ownerEq := activation_owner runtime leaks delay bound seeds coordinate _ owner
            expected request.2.2.2.1 replyEq
          subst expected
          have oldOwnerEq : oldOwner = owner := Option.some.inj
            (requested.2.2.2.1.symm.trans request.2.2.2.1)
          subst oldOwner
          rcases closed.event request.1 with completed | active
          · exact request.2.2.1.1 completed
          · have sameElapsed :
                PhaseSeedScheduler.elapsed runtime leaks coordinate.1 entry.beforeView =
                PhaseSeedScheduler.elapsed runtime leaks coordinate.1
                  (execution.observeEnvironment app) := by
              rw [elapsed]
              change _ = execution.application.current.native.clock -
                (execution.application.current.native.activatedAt coordinate.1.event).getD
                  execution.application.current.native.clock
              rw [active.2.1, Option.getD_some]
            exact reply_ne_activate_of_entry runtime leaks delay bound coordinate
              (seeds.2 coordinate) owner _ _ entry member activated requested sameElapsed replyEq

end Vegas.EventGraphRuntime.PhaseSeedCalendar
