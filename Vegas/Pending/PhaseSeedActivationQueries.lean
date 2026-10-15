/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedUnsentQueries
import Vegas.Pending.PhaseSeedAttribution
import Interaction.ReactiveServiceRounds

/-! # Actual owner activations identify the selected physical coordinate -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A ready owner's actual activation is a query for this unique ready event,
even though the command carries only the owner identifier. -/
theorem callback_request (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (execution : (app).Execution) {inputs : graph.Inputs}
    (valid : execution.application.Invariant inputs) (ordered : graph.RevealRelaxedOrdered)
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate.1)
    (chosen : (controller runtime leaks delay bound priority).choose seeds
      execution.environmentRecall (execution.observeEnvironment app) = .activate owner) :
    (controller runtime leaks delay bound priority).request seeds.1
      execution.environmentRecall (execution.observeEnvironment app) =
        some (coordinate, queryAt runtime leaks execution coordinate owner) := by
  cases queried : (controller runtime leaks delay bound priority).request seeds.1
      execution.environmentRecall (execution.observeEnvironment app) with
  | none =>
      have impossible : fallback runtime leaks (execution.observeEnvironment app) =
          .activate owner := by
        unfold ReactiveApplication.AddressedScheduler.choose at chosen
        rw [queried] at chosen
        exact chosen
      unfold fallback at impossible
      split at impossible
      · split at impossible <;> cases impossible
      · cases impossible
      · cases impossible
      · cases impossible
  | some selected =>
      rcases selected with ⟨selected, query⟩
      obtain ⟨actor, actual⟩ := request_sound runtime leaks delay bound priority seeds.1 execution
        valid queried
      have replyEq : reply runtime leaks delay bound selected (seeds.2 selected) query =
          .activate owner := by
        unfold ReactiveApplication.AddressedScheduler.choose at chosen
        rw [queried] at chosen
        exact chosen
      have sameOwner := activation_owner runtime leaks delay bound seeds selected query owner actor
        actual.2.2.2.1 replyEq
      subst actor
      have eventEq : selected.1.event = coordinate.1.event :=
        ordered.ready_actor_unique execution.application.current.native.config.cut
          request.2.2.1 actual.2.2.1 request.2.2.2.1 actual.2.2.2.1
      have same : selected = coordinate := by
        apply Subtype.ext
        exact congrArg₂ CommitAttemptEvent.mk (actual.1.trans request.1.symm) eventEq
      subst selected
      have inputEq := request_query runtime leaks delay bound priority seeds.1 execution coordinate
        owner request.2.2.2.1 query queried
      rw [← inputEq]

open Classical in
/-- The relative clock of each actual activation reply for one local coordinate. -/
def activationTranscript (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (past : List (app).EnvironmentEntry) : List Nat :=
  (((controller runtime leaks delay bound priority).coordinateTranscriptFrom
    rest coordinate [] past).filter fun item => decide (item.2 = .activate owner)).map
      fun item => item.1.elapsed

private theorem activationTranscript_dispatch (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (ordered : graph.RevealRelaxedOrdered) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (players : Player → (app).Policy) (execution next : (app).Execution)
    {inputs : graph.Inputs} (valid : execution.application.Invariant inputs)
    (word : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (same : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (execution.recall owner)).map Prod.fst =
        activationTranscript runtime leaks delay bound priority seeds.1 coordinate owner
          execution.environmentRecall)
    (command : (app).Command)
    (chosen : command = (controller runtime leaks delay bound priority).choose seeds
      execution.environmentRecall (execution.observeEnvironment app))
    (reached : next ∈ ((app).dispatch players command execution).support) :
    (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (next.recall owner)).map Prod.fst =
        activationTranscript runtime leaks delay bound priority seeds.1 coordinate owner
          next.environmentRecall := by
  classical
  have afterWord := PhaseSeedScheduler.dispatch_wordRecall runtime leaks players command
    execution next word reached
  rw [← afterWord owner coordinate.1,
    (app).dispatch_environmentRecall players command execution next reached,
    PhaseSeedScheduler.word_snoc, List.map_append, word owner coordinate.1, same]
  unfold activationTranscript
  rw [ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_append,
    List.filter_append, List.map_append]
  congr 1
  simp only [List.nil_append, ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom]
  cases queried : (controller runtime leaks delay bound priority).request seeds.1
      execution.environmentRecall (execution.observeEnvironment app) with
  | none =>
      have noCallback : ¬ PhaseSeedScheduler.callback runtime leaks coordinate.1 owner
          ⟨execution.observeEnvironment app, command⟩ := by
        rintro ⟨activated, visible⟩
        have ownRequest := (PhaseRuntimeState.requests_publicView _ valid _ _).mp visible
        have actual := callback_request runtime leaks delay bound priority seeds execution valid
          ordered coordinate owner ownRequest (chosen.symm.trans activated)
        rw [queried] at actual
        cases actual
      simp only [List.filter_nil, List.map_nil, ite_eq_right noCallback]
  | some selected =>
      rcases selected with ⟨selected, query⟩
      by_cases selectedEq : selected = coordinate
      · subst selected
        have queryEq := request_query runtime leaks delay bound priority seeds.1
          execution coordinate
          owner actor query queried
        obtain ⟨principal, requested⟩ := request_sound runtime leaks delay bound priority seeds.1
          execution valid queried
        have principalEq : principal = owner := Option.some.inj
          (requested.2.2.2.1.symm.trans actor)
        subst principal
        have visible := (PhaseRuntimeState.requests_publicView _ valid _ _).mpr requested
        have callback : PhaseSeedScheduler.callback runtime leaks coordinate.1 owner
            ⟨execution.observeEnvironment app, command⟩ ↔ command = .activate owner :=
          ⟨And.left, fun activated => ⟨activated, visible⟩⟩
        by_cases activated : command = .activate owner
        · have actual : PhaseSeedScheduler.callback runtime leaks coordinate.1 owner
              ⟨execution.observeEnvironment app, command⟩ := callback.mpr activated
          rw [ite_eq_left actual]
          simp [activated, queryEq, queryAt, PhaseSeedInput.operational]
          rfl
        · have actual := fun yes => activated (callback.mp yes)
          rw [ite_eq_right actual]
          simp [activated]
      · have noCallback : ¬ PhaseSeedScheduler.callback runtime leaks coordinate.1 owner
            ⟨execution.observeEnvironment app, command⟩ := by
          rintro ⟨activated, visible⟩
          have ownRequest := (PhaseRuntimeState.requests_publicView _ valid _ _).mp visible
          have actual := callback_request runtime leaks delay bound priority seeds execution valid
            ordered coordinate owner ownRequest (chosen.symm.trans activated)
          rw [queried] at actual
          exact selectedEq (Prod.mk.inj (Option.some.inj actual)).1
        simp only [ite_eq_right selectedEq, List.filter_nil, List.map_nil,
          ite_eq_right noCallback]

/-- Actual complete rounds reconstruct the activation part of one coordinate's
query transcript from the owner's permanent recall, with arbitrary priorities. -/
theorem runRounds_activationTranscript (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (ordered : graph.RevealRelaxedOrdered) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    {inputs : graph.Inputs} (valid : execution.application.Invariant inputs)
    (word : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (same : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (execution.recall owner)).map Prod.fst =
        activationTranscript runtime leaks delay bound priority seeds.1 coordinate owner
          execution.environmentRecall)
    (reached : next ∈ ((app).runRounds
      ((controller runtime leaks delay bound priority).family seeds) players count
        execution).support) :
    (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (next.recall owner)).map Prod.fst =
        activationTranscript runtime leaks delay bound priority seeds.1 coordinate owner
          next.environmentRecall := by
  have native : (app).ServiceInvariant
      ((controller runtime leaks delay bound priority).family seeds)
      (fun current => current.application.Invariant inputs) :=
    ⟨(phaseApplication_invariant runtime leaks inputs).respond,
      fun before after command safe _ reached =>
        (phaseApplication_invariant runtime leaks inputs).environmentStep
          before after command safe reached⟩
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact same
  | succ count ih =>
      obtain ⟨middle, moved, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨command, chosen, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      have commandEq : command = (controller runtime leaks delay bound priority).choose seeds
          execution.environmentRecall (execution.observeEnvironment app) :=
        (PMF.mem_support_pure_iff _ _).mp chosen
      exact ih middle (native.dispatch players command execution middle valid chosen dispatched)
        (PhaseSeedScheduler.dispatch_wordRecall runtime leaks players command execution middle
          word dispatched)
        (activationTranscript_dispatch runtime leaks delay bound priority seeds ordered coordinate
          owner actor players execution middle valid word same command commandEq dispatched) tail

end Vegas.EventGraphRuntime.PhaseSeedCalendar
