/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceScheduler
import Interaction.ReactiveAddressedTranscriptAppend
import Interaction.ReactiveServiceRounds

/-! # Actual activation recall for arbitrary phased service decisions -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The current actual scheduler query for the named owner and coordinate. -/
def queryAt (execution : (app).Execution) (coordinate : PhaseSeedAddress graph) (owner : Player) :=
  PhaseSeedInput.operational coordinate.1.attempt
    (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner execution.environmentRecall
      (execution.observeEnvironment app))

/-- A ready owner's actual activation is a query for this unique ready event,
even though the command carries only the owner identifier. -/
theorem callback_request
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (execution : (app).Execution) {inputs : graph.Inputs}
    (valid : execution.application.Invariant inputs) (ordered : graph.RevealRelaxedOrdered)
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate.1)
    (chosen : (controller runtime leaks priority decideLocal).choose seeds
      execution.environmentRecall (execution.observeEnvironment app) = .activate owner) :
    (controller runtime leaks priority decideLocal).request seeds.1
      execution.environmentRecall (execution.observeEnvironment app) =
        some (coordinate, queryAt runtime leaks execution coordinate owner) := by
  cases queried : (controller runtime leaks priority decideLocal).request seeds.1
      execution.environmentRecall (execution.observeEnvironment app) with
  | none =>
      have impossible :
          PhaseSeedCalendar.fallback runtime leaks (execution.observeEnvironment app) =
          .activate owner := by
        unfold ReactiveApplication.AddressedScheduler.choose at chosen
        rw [queried] at chosen
        exact chosen
      unfold PhaseSeedCalendar.fallback at impossible
      split at impossible
      · split at impossible <;> cases impossible
      · cases impossible
      · cases impossible
      · cases impossible
  | some selected =>
      rcases selected with ⟨selected, query⟩
      obtain ⟨actor, actual⟩ := request_sound runtime leaks priority decideLocal seeds.1 execution
        valid queried
      have replyEq : reply runtime leaks decideLocal selected (seeds.2 selected) query =
          .activate owner := by
        unfold ReactiveApplication.AddressedScheduler.choose at chosen
        rw [queried] at chosen
        exact chosen
      have sameOwner := activation_owner runtime leaks decideLocal selected (seeds.2 selected)
        query owner actor
        actual.2.2.2.1 replyEq
      subst actor
      have eventEq : selected.1.event = coordinate.1.event :=
        ordered.ready_actor_unique execution.application.current.native.config.cut
          request.2.2.1 actual.2.2.1 request.2.2.2.1 actual.2.2.2.1
      have same : selected = coordinate := by
        apply Subtype.ext
        exact congrArg₂ CommitAttemptEvent.mk (actual.1.trans request.1.symm) eventEq
      subst selected
      have inputEq := request_query runtime leaks priority decideLocal seeds.1 execution coordinate
        owner request.2.2.2.1 query queried
      exact congrArg (fun input => some (coordinate, input)) inputEq

open Classical in
/-- The relative clock of each actual activation reply for one local coordinate. -/
def activationTranscript
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (past : List (app).EnvironmentEntry) : List Nat :=
  (((controller runtime leaks priority decideLocal).coordinateTranscriptFrom
    rest coordinate [] past).filter fun item => decide (item.2 = .activate owner)).map
      fun item => item.1.elapsed

private theorem activationTranscript_dispatch
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (ordered : graph.RevealRelaxedOrdered) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (players : Player → (app).Policy) (execution next : (app).Execution)
    {inputs : graph.Inputs} (valid : execution.application.Invariant inputs)
    (word : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (same : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (execution.recall owner)).map Prod.fst =
        activationTranscript runtime leaks priority decideLocal seeds.1 coordinate owner
          execution.environmentRecall)
    (command : (app).Command)
    (chosen : command = (controller runtime leaks priority decideLocal).choose seeds
      execution.environmentRecall (execution.observeEnvironment app))
    (reached : next ∈ ((app).dispatch players command execution).support) :
    (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (next.recall owner)).map Prod.fst =
        activationTranscript runtime leaks priority decideLocal seeds.1 coordinate owner
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
  cases queried : (controller runtime leaks priority decideLocal).request seeds.1
      execution.environmentRecall (execution.observeEnvironment app) with
  | none =>
      have noCallback : ¬ PhaseSeedScheduler.callback runtime leaks coordinate.1 owner
          ⟨execution.observeEnvironment app, command⟩ := by
        rintro ⟨activated, visible⟩
        have ownRequest := (PhaseRuntimeState.requests_publicView _ valid _ _).mp visible
        have actual := callback_request runtime leaks priority decideLocal seeds execution valid
          ordered coordinate owner ownRequest (chosen.symm.trans activated)
        rw [queried] at actual
        cases actual
      simp only [List.filter_nil, List.map_nil, ite_eq_right noCallback]
  | some selected =>
      rcases selected with ⟨selected, query⟩
      by_cases selectedEq : selected = coordinate
      · subst selected
        have queryEq := request_query runtime leaks priority decideLocal seeds.1
          execution coordinate
          owner actor query queried
        obtain ⟨principal, requested⟩ := request_sound runtime leaks priority decideLocal seeds.1
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
          simp [activated, queryEq, PhaseSeedInput.operational]
          rfl
        · have actual := fun yes => activated (callback.mp yes)
          rw [ite_eq_right actual]
          simp [activated]
      · have noCallback : ¬ PhaseSeedScheduler.callback runtime leaks coordinate.1 owner
            ⟨execution.observeEnvironment app, command⟩ := by
          rintro ⟨activated, visible⟩
          have ownRequest := (PhaseRuntimeState.requests_publicView _ valid _ _).mp visible
          have actual := callback_request runtime leaks priority decideLocal seeds execution valid
            ordered coordinate owner ownRequest (chosen.symm.trans activated)
          rw [queried] at actual
          exact selectedEq (Prod.mk.inj (Option.some.inj actual)).1
        simp only [ite_eq_right selectedEq, List.filter_nil, List.map_nil,
          ite_eq_right noCallback]

/-- Actual complete rounds reconstruct the activation part of one coordinate's
query transcript from permanent owner recall, for arbitrary local decision rules
and priorities, including repeated activations at the same clock. -/
theorem runRounds_activationTranscript
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (ordered : graph.RevealRelaxedOrdered) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    {inputs : graph.Inputs} (valid : execution.application.Invariant inputs)
    (word : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (same : (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (execution.recall owner)).map Prod.fst =
        activationTranscript runtime leaks priority decideLocal seeds.1 coordinate owner
          execution.environmentRecall)
    (reached : next ∈ ((app).runRounds
      ((controller runtime leaks priority decideLocal).family seeds) players count
        execution).support) :
    (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (next.recall owner)).map Prod.fst =
        activationTranscript runtime leaks priority decideLocal seeds.1 coordinate owner
          next.environmentRecall := by
  have native : (app).ServiceInvariant
      ((controller runtime leaks priority decideLocal).family seeds)
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
      have commandEq : command = (controller runtime leaks priority decideLocal).choose seeds
          execution.environmentRecall (execution.observeEnvironment app) :=
        (PMF.mem_support_pure_iff _ _).mp chosen
      exact ih middle (native.dispatch players command execution middle valid chosen dispatched)
        (PhaseSeedScheduler.dispatch_wordRecall runtime leaks players command execution middle
          word dispatched)
        (activationTranscript_dispatch runtime leaks priority decideLocal seeds ordered coordinate
          owner actor players execution middle valid word same command commandEq dispatched) tail

end Vegas.EventGraphRuntime.PhaseServiceScheduler
