/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceRecordedWait
import Interaction.ReactiveAddressedTranscriptAppend
import Interaction.ReactiveHistory

/-! # Earlier local queries retain exact prefixes of the actual owner clock word -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
private theorem owner_clocks_prefix (coordinate : CommitAttemptEvent graph) (owner : Player)
    (first later : List (app).PlayerEntry) (retained : first <+: later) :
    (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner first).map Prod.fst <+:
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner later).map Prod.fst := by
  obtain ⟨suffix, rfl⟩ := retained
  refine ⟨(PhaseSeedScheduler.ownerWord runtime leaks coordinate owner suffix).map Prod.fst, ?_⟩
  simp only [PhaseSeedScheduler.ownerWord, List.filter_append, List.map_append]

omit [Fintype Player] in
private theorem recall_dispatch_prefix (players : Player → (app).Policy)
    (execution next : (app).Execution) (command : (app).Command) (owner : Player)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    execution.recall owner <+: next.recall owner := by
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have recalled := (app).environmentStep_recall execution middle command moved
  cases active : command.actor? app with
  | none =>
      rw [active] at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      rw [recalled]
  | some who =>
      rw [active] at resumed
      obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
      rw [← recalled]
      exact (app).respond_recall_prefix middle who owner response

/-- Every actual queried activation word is an exact prefix of the final
physical-coordinate clock word, retaining repetitions and their order. -/
def QueryActivationPrefixes
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (execution : (app).Execution) : Prop :=
  ∀ item ∈ (controller runtime leaks priority decideLocal).coordinateTranscriptFrom
      rest coordinate [] execution.environmentRecall,
    item.1.activationClocks <+: (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        (execution.recall owner)).map Prod.fst

private theorem queryPrefixes_dispatch
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (players : Player → (app).Policy) (execution next : (app).Execution)
    (command : (app).Command) (word : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (valid : QueryActivationPrefixes runtime leaks priority decideLocal rest coordinate owner
      execution)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    QueryActivationPrefixes runtime leaks priority decideLocal rest coordinate owner next := by
  have retained := owner_clocks_prefix runtime leaks coordinate.1 owner (execution.recall owner)
    (next.recall owner) (recall_dispatch_prefix runtime leaks players execution next command owner
      reached)
  intro item member
  rw [(app).dispatch_environmentRecall players command execution next reached,
    ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_append] at member
  rcases List.mem_append.mp member with old | latest
  · exact (valid item old).trans retained
  · simp only [List.nil_append, ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom]
      at latest
    cases requested : (controller runtime leaks priority decideLocal).request rest
        execution.environmentRecall (execution.observeEnvironment app) with
    | none => simp only [requested, List.not_mem_nil] at latest
    | some selected =>
        rcases selected with ⟨selected, input⟩
        rw [requested] at latest
        change item ∈ (if selected = coordinate then [(input, command)] else []) at latest
        by_cases same : selected = coordinate
        · rw [ite_eq_left same] at latest
          have itemEq : item = (input, command) := by
            simpa only [List.mem_singleton] using latest
          subst item
          have requestedQuery : (controller runtime leaks priority decideLocal).request rest
              execution.environmentRecall (execution.observeEnvironment app) =
                some (coordinate, input) := by simpa only [same] using requested
          have query := request_query runtime leaks priority decideLocal rest execution coordinate
            owner actor input requestedQuery
          rw [query]
          change (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner
            execution.environmentRecall (execution.observeEnvironment app)).activationClocks <+:
              (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
                (next.recall owner)).map Prod.fst
          rw [PhaseSeedScheduler.localInput_word, word owner coordinate.1]
          exact retained
        · simp only [ite_eq_right same, List.not_mem_nil] at latest

/-- Original round execution retains every queried clock-word prefix, with
foreign interleavings, retries and arbitrary responses preserved. -/
theorem runRounds_queryActivationPrefixes
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (scheduler : (app).Scheduler) (players : Player → (app).Policy) (count : Nat)
    (execution next : (app).Execution)
    (word : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (valid : QueryActivationPrefixes runtime leaks priority decideLocal rest coordinate owner
      execution)
    (reached : next ∈ ((app).runRounds scheduler players count execution).support) :
    QueryActivationPrefixes runtime leaks priority decideLocal rest coordinate owner next := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid
  | succ count ih =>
      obtain ⟨middle, moved, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      exact ih middle
        (PhaseSeedScheduler.dispatch_wordRecall runtime leaks players command execution middle
          word dispatched)
        (queryPrefixes_dispatch runtime leaks priority decideLocal rest coordinate owner actor
          players execution middle command word valid dispatched) tail

/-- Every queried activation list in an actual initialized run is an exact
prefix of the final retained owner word; there is no supplied query-log premise. -/
theorem initialized_queryActivationPrefixes
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (scheduler : (app).Scheduler) (players : Player → (app).Policy) (count : Nat)
    (state : PhaseRuntimeState graph) (execution : (app).Execution)
    (reached : execution ∈ ((app).runRounds scheduler players count
      (ReactiveApplication.Execution.initial app state)).support) :
    QueryActivationPrefixes runtime leaks priority decideLocal rest coordinate owner execution :=
  runRounds_queryActivationPrefixes runtime leaks priority decideLocal rest coordinate owner actor
    scheduler players count (ReactiveApplication.Execution.initial app state) execution
      (PhaseSeedScheduler.initial_wordRecall runtime leaks state)
      (by intro item impossible; cases impossible) reached

end Vegas.EventGraphRuntime.PhaseServiceScheduler
