/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedUnsentQueries

/-! # Earlier local-query clocks remain in permanent owner recall -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
private theorem owner_clocks_mono (coordinate : CommitAttemptEvent graph) (owner : Player)
    (first later : List (app).PlayerEntry) (retained : first ⊆ later) :
    (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner first).map Prod.fst ⊆
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner later).map Prod.fst := by
  intro clock present
  obtain ⟨record, member, same⟩ := List.mem_map.mp present
  obtain ⟨entry, recorded, entryEq⟩ := List.mem_map.mp member
  refine List.mem_map.mpr ⟨record, ?_, same⟩
  exact List.mem_map.mpr ⟨entry, List.mem_filter.mpr
    ⟨retained (List.mem_filter.mp recorded).1, (List.mem_filter.mp recorded).2⟩, entryEq⟩

omit [Fintype Player] in
private theorem recall_dispatch_mono (players : Player → (app).Policy)
    (execution next : (app).Execution) (command : (app).Command) (owner : Player)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    execution.recall owner ⊆ next.recall owner := by
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
      exact (app).respond_recall_mono middle who owner response

/-- Every activation clock used by a reconstructed query is still observable
in this owner's complete physical-coordinate recall. -/
def QueryClocksRecalled (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (execution : (app).Execution) : Prop :=
  ∀ item ∈ (controller runtime leaks delay bound priority).coordinateTranscriptFrom
      rest coordinate [] execution.environmentRecall,
    ∀ clock ∈ item.1.activationClocks,
      clock ∈ (PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
        (execution.recall owner)).map Prod.fst

private theorem queryClocks_dispatch (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (players : Player → (app).Policy) (execution next : (app).Execution)
    (command : (app).Command) (word : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (valid : QueryClocksRecalled runtime leaks delay bound priority rest coordinate owner execution)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    QueryClocksRecalled runtime leaks delay bound priority rest coordinate owner next := by
  have retained := owner_clocks_mono runtime leaks coordinate.1 owner (execution.recall owner)
    (next.recall owner) (recall_dispatch_mono runtime leaks players execution next command owner
      reached)
  intro item member clock present
  rw [(app).dispatch_environmentRecall players command execution next reached,
    ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_append] at member
  rcases List.mem_append.mp member with old | latest
  · exact retained (valid item old clock present)
  · simp only [List.nil_append, ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom]
      at latest
    cases requested : (controller runtime leaks delay bound priority).request rest
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
          have requestedQuery : (controller runtime leaks delay bound priority).request rest
              execution.environmentRecall (execution.observeEnvironment app) =
                some (coordinate, input) := by simpa only [same] using requested
          have query := request_query runtime leaks delay bound priority rest execution coordinate
            owner actor input requestedQuery
          rw [query] at present
          change clock ∈ (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner
            execution.environmentRecall (execution.observeEnvironment app)).activationClocks
            at present
          rw [PhaseSeedScheduler.localInput_word, word owner coordinate.1] at present
          exact retained present
        · simp only [ite_eq_right same, List.not_mem_nil] at latest

/-- Recorded query clocks cannot be manufactured or forgotten by foreign
interleavings, retries, or unrestricted legal responses. -/
theorem runRounds_queryClocks (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (scheduler : (app).Scheduler) (players : Player → (app).Policy) (count : Nat)
    (execution next : (app).Execution)
    (word : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (valid : QueryClocksRecalled runtime leaks delay bound priority rest coordinate owner execution)
    (reached : next ∈ ((app).runRounds scheduler players count execution).support) :
    QueryClocksRecalled runtime leaks delay bound priority rest coordinate owner next := by
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
        (queryClocks_dispatch runtime leaks delay bound priority rest coordinate owner actor
          players execution middle command word valid dispatched) tail

end Vegas.EventGraphRuntime.PhaseSeedCalendar
