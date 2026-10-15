/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedInclusion
import Interaction.ReactiveAddressedTranscriptAppend

/-! # Every queried emission is retained in the actual permanent signed traffic -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem request_query (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (execution : (app).Execution) (coordinate : PhaseSeedAddress graph)
    (owner : Player) (actor : graph.actor? coordinate.1.event = some owner)
    (query : PhaseSeedOperationalInput graph)
    (requested : (controller runtime leaks delay bound priority).request rest
      execution.environmentRecall (execution.observeEnvironment app) = some (coordinate, query)) :
    query = queryAt runtime leaks execution coordinate owner := by
  unfold controller at requested
  cases chosen : selectOpen runtime leaks
      (replayClosed runtime leaks priority rest execution.environmentRecall)
      (execution.observeEnvironment app)
      (priority rest execution.environmentRecall (execution.observeEnvironment app)) with
  | none => simp only [chosen, Option.bind_none, reduceCtorEq] at requested
  | some selected =>
      cases acting : graph.actor? selected.1.event with
      | none => simp only [chosen, Option.bind_some, acting, Option.map_none, reduceCtorEq]
          at requested
      | some principal =>
          have pair := Option.some.inj (by
            simpa only [chosen, Option.bind_some, acting, Option.map_some] using requested)
          have same : selected = coordinate := (Prod.mk.inj pair).1
          subst selected
          have ownerEq : principal = owner := Option.some.inj (acting.symm.trans actor)
          subst principal
          exact (Prod.mk.inj pair).2.symm

/-- Every emission appearing in an earlier queried local word still has an
actual signed input with this exact physical address and owner. -/
def QueryTraffic (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (execution : (app).Execution) : Prop :=
  ∀ item ∈ (controller runtime leaks delay bound priority).coordinateTranscriptFrom
      rest coordinate [] execution.environmentRecall,
    ∀ emission ∈ item.1.emissions,
      ∃ message ∈ execution.network.inputs,
        PhaseSeedScheduler.ownPacket coordinate.1 owner message = true

omit [Fintype Player] in
private theorem inputs_respond (execution : (app).Execution) (who : Player)
    (action : (app).Action) : execution.network.inputs ⊆
      (execution.respond app who action).network.inputs := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact List.Subset.refl _
  | some material => exact List.subset_append_left _ _

omit [Fintype Player] in
private theorem inputs_dispatch (players : Player → (app).Policy)
    (execution next : (app).Execution) (command : (app).Command)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    execution.network.inputs ⊆ next.network.inputs := by
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have inputs := (app).environmentStep_inputs execution middle command moved
  cases active : command.actor? app with
  | none =>
      rw [active] at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      rw [inputs]
  | some who =>
      rw [active] at resumed
      obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
      rw [← inputs]
      exact inputs_respond runtime leaks middle who response

omit [Fintype Player] in
private theorem inputRecall_dispatch (players : Player → (app).Policy)
    (execution next : (app).Execution) (command : (app).Command)
    (valid : execution.InputRecall app)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    next.InputRecall app := by
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have recalled := (app).environment_inputRecall execution middle command valid moved
  cases active : command.actor? app with
  | none =>
      rw [active] at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      exact recalled
  | some who =>
      rw [active] at resumed
      obtain ⟨response, _, rfl⟩ := PMF.support_map .. ▸ resumed
      exact (app).respond_inputRecall middle who response recalled

private theorem queryTraffic_dispatch (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (players : Player → (app).Policy) (execution next : (app).Execution)
    (command : (app).Command) (word : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (recalled : execution.InputRecall app)
    (valid : QueryTraffic runtime leaks delay bound priority rest coordinate owner execution)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    QueryTraffic runtime leaks delay bound priority rest coordinate owner next := by
  intro item member emission emitted
  rw [(app).dispatch_environmentRecall players command execution next reached,
    ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_append] at member
  rcases List.mem_append.mp member with old | latest
  · obtain ⟨message, authentic, own⟩ := valid item old emission emitted
    exact ⟨message, inputs_dispatch runtime leaks players execution next command reached authentic,
      own⟩
  · simp only [List.nil_append, ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom]
      at latest
    cases requested : (controller runtime leaks delay bound priority).request rest
        execution.environmentRecall (execution.observeEnvironment app) with
    | none => simp only [requested, List.not_mem_nil] at latest
    | some selected =>
        rcases selected with ⟨selected, input⟩
        rw [requested] at latest
        change item ∈ (if selected = coordinate then [(input, command)] else [])
          at latest
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
          rw [query] at emitted
          obtain ⟨packet, present, _⟩ := List.mem_map.mp emitted
          obtain ⟨authentic, sender, attempt, named⟩ :=
            PhaseSeedScheduler.localInput_emission_authentic runtime leaks execution coordinate.1
              owner word recalled packet.1 packet.2 present
          exact ⟨packet.2, inputs_dispatch runtime leaks players execution next command reached
            authentic, by simp only [PhaseSeedScheduler.ownPacket, sender, attempt, named,
              and_self, decide_true]⟩
        · simp only [ite_eq_right same, List.not_mem_nil] at latest

/-- The permanent input provenance of every earlier coordinate query is an
actual round invariant, with unrestricted player responses and arbitrary priority. -/
theorem runRounds_queryTraffic (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (scheduler : (app).Scheduler) (players : Player → (app).Policy) (count : Nat)
    (execution next : (app).Execution)
    (word : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (recalled : execution.InputRecall app)
    (valid : QueryTraffic runtime leaks delay bound priority rest coordinate owner execution)
    (reached : next ∈ ((app).runRounds scheduler players count execution).support) :
    QueryTraffic runtime leaks delay bound priority rest coordinate owner next := by
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
        (inputRecall_dispatch runtime leaks players execution middle command recalled dispatched)
        (queryTraffic_dispatch runtime leaks delay bound priority rest coordinate owner actor
          players execution middle command word recalled valid dispatched) tail

/-- No candidate inclusion coin can affect any earlier coordinate reply at an
actual unsent prefix: every reconstructed query has an empty emission list. -/
theorem queried_emissions_nil_of_unsent (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (scheduler : (app).Scheduler) (players : Player → (app).Policy) (count : Nat)
    (state : PhaseRuntimeState graph) (execution : (app).Execution)
    (reached : execution ∈ ((app).runRounds scheduler players count
      (ReactiveApplication.Execution.initial app state)).support)
    (unsent : ∀ message ∈ execution.network.inputs,
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false) :
    ∀ item ∈ (controller runtime leaks delay bound priority).coordinateTranscriptFrom
      rest coordinate [] execution.environmentRecall, item.1.emissions = [] := by
  have valid := runRounds_queryTraffic runtime leaks delay bound priority rest coordinate owner
    actor scheduler players count (ReactiveApplication.Execution.initial app state) execution
    (PhaseSeedScheduler.initial_wordRecall runtime leaks state) ((app).initial_inputRecall state)
    (by intro item impossible; cases impossible) reached
  intro item member
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro emission emitted
  obtain ⟨message, authentic, own⟩ := valid item member emission emitted
  exact Bool.noConfusion (own.symm.trans (unsent message authentic))

/-- At empty-emission queries the concrete reply reads only the first-delay
coordinate; all original inclusion-coin candidates give the same reply. -/
theorem reply_eq_of_first_eq_of_no_emissions (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (first second : Seed runtime delay)
    (query : PhaseSeedOperationalInput graph) (same : first.1 = second.1)
    (empty : query.emissions = []) :
    reply runtime leaks delay bound coordinate first query =
      reply runtime leaks delay bound coordinate second query := by
  simp only [reply, decision, empty, List.zipIdx_nil, List.find?_nil, same]

/-- For EVERY original candidate seed, the exact actual transcript filter at an
unsent prefix depends only on its first delay and ignores all inclusion coins. -/
theorem coordinateConsistent_iff_of_unsent_first_eq (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (scheduler : (app).Scheduler) (players : Player → (app).Policy) (count : Nat)
    (state : PhaseRuntimeState graph) (execution : (app).Execution)
    (reached : execution ∈ ((app).runRounds scheduler players count
      (ReactiveApplication.Execution.initial app state)).support)
    (unsent : ∀ message ∈ execution.network.inputs,
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false)
    (first second : Seed runtime delay) (same : first.1 = second.1) :
    (controller runtime leaks delay bound priority).coordinateConsistentFrom rest coordinate first
      [] execution.environmentRecall ↔
    (controller runtime leaks delay bound priority).coordinateConsistentFrom rest coordinate second
      [] execution.environmentRecall := by
  rw [ReactiveApplication.AddressedScheduler.coordinateConsistentFrom_iff_transcript,
    ReactiveApplication.AddressedScheduler.coordinateConsistentFrom_iff_transcript]
  have empty := queried_emissions_nil_of_unsent runtime leaks delay bound priority rest coordinate
    owner actor scheduler players count state execution reached unsent
  have equal : ∀ item ∈ (controller runtime leaks delay bound priority).coordinateTranscriptFrom
      rest coordinate [] execution.environmentRecall,
      reply runtime leaks delay bound coordinate first item.1 =
        reply runtime leaks delay bound coordinate second item.1 := by
    intro item member
    exact reply_eq_of_first_eq_of_no_emissions runtime leaks delay bound coordinate first second
      item.1 same (empty item member)
  constructor
  · intro matched item member
    exact (equal item member).symm.trans (matched item member)
  · intro matched item member
    exact (equal item member).trans (matched item member)

end Vegas.EventGraphRuntime.PhaseSeedCalendar
