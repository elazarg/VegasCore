/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedResolutionWindow
import Vegas.Pending.PhaseSeedEmissionPersistence
import Vegas.Pending.PhaseSeedQueryMarks

/-! # An authorized earlier emission cannot be ignored on a service tick -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [DecidableEq Player] in
/-- A wait excludes both protection and a true current coin for every authorized
member of the actual operational emission word, without a singleton-word premise. -/
theorem decision_wait_excludes_service (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (seed : Seed runtime delay)
    (input : PhaseSeedOperationalInput graph) (emission : PhaseSeedEmission graph)
    (member : emission ∈ input.emissions) (authorized : emission.authorized = true)
    (waited : decision runtime delay bound coordinate seed input = .wait) :
    ¬ emission.clock + bound coordinate.1.event < runtime.deadline coordinate.1.event ∧
      seed.2 (Fin.ofNat (clockLimit runtime delay + 1) input.elapsed) = false := by
  unfold decision at waited
  split at waited
  · cases waited
  · split at waited
    · cases waited
    · cases found : input.emissions.zipIdx.find? (fun entry => entry.1.authorized &&
          (entry.1.clock + bound coordinate.1.event < runtime.deadline coordinate.1.event ||
            seed.2 (Fin.ofNat (clockLimit runtime delay + 1) input.elapsed))) with
      | none =>
          obtain ⟨index, indexed⟩ := List.mem_iff_getElem?.mp member
          have zipped : (emission, index) ∈ input.emissions.zipIdx :=
            List.mem_zipIdx_iff_getElem?.mpr indexed
          have excluded := (List.find?_eq_none.mp found) (emission, index) zipped
          simpa only [authorized, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq,
            not_or, Bool.not_eq_true] using excluded
      | some entry => simp only [found, reduceCtorEq] at waited

/-- A wait command is an actual wait decision: a purported inclusion index
cannot fall outside the finite word selected by the same decision. -/
theorem decision_wait_of_reply_wait (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (seed : Seed runtime delay)
    (owner : Player) (acting : graph.actor? coordinate.1.event = some owner)
    (input : PhaseSeedOperationalInput graph)
    (waited : reply runtime leaks delay bound coordinate seed input = .wait) :
    decision runtime delay bound coordinate seed input = .wait := by
  cases decided : decision runtime delay bound coordinate seed input with
  | wait => rfl
  | activation =>
      simp only [reply, decided, acting, Option.map_some, Option.getD_some] at waited
      cases waited
  | expiry => simp only [reply, decided] at waited; cases waited
  | inclusion index =>
      obtain ⟨emission, indexed, _authorized, _timely⟩ :=
        decision_inclusion_witness runtime delay bound coordinate seed input index decided
      simp only [reply, decided, indexed, Option.map_some, Option.getD_some] at waited
      cases waited

/-- Every earlier authorized timed emission remains effective in future actual
selected queries, even with arbitrary foreign interleavings and reset effects.
A wait then proves this precise original coin was false and the packet unprotected. -/
theorem runRounds_wait_excludes_earlier_emission (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    (wordRecall : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (clean : PhaseCount.CountClean runtime leaks execution)
    (continued : next ∈ ((app).runRounds
      ((controller runtime leaks delay bound priority).family seeds) players count
        execution).support)
    (owner : Player) (coordinate : PhaseSeedAddress graph)
    (acting : graph.actor? coordinate.1.event = some owner)
    (selected : selectedAt runtime leaks priority seeds.1 next = some coordinate)
    (clock : Nat) (message : Message Player (CommitAttemptPacket graph))
    (recorded : (clock, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions)
    (waited : (controller runtime leaks delay bound priority).choose seeds next.environmentRecall
      (next.observeEnvironment app) = .wait) :
    ¬ clock + bound coordinate.1.event < runtime.deadline coordinate.1.event ∧
      (seeds.2 coordinate).2 (Fin.ofNat (clockLimit runtime delay + 1)
        (queryAt runtime leaks next coordinate owner).elapsed) = false := by
  have authentic := PhaseSeedScheduler.localInput_emission_authentic runtime leaks execution
    coordinate.1 owner wordRecall clean.1.1 clock message recorded
  have permitted := (PhaseCount.permits_eq_true_iff execution.network.inputs message).mp
    (clean.2 message authentic.1)
  have authorized : message.payload.tokenValid coordinate.1.attempt = true := by
    simpa only [CommitAttemptPacket.tokenValid, authentic.2.2.1, decide_true, Bool.true_and]
      using permitted.1
  have retainedWord := PhaseSeedScheduler.runRounds_emissions_prefix runtime leaks
    ((controller runtime leaks delay bound priority).family seeds) players count execution next
      wordRecall continued owner coordinate.1
  have retained := retainedWord.subset recorded
  have operational : PhaseSeedInput.operationalEmission coordinate.1.attempt (clock, message) ∈
      (queryAt runtime leaks next coordinate owner).emissions := List.mem_map.mpr
    ⟨(clock, message), retained, rfl⟩
  have actualWait := (choose_eq_reply runtime leaks delay bound priority seeds next coordinate
    selected owner acting).symm.trans waited
  exact decision_wait_excludes_service runtime delay bound coordinate (seeds.2 coordinate)
    (queryAt runtime leaks next coordinate owner)
    (PhaseSeedInput.operationalEmission coordinate.1.attempt (clock, message)) operational
    authorized (decision_wait_of_reply_wait runtime leaks delay bound coordinate
      (seeds.2 coordinate) owner acting (queryAt runtime leaks next coordinate owner) actualWait)

end Vegas.EventGraphRuntime.PhaseSeedCalendar
