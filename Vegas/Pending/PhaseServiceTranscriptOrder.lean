/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceQueryStrictOrder
import Interaction.ReactiveAddressedTranscriptOrder

/-! # Actual phased query order and unique elapsed-clock wait records -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

open Classical in
/-- Actual elapsed clocks of nonactivation queries, in their original order. -/
def waitClocks
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph)
    (past : List (app).EnvironmentEntry) : List Nat :=
  ((controller runtime leaks priority decideLocal).coordinateTranscriptFrom rest coordinate []
    past).filterMap fun item => if item.2 = .wait then some item.1.elapsed else none

/-- Every counted wait clock comes from an actual queried WAIT pair. -/
theorem waitClocks_mem_iff
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph)
    (past : List (app).EnvironmentEntry) (tick : Nat) :
    tick ∈ waitClocks runtime leaks priority decideLocal rest coordinate past ↔
      ∃ query, (query, .wait) ∈
        (controller runtime leaks priority decideLocal).coordinateTranscriptFrom rest coordinate []
          past ∧ query.elapsed = tick := by
  classical
  unfold waitClocks
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨item, member, clock⟩
    by_cases waited : item.2 = .wait
    · rw [ite_eq_left waited] at clock
      refine ⟨item.1, ?_, Option.some.inj clock⟩
      have pair : item = (item.1, .wait) := Prod.ext rfl waited
      rw [← pair]
      exact member
    · rw [ite_eq_right waited] at clock
      cases clock
  · rintro ⟨query, member, clock⟩
    exact ⟨(query, .wait), member, by simp only [ite_true, clock]⟩

/-- The full actual transcript retains nondecreasing elapsed clocks, and every
nonactivation is followed only by strictly later clocks at that coordinate. -/
theorem runRounds_transcript_clockOrder
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (plan : RuntimePhasePlan graph) (input : graph.Inputs)
    (players : Player → (app).Policy) (count : Nat) (execution : (app).Execution)
    (reached : execution ∈ ((app).runRounds
      ((controller runtime leaks priority decideLocal).family seeds) players count
        (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input))).support)
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner) :
    ((controller runtime leaks priority decideLocal).coordinateTranscriptFrom seeds.1 coordinate []
      execution.environmentRecall).Pairwise (fun first second =>
        first.1.elapsed ≤ second.1.elapsed ∧ ((first.2.actor? app).isNone = true →
          first.1.elapsed < second.1.elapsed)) := by
  apply ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_pairwise
  intro before first between second after firstQuery secondQuery recorded firstAt secondAt
  simp only [List.nil_append] at firstAt secondAt
  refine ⟨recorded_queries_elapsed_mono runtime leaks priority decideLocal seeds plan input
    players count execution reached coordinate owner actor before first between second after
      recorded firstQuery secondQuery firstAt secondAt, ?_⟩
  intro idle
  exact recorded_queries_elapsed_strict_after_nonactivation runtime leaks priority decideLocal
    seeds plan input players count execution reached coordinate owner actor before first between
      second after recorded firstQuery secondQuery firstAt secondAt idle

/-- Every physical WAIT clock occurs once. This follows from actual query
order, without any first-delay or local-seed distribution premise. -/
theorem runRounds_waitClocks_nodup
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (plan : RuntimePhasePlan graph) (input : graph.Inputs)
    (players : Player → (app).Policy) (count : Nat) (execution : (app).Execution)
    (reached : execution ∈ ((app).runRounds
      ((controller runtime leaks priority decideLocal).family seeds) players count
        (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input))).support)
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner) :
    (waitClocks runtime leaks priority decideLocal seeds.1 coordinate
      execution.environmentRecall).Nodup := by
  classical
  have ordered := runRounds_transcript_clockOrder runtime leaks priority decideLocal seeds plan
    input players count execution reached coordinate owner actor
  have strict : (waitClocks runtime leaks priority decideLocal seeds.1 coordinate
      execution.environmentRecall).Pairwise (· < ·) := by
    apply ordered.filterMap
    intro first second related left leftAt right rightAt
    by_cases waited : first.2 = .wait
    · rw [ite_eq_left waited] at leftAt
      have clock := Option.some.inj leftAt
      by_cases otherWaited : second.2 = .wait
      · rw [ite_eq_left otherWaited] at rightAt
        have otherClock := Option.some.inj rightAt
        rw [← clock, ← otherClock]
        exact related.2 (by rw [waited]; rfl)
      · rw [ite_eq_right otherWaited] at rightAt
        cases rightAt
    · rw [ite_eq_right waited] at leftAt
      cases leftAt
  exact strict.imp (fun earlier => Nat.ne_of_lt earlier)

end Vegas.EventGraphRuntime.PhaseServiceScheduler
