/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedInclusion

/-! # The original local coin window behind calendar inclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)

/-- The seed-only upper event for an envelope emitted no earlier than this tick.
Protected emissions succeed without consulting the local coin word. -/
def InclusionWindow (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (seed : Seed runtime delay) (sent : Nat) : Prop :=
  sent + bound coordinate.1.event < runtime.deadline coordinate.1.event ∨
    ∃ tick, sent ≤ tick ∧ tick < runtime.deadline coordinate.1.event ∧
      seed.2 (Fin.ofNat (clockLimit runtime delay + 1) tick) = true

omit [DecidableEq Player] in
/-- A later emission cannot achieve inclusion outside the earlier emission's
original-seed window. This statement keeps all timing and authorization data. -/
theorem inclusionWindow_of_decision (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (seed : Seed runtime delay)
    (input : PhaseSeedOperationalInput graph) (index sent : Nat)
    (emitted : ∀ emission ∈ input.emissions, sent ≤ emission.clock ∧ emission.clock ≤ input.elapsed)
    (chosen : decision runtime delay bound coordinate seed input = .inclusion index) :
    InclusionWindow runtime delay bound coordinate seed sent := by
  obtain ⟨emission, indexed, _authorized, timely, service⟩ :=
    decision_inclusion_service runtime delay bound coordinate seed input index chosen
  have bounds := emitted emission (List.mem_of_getElem? indexed)
  rcases service with protection | coin
  · exact Or.inl (lt_of_le_of_lt (Nat.add_le_add_right bounds.1 _) protection)
  · exact Or.inr ⟨input.elapsed, bounds.1.trans bounds.2, timely, coin⟩

omit [DecidableEq Player] in
/-- With one authorized envelope and the current activation already recorded,
the local rule includes exactly on protection or this tick's original coin. -/
theorem decision_single_emission (delay bound : graph.EventId → Nat)
    (coordinate : PhaseSeedAddress graph) (seed : Seed runtime delay)
    (elapsed : Nat) (clocks : List Nat) (emission : PhaseSeedEmission graph)
    (recorded : elapsed ∈ clocks) (authorized : emission.authorized = true)
    (timely : elapsed < runtime.deadline coordinate.1.event) :
    decision runtime delay bound coordinate seed ⟨elapsed, clocks, [emission]⟩ = .inclusion 0 ↔
      emission.clock + bound coordinate.1.event < runtime.deadline coordinate.1.event ∨
        seed.2 (Fin.ofNat (clockLimit runtime delay + 1) elapsed) = true := by
  cases coin : seed.2 (Fin.ofNat (clockLimit runtime delay + 1) elapsed) with
  | false =>
      simp only [Fin.ofNat_eq_cast] at coin
      by_cases protection : emission.clock + bound coordinate.1.event <
          runtime.deadline coordinate.1.event
      · simp [decision, Nat.not_le_of_lt timely, recorded, authorized, protection]
      · simp [decision, Nat.not_le_of_lt timely, recorded, authorized, coin, protection]
  | true =>
      simp only [Fin.ofNat_eq_cast] at coin
      simp [decision, Nat.not_le_of_lt timely, recorded, authorized, coin]

end Vegas.EventGraphRuntime.PhaseSeedCalendar
