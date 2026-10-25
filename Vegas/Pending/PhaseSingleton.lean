/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseApplication
import Vegas.Pending.ReactiveEventStability

/-! # Singleton commitment phases cannot retry a surviving owner

The interval and actor facts concern the actual phase descriptor. A fresh miss
in a singleton commitment phase excludes its only owner, so automatic phase
settlement advances without creating a surviving-owner attempt.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RuntimePhase

omit [DecidableEq Player] in
theorem events_eq_singleton (phase : RuntimePhase graph)
    (singleton : phase.high = phase.low + 1) :
    phase.events = {⟨phase.low, lt_of_lt_of_le phase.nonempty phase.bounded⟩} := by
  ext event
  simp only [mem_events, Finset.mem_singleton]
  constructor
  · intro inside
    apply Fin.ext
    simp only
    omega
  · intro same
    subst event
    exact ⟨le_rfl, phase.nonempty⟩

theorem owners_eq_singleton (phase : RuntimePhase graph)
    (singleton : phase.high = phase.low + 1) (kind : phase.kind = .commitment) :
    ∃ owner, phase.owners = {owner} := by
  let event : graph.EventId := ⟨phase.low, lt_of_lt_of_le phase.nonempty phase.bounded⟩
  have field := phase.fields event le_rfl phase.nonempty
  rw [kind] at field
  obtain ⟨owner, payload, binding⟩ := field
  refine ⟨owner, ?_⟩
  have actor := graph.actor?_of_outputLayout_binding binding
  rw [owners, phase.events_eq_singleton singleton]
  rw [Finset.singleton_biUnion]
  change (graph.actor? event).toFinset = {owner}
  rw [actor]
  rfl

theorem owners_subset_of_miss (phase : RuntimePhase graph)
    (singleton : phase.high = phase.low + 1) (kind : phase.kind = .commitment)
    (prior excluded : Finset Player)
    (missed : ((excluded \ prior) ∩ phase.owners).Nonempty) :
    phase.owners ⊆ excluded := by
  obtain ⟨owner, owners⟩ := phase.owners_eq_singleton singleton kind
  obtain ⟨missedOwner, missed⟩ := missed
  rw [owners] at missed ⊢
  obtain ⟨fresh, same⟩ := Finset.mem_inter.mp missed
  have equal := Finset.mem_singleton.mp same
  subst missedOwner
  exact Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp fresh).1

theorem no_survivors_of_miss (phase : RuntimePhase graph)
    (singleton : phase.high = phase.low + 1) (kind : phase.kind = .commitment)
    (prior excluded : Finset Player)
    (missed : ((excluded \ prior) ∩ phase.owners).Nonempty) :
    ¬ (phase.owners \ excluded).Nonempty := by
  intro survivor
  obtain ⟨owner, belongs⟩ := survivor
  exact (Finset.mem_sdiff.mp belongs).2
    (phase.owners_subset_of_miss singleton kind prior excluded missed
      (Finset.mem_sdiff.mp belongs).1)

/-- A singleton phase drains an eligible excluded event exactly once. -/
theorem drain_eq_completeAutomatic_of_singleton (phase : RuntimePhase graph)
    (state : RecoveryState graph) (event : graph.EventId) (only : phase.events = {event})
    (eligible : state.AutomaticReady event) :
    phase.drain state = state.completeAutomatic event eligible := by
  have clear : ∀ other, ¬ (other ∈ phase.events ∧
      (state.completeAutomatic event eligible).AutomaticReady other) := by
    intro other ⟨inside, ready⟩
    rw [only] at inside
    have same := Finset.mem_singleton.mp inside
    subst other
    obtain ⟨action, supported⟩ := state.completeAutomatic_step event eligible
    have cut := state.native.config.step_cut event eligible.1 action _ supported
    exact ready.1.1 (by rw [cut]; simp)
  have positive : 0 < state.native.config.remaining := by
    have progress := state.completeAutomatic_progress event eligible
    omega
  unfold drain
  cases fuelEq : state.native.config.remaining with
  | zero => omega
  | succ fuel =>
      rw [drainFuel]
      split
      · rename_i pending
        have selected : Classical.choose pending = event := by
          exact Finset.mem_singleton.mp
            ((Finset.ext_iff.mp only _).mp (Classical.choose_spec pending).1)
        have same : state.completeAutomatic (Classical.choose pending)
            (Classical.choose_spec pending).2 = state.completeAutomatic event eligible := by
          cases selected
          rfl
        rw [same]
        exact phase.drainFuel_eq_of_clear fuel _ clear
      · rename_i impossible
        exact (impossible ⟨event, by rw [only]; simp, eligible⟩).elim

end RuntimePhase

namespace PhaseRuntimeState

/-- Singleton commitment phases cannot allocate a surviving-owner retry generation. -/
theorem settle_generation_eq (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (singletons : ∀ phase ∈ phases, phase.kind = .commitment → phase.high = phase.low + 1) :
    (settle phases generation entry current retired).generation = generation := by
  revert singletons
  fun_induction settle with
  | case1 => exact fun _ => rfl
  | case2 phase remaining generation entry current retired drained finished failed
      checkpoint rebuilt archive survivors =>
      intro singletons
      exact (phase.no_survivors_of_miss
        (singletons phase (List.mem_cons_self ..) failed.1) failed.1 _ _ failed.2 survivors).elim
  | case3 phase remaining generation entry current retired drained finished failed
      checkpoint rebuilt archive exhausted ih =>
      intro singletons
      exact ih (fun target member => singletons target (List.mem_cons_of_mem _ member))
  | case4 phase remaining generation entry current retired drained finished clean ih =>
      intro singletons
      exact ih (fun target member => singletons target (List.mem_cons_of_mem _ member))
  | case5 => exact fun _ => rfl

end PhaseRuntimeState

end Vegas.EventGraphRuntime
