module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveRoundTrace

@[expose] public section

/-! # Scheduler rounds stopped at a predicate

`Interaction.ReactiveApplication.runUntil` executes scheduler rounds until a
stopping predicate holds or its round budget is spent. Every round records
exactly one scheduler command, so the rounds left before a horizon are read
from the environment recall
(`runToHorizon`). Running to the horizon is the same as running to the
stopping point and then on to the horizon
(`runToHorizon_eq_runUntilHorizon_bind`): the round evaluator has the Markov
property at every stopping time, for arbitrary schedulers and player policies.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

/-- Scheduler rounds until `stop` holds, for at most `count` rounds. -/
def runUntil (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (stop : app.Execution → Prop) [DecidablePred stop] : Nat → app.Execution → PMF app.Execution
  | 0, execution => PMF.pure execution
  | count + 1, execution =>
      if stop execution then PMF.pure execution
      else (app.round scheduler players execution).bind (runUntil scheduler players stop count)

/-- The scheduler rounds left before `horizon`, counted from the environment
recall. -/
def runToHorizon (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (horizon : Nat) (execution : app.Execution) : PMF app.Execution :=
  app.runRounds scheduler players (horizon - execution.environmentRecall.length) execution

/-- Scheduler rounds until `stop` holds or the horizon is reached. -/
def runUntilHorizon (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (stop : app.Execution → Prop) [DecidablePred stop] (horizon : Nat)
    (execution : app.Execution) : PMF app.Execution :=
  app.runUntil scheduler players stop (horizon - execution.environmentRecall.length) execution

variable (scheduler : app.Scheduler) (players : Principal → app.Policy)

/-- A round records exactly one scheduler command. -/
theorem round_environmentRecall_length (execution next : app.Execution)
    (reached : next ∈ (app.round scheduler players execution).support) :
    next.environmentRecall.length = execution.environmentRecall.length + 1 := by
  obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  rw [app.dispatch_environmentRecall players command execution next dispatched]
  simp only [List.length_append, List.length_singleton]

theorem runRounds_environmentRecall_length (count : Nat) (execution next : app.Execution)
    (reached : next ∈ (app.runRounds scheduler players count execution).support) :
    next.environmentRecall.length = execution.environmentRecall.length + count := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | succ count ih =>
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      rw [ih middle rest, app.round_environmentRecall_length scheduler players execution middle
        moved]
      omega

theorem runUntil_of_stop (stop : app.Execution → Prop) [DecidablePred stop] (count : Nat)
    (execution : app.Execution) (stopped : stop execution) :
    app.runUntil scheduler players stop count execution = PMF.pure execution := by
  cases count with
  | zero => rfl
  | succ count => simp only [runUntil, stopped, ↓reduceIte]

/-- A stopped point is reached by some number of complete rounds within the
budget. -/
theorem runUntil_runRounds (stop : app.Execution → Prop) [DecidablePred stop] (count : Nat)
    (execution stopped : app.Execution)
    (reached : stopped ∈ (app.runUntil scheduler players stop count execution).support) :
    ∃ used ≤ count, stopped ∈ (app.runRounds scheduler players used execution).support ∧
      stopped.environmentRecall.length = execution.environmentRecall.length + used := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨0, le_rfl, by simp [runRounds], rfl⟩
  | succ count ih =>
      by_cases halt : stop execution
      · rw [app.runUntil_of_stop scheduler players stop _ execution halt] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact ⟨0, Nat.zero_le _, by simp [runRounds], rfl⟩
      · simp only [runUntil, halt, ↓reduceIte] at reached
        obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        obtain ⟨used, within, supported, length⟩ := ih middle rest
        refine ⟨used + 1, by omega, ?_, ?_⟩
        · rw [Nat.add_comm, runRounds_add, PMF.support_bind]
          exact Set.mem_iUnion₂.mpr ⟨middle,
            by simpa only [runRounds, PMF.bind_pure] using moved, supported⟩
        · rw [length, app.round_environmentRecall_length scheduler players execution middle moved]
          omega

/-- A stopped point satisfies the predicate or has spent the whole budget. -/
theorem runUntil_stopped (stop : app.Execution → Prop) [DecidablePred stop] (count : Nat)
    (execution stopped : app.Execution)
    (reached : stopped ∈ (app.runUntil scheduler players stop count execution).support) :
    stop stopped ∨
      stopped.environmentRecall.length = execution.environmentRecall.length + count := by
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact Or.inr rfl
  | succ count ih =>
      by_cases halt : stop execution
      · rw [app.runUntil_of_stop scheduler players stop _ execution halt] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact Or.inl halt
      · simp only [runUntil, halt, ↓reduceIte] at reached
        obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        rcases ih middle rest with done | spent
        · exact Or.inl done
        · right
          rw [spent, app.round_environmentRecall_length scheduler players execution middle moved]
          omega

/-- **Markov property at a stopping time.** Running to the horizon is running
until `stop`, then on to the horizon from the stopped point. -/
theorem runToHorizon_eq_runUntilHorizon_bind (stop : app.Execution → Prop) [DecidablePred stop]
    (horizon : Nat) (execution : app.Execution) :
    app.runToHorizon scheduler players horizon execution =
      (app.runUntilHorizon scheduler players stop horizon execution).bind
        (app.runToHorizon scheduler players horizon) := by
  unfold runUntilHorizon
  generalize left : horizon - execution.environmentRecall.length = count
  induction count generalizing execution with
  | zero =>
      simp only [runUntil, PMF.pure_bind]
  | succ count ih =>
      by_cases halt : stop execution
      · rw [app.runUntil_of_stop scheduler players stop _ execution halt, PMF.pure_bind]
      · simp only [runUntil, halt, ↓reduceIte, PMF.bind_bind]
        rw [runToHorizon, left, runRounds]
        apply bind_congr_on_support _
        intro middle moved
        have length := app.round_environmentRecall_length scheduler players execution middle moved
        have remaining : horizon - middle.environmentRecall.length = count := by omega
        have step := ih middle remaining
        rw [runToHorizon, remaining] at step
        exact step

/-- The remaining protocol play from an idle control state is the run to the
horizon. -/
theorem finish_eq_runToHorizon (initial : PMF app.State) (horizon remaining : Nat)
    (execution : app.Execution)
    (accounted : execution.environmentRecall.length + remaining = horizon) :
    app.finish initial horizon scheduler players (some ⟨remaining, none, execution⟩) =
      (app.runToHorizon scheduler players horizon execution).map app.finished := by
  have count : horizon - execution.environmentRecall.length = remaining := by omega
  simp only [finish, resume, PMF.pure_bind, runToHorizon, count]

/-- Complete rounds from a supported initialized execution stay supported. -/
theorem roundsFrom_runRounds (initial : PMF app.State) (count used : Nat)
    (execution next : app.Execution)
    (supported : execution ∈ (app.roundsFrom initial scheduler players count).support)
    (reached : next ∈ (app.runRounds scheduler players used execution).support) :
    next ∈ (app.roundsFrom initial scheduler players (count + used)).support := by
  obtain ⟨state, stateMem, prior⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  unfold roundsFrom
  rw [PMF.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨state, stateMem, ?_⟩
  rw [runRounds_add, PMF.support_bind]
  exact Set.mem_iUnion₂.mpr ⟨execution, prior, reached⟩

/-- Stopped points of a supported initialized execution are supported, at their
own recall length. -/
theorem roundsFrom_runUntil (initial : PMF app.State) (stop : app.Execution → Prop)
    [DecidablePred stop] (count : Nat) (execution stopped : app.Execution)
    (supported : execution ∈ (app.roundsFrom initial scheduler players
      execution.environmentRecall.length).support)
    (reached : stopped ∈ (app.runUntil scheduler players stop count execution).support) :
    stopped ∈ (app.roundsFrom initial scheduler players
      stopped.environmentRecall.length).support := by
  obtain ⟨used, _, rounds, length⟩ :=
    app.runUntil_runRounds scheduler players stop count execution stopped reached
  rw [length]
  exact app.roundsFrom_runRounds scheduler players initial _ used execution stopped supported rounds

/-- A stopped point before the horizon satisfies the predicate, or the horizon is
spent. -/
theorem runUntilHorizon_stopped
    (stop : app.Execution → Prop) [DecidablePred stop] (horizon remaining : Nat)
    (execution stopped : app.Execution)
    (accounted : execution.environmentRecall.length + remaining = horizon)
    (reached : stopped ∈ (app.runUntilHorizon scheduler players stop horizon execution).support) :
    stop stopped ∨ stopped.environmentRecall.length = horizon := by
  rcases app.runUntil_stopped scheduler players stop _ execution stopped reached with done | spent
  · exact Or.inl done
  · right
    omega

/-- Two stopping rules that agree along runs keeping an invariant stop those
runs alike. -/
theorem runUntil_stop_congr (first second : app.Execution → Prop) [DecidablePred first]
    [DecidablePred second] (invariant : app.Execution → Prop)
    (agree : ∀ execution, invariant execution → (first execution ↔ second execution))
    (preserved : ∀ execution, invariant execution → ¬ first execution →
      ∀ next ∈ (app.round scheduler players execution).support, invariant next) :
    ∀ (count : Nat) (execution : app.Execution), invariant execution →
      app.runUntil scheduler players first count execution =
        app.runUntil scheduler players second count execution := by
  intro count
  induction count with
  | zero => intro _ _; rfl
  | succ count ih =>
      intro execution holds
      by_cases halt : first execution
      · rw [app.runUntil_of_stop scheduler players first _ execution halt,
          app.runUntil_of_stop scheduler players second _ execution
            ((agree execution holds).mp halt)]
      · have running : ¬ second execution := fun stopped =>
          halt ((agree execution holds).mpr stopped)
        simp only [runUntil, halt, running, ↓reduceIte]
        apply bind_congr_on_support _
        intro next reached
        exact ih next (preserved execution holds halt next reached)

section RoundCongruence

variable {β : Type*}

/-- **Stopped runs from a round congruence.** Two profiles whose single rounds
have equal laws of a readout `ψ` from executions with equal readouts, under
per-side invariants that rounds keep and that determine when to stop, have
equal laws of `ψ` after any number of stopped rounds. The invariants are indexed
by the rounds still to run. -/
theorem runUntil_map_congr_of_rounds (scheduler : app.Scheduler)
    (first second : Principal → app.Policy) (stop : app.Execution → Prop) [DecidablePred stop]
    (ψ : app.Execution → β) (leftHolds rightHolds : Nat → app.Execution → Prop)
    (stops : ∀ n left right, leftHolds n left → rightHolds n right → ψ left = ψ right →
      (stop left ↔ stop right))
    (rounds : ∀ n left right, leftHolds (n + 1) left → rightHolds (n + 1) right →
      ψ left = ψ right → ¬ stop left →
      (app.round scheduler first left).map ψ = (app.round scheduler second right).map ψ)
    (leftStep : ∀ n left, leftHolds (n + 1) left → ¬ stop left →
      ∀ next ∈ (app.round scheduler first left).support, leftHolds n next)
    (rightStep : ∀ n right, rightHolds (n + 1) right → ¬ stop right →
      ∀ next ∈ (app.round scheduler second right).support, rightHolds n next) :
    ∀ count left right, leftHolds count left → rightHolds count right → ψ left = ψ right →
      (app.runUntil scheduler first stop count left).map ψ =
        (app.runUntil scheduler second stop count right).map ψ := by
  intro count
  induction count with
  | zero =>
      intro left right _ _ same
      simp only [ReactiveApplication.runUntil, PMF.pure_map]
      exact congrArg PMF.pure same
  | succ count ih =>
      intro left right leftValid rightValid same
      by_cases halted : stop left
      · have rightHalted := (stops _ left right leftValid rightValid same).mp halted
        rw [app.runUntil_of_stop scheduler first stop _ left halted,
          app.runUntil_of_stop scheduler second stop _ right rightHalted, PMF.pure_map,
          PMF.pure_map]
        exact congrArg PMF.pure same
      · have rightRunning : ¬ stop right := fun rightHalted =>
          halted ((stops _ left right leftValid rightValid same).mpr rightHalted)
        simp only [ReactiveApplication.runUntil, halted, rightRunning, ↓reduceIte, PMF.map_bind]
        apply bind_eq_of_map_eq _ _ _ _ (rounds count left right leftValid rightValid same halted)
        intro next nextReached other otherReached equal
        exact ih next other (leftStep count left leftValid halted next nextReached)
          (rightStep count right rightValid rightRunning other otherReached) equal


end RoundCongruence

end Interaction.ReactiveApplication
