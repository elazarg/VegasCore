/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveSafety
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveRecallInvariant

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Actual application operations never move the public clock backwards. -/
theorem reactiveClockLowerBoundInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (lower : Nat) :
    (runtime.reactiveApplication leaks).Invariant (fun state => lower ≤ state.clock) := by
  let app := runtime.reactiveApplication leaks
  constructor
  · intro state who material bounded
    have same := (runtime.reactive_respond_application leaks (.initial app state) who
      ⟨some material⟩).2
    have clock := congrArg PublicView.clock same
    change (app.submit state who material).clock = state.clock at clock
    rwa [clock]
  · intro state message next bounded accepted
    rw [(handle_clock_activated runtime state next ⟨message.id, message.payload.call⟩
      (reactiveHandle_call accepted)).1]
    exact bounded
  · intro state command next bounded reached
    cases command with
    | advanceClock =>
        change next ∈ (PMF.pure { state with clock := state.clock + 1 }).support at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact Nat.le_succ_of_le bounded
    | executeSample event =>
        rw [(environmentStep_executeSample_config_activated runtime state next event reached).1]
        exact bounded
    | expire event =>
        rw [(environmentStep_expire_config_activated runtime state next event reached).1]
        exact bounded

/-- Raw own recall is chronological, and every recorded clock is at most current time. -/
def ChronologicalRecall (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  ReactiveApplication.Execution.RecallBound (runtime.reactiveApplication leaks)
    (fun view => view.publicView.clock) (fun state => state.clock) execution ∧
  ∀ who, (execution.recall who).Pairwise
    (fun earlier later => earlier.beforeView.application.publicView.clock ≤
      later.beforeView.application.publicView.clock)

/-- Actual monotone clock operations establish all original own-response chronology. -/
theorem chronologicalRecallInvariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (runtime.ChronologicalRecall leaks) := by
  let app := runtime.reactiveApplication leaks
  have bound := app.recallBoundInvariant (fun view => view.publicView.clock)
    (fun state => state.clock) (fun _ _ => rfl)
      (runtime.reactiveClockLowerBoundInvariant leaks) scheduler
  constructor
  · intro execution who action valid
    refine ⟨bound.respond execution who action valid.1, ?_⟩
    intro observer
    by_cases same : observer = who
    · subst observer
      obtain ⟨entry, recalled, viewed⟩ : ∃ entry,
          (execution.respond app who action).recall who = execution.recall who ++ [entry] ∧
          entry.beforeView = execution.observe app who := by
        rcases action with ⟨transmission⟩
        cases transmission with
        | none =>
            exact ⟨⟨execution.observe app who, ⟨none⟩, none⟩,
              by simp only [ReactiveApplication.Execution.respond, ↓reduceIte], rfl⟩
        | some material =>
            exact ⟨⟨execution.observe app who, ⟨some material⟩,
              some (execution.network.submit who
                (app.packet (app.submit execution.application who material) who
                  (execution.network.known who) material)).1⟩,
                by simp only [ReactiveApplication.Execution.respond, ↓reduceIte], rfl⟩
      rw [recalled]
      apply List.pairwise_append.mpr
      refine ⟨valid.2 who, List.pairwise_singleton _ entry, ?_⟩
      intro earlier retained later member
      have equal := List.mem_singleton.mp member
      subst later
      rw [viewed]
      exact valid.1 who earlier retained
    · rw [app.respond_recall_other execution who observer same action]
      exact valid.2 observer
  · intro execution next command valid selected reached
    refine ⟨bound.environment execution next command valid.1 selected reached, ?_⟩
    intro who
    rw [app.environmentStep_recall execution next command reached]
    exact valid.2 who

/-- Every actual initialized legal trace has ordered original response clocks. -/
theorem chronologicalRecall_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) : runtime.ChronologicalRecall leaks control.execution := by
  exact (runtime.chronologicalRecallInvariant leaks scheduler).history initial horizon
    (fun _ _ => ⟨fun _ _ member => False.elim (List.not_mem_nil member),
      fun _ => List.Pairwise.nil⟩) trace

end Vegas.EventGraphRuntime
