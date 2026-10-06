/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePolicyMixture
import Interaction.ReactiveStopping
import Interaction.ReactiveRawRoundTrace

/-! # Policy mixtures and profile agreement through scheduler rounds

A behavioral mixture of response policies, realized from actual own recall,
runs as the mixture of the runs of its members, drawn from the posterior on the
current recall. This holds for complete rounds and for rounds stopped at a
predicate, under every scheduler. Two profiles that agree at every input
actually queried before stopping give the same stopped run.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)
  {Index : Type}

private theorem resume_policyMixture {Result : Type} (initial : PMF Index)
    (policies : Index → app.Policy) (who : Principal) (players : Principal → app.Policy)
    (rest : (Principal → app.Policy) → app.Execution → PMF Result)
    (restMixture : ∀ current : app.Execution,
      ((app.policyMixture initial policies).posterior (current.recall who)).bind
          (fun index => rest (Function.update players who (policies index)) current) =
        rest (Function.update players who (app.policyMixture initial policies).policy) current)
    (current : app.Execution) (actor : Option Principal) :
    ((app.policyMixture initial policies).posterior (current.recall who)).bind (fun index =>
      (app.resume (Function.update players who (policies index)) actor current).bind
        (rest (Function.update players who (policies index)))) =
      (app.resume (Function.update players who (app.policyMixture initial policies).policy)
        actor current).bind
          (rest (Function.update players who (app.policyMixture initial policies).policy)) := by
  let mixture := app.policyMixture initial policies
  cases actor with
  | none => simpa only [resume, PMF.pure_bind] using restMixture current
  | some owner =>
      by_cases same : owner = who
      · subst owner
        have split := mixture.response_disintegrate current who (fun next index =>
          rest (Function.update players who (policies index)) next)
        simp only [mixture, policyMixture, PMF.bind_map] at split
        simp only [resume, invoke, Function.update_self, PMF.bind_map]
        refine split.trans ?_
        apply bind_congr_on_support _
        intro action _
        exact restMixture _
      · simp only [resume, invoke, Function.update_of_ne same, PMF.bind_map]
        rw [PMF.bind_comm]
        apply bind_congr_on_support _
        intro action _
        rw [← app.respond_recall_other current owner who (Ne.symm same) action]
        exact restMixture _

private theorem round_policyMixture {Result : Type} (scheduler : app.Scheduler)
    (initial : PMF Index) (policies : Index → app.Policy) (who : Principal)
    (players : Principal → app.Policy)
    (rest : (Principal → app.Policy) → app.Execution → PMF Result)
    (restMixture : ∀ current : app.Execution,
      ((app.policyMixture initial policies).posterior (current.recall who)).bind
          (fun index => rest (Function.update players who (policies index)) current) =
        rest (Function.update players who (app.policyMixture initial policies).policy) current)
    (execution : app.Execution) :
    ((app.policyMixture initial policies).posterior (execution.recall who)).bind (fun index =>
      (app.round scheduler (Function.update players who (policies index)) execution).bind
        (rest (Function.update players who (policies index)))) =
      (app.round scheduler (Function.update players who (app.policyMixture initial policies).policy)
        execution).bind
          (rest (Function.update players who (app.policyMixture initial policies).policy)) := by
  simp only [round, dispatch, PMF.bind_bind]
  rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro command _
  rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro current reached
  rw [← app.environmentStep_recall execution current command reached]
  exact app.resume_policyMixture initial policies who players rest restMixture current
    (command.actor? app)

/-- A behavioral mixture runs as the posterior mixture of its members' runs. -/
theorem runRounds_policyMixture (scheduler : app.Scheduler) (initial : PMF Index)
    (policies : Index → app.Policy) (who : Principal) (players : Principal → app.Policy)
    (count : Nat) (execution : app.Execution) :
    ((app.policyMixture initial policies).posterior (execution.recall who)).bind
        (fun index => app.runRounds scheduler (Function.update players who (policies index))
          count execution) =
      app.runRounds scheduler
        (Function.update players who (app.policyMixture initial policies).policy) count
          execution := by
  induction count generalizing execution with
  | zero => simp only [runRounds, PMF.bind_const]
  | succ count ih =>
      exact app.round_policyMixture scheduler initial policies who players
        (fun profile => app.runRounds scheduler profile count) ih execution

/-- A behavioral mixture runs as the posterior mixture of its members' runs,
stopped at a predicate. -/
theorem runUntil_policyMixture (scheduler : app.Scheduler) (initial : PMF Index)
    (policies : Index → app.Policy) (who : Principal) (players : Principal → app.Policy)
    (stop : app.Execution → Prop) [DecidablePred stop] (count : Nat)
    (execution : app.Execution) :
    ((app.policyMixture initial policies).posterior (execution.recall who)).bind
        (fun index => app.runUntil scheduler (Function.update players who (policies index))
          stop count execution) =
      app.runUntil scheduler
        (Function.update players who (app.policyMixture initial policies).policy) stop count
          execution := by
  induction count generalizing execution with
  | zero => simp only [runUntil, PMF.bind_const]
  | succ count ih =>
      by_cases halt : stop execution
      · simp only [runUntil, halt, ↓reduceIte, PMF.bind_const]
      · simp only [runUntil, halt, ↓reduceIte]
        exact app.round_policyMixture scheduler initial policies who players
          (fun profile => app.runUntil scheduler profile stop count) ih execution

/-- Two profiles that agree at every input queried before stopping, along runs
that keep an invariant, give the same stopped run. -/
theorem runUntil_congr_of_agree (scheduler : app.Scheduler)
    (first second : Principal → app.Policy) (stop : app.Execution → Prop) [DecidablePred stop]
    (invariant : app.Execution → Prop)
    (agree : ∀ execution, invariant execution → ¬ stop execution →
      ∀ command ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment app)).support,
      ∀ middle ∈ (execution.environmentStep app command).support, ∀ who,
        command.actor? app = some who →
          first who (middle.recall who) (middle.observe app who) =
            second who (middle.recall who) (middle.observe app who))
    (preserved : ∀ execution, invariant execution → ¬ stop execution →
      ∀ next ∈ (app.round scheduler first execution).support, invariant next)
    (count : Nat) (execution : app.Execution) (holds : invariant execution) :
    app.runUntil scheduler first stop count execution =
      app.runUntil scheduler second stop count execution := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      by_cases halt : stop execution
      · simp only [runUntil, halt, ↓reduceIte]
      · simp only [runUntil, halt, ↓reduceIte, round, dispatch, PMF.bind_bind]
        apply bind_congr_on_support _
        intro command selected
        apply bind_congr_on_support _
        intro middle moved
        have sameResponse : app.resume first (command.actor? app) middle =
            app.resume second (command.actor? app) middle := by
          cases active : command.actor? app with
          | none => rfl
          | some who =>
              simp only [resume, invoke,
                agree execution holds halt command selected middle moved who active]
        rw [← sameResponse]
        apply bind_congr_on_support _
        intro next resumed
        apply ih next
        apply preserved execution holds halt next
        simp only [round, dispatch, PMF.support_bind, Set.mem_iUnion]
        exact ⟨command, selected, middle, moved, resumed⟩

/-- Two profiles that agree at every input queried before stopping along legal
raw histories, where an invariant holds, give the same stopped run from a legal
raw history with enough remaining scheduler decisions. -/
theorem runUntil_congr_of_agree_on_traces (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (first second : Principal → app.Policy)
    (stop : app.Execution → Prop) [DecidablePred stop] (invariant : app.Execution → Prop)
    (agree : ∀ remaining execution,
      (app.protocol initial horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩) →
      invariant execution → ¬ stop execution →
      ∀ command ∈ (scheduler execution.environmentRecall
        (execution.observeEnvironment app)).support,
      ∀ middle ∈ (execution.environmentStep app command).support, ∀ who,
        command.actor? app = some who →
          first who (middle.recall who) (middle.observe app who) =
            second who (middle.recall who) (middle.observe app who))
    (preserved : ∀ remaining execution,
      (app.protocol initial horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩) →
      invariant execution → ¬ stop execution →
      ∀ next ∈ (app.round scheduler first execution).support, invariant next) :
    ∀ (count remaining : Nat) (execution : app.Execution),
      (app.protocol initial horizon scheduler).Trace
        (some ⟨remaining + count, none, execution⟩) →
      invariant execution →
      app.runUntil scheduler first stop count execution =
        app.runUntil scheduler second stop count execution := by
  intro count
  induction count with
  | zero => intro _ _ _ _; rfl
  | succ count ih =>
      intro remaining execution trace holds
      by_cases halt : stop execution
      · simp only [runUntil, halt, ↓reduceIte]
      · have trace' : (app.protocol initial horizon scheduler).Trace
            (some ⟨(remaining + count) + 1, none, execution⟩) := by
          simpa only [Nat.add_assoc] using trace
        simp only [runUntil, halt, ↓reduceIte, round, dispatch, PMF.bind_bind]
        apply bind_congr_on_support _
        intro command selected
        apply bind_congr_on_support _
        intro middle moved
        have sameResponse : app.resume first (command.actor? app) middle =
            app.resume second (command.actor? app) middle := by
          cases active : command.actor? app with
          | none => rfl
          | some who =>
              simp only [resume, invoke,
                agree (remaining + count) execution trace' holds halt command selected middle
                  moved who active]
        rw [← sameResponse]
        apply bind_congr_on_support _
        intro next resumed
        have reached : next ∈ (app.round scheduler first execution).support := by
          simp only [round, dispatch, PMF.support_bind, Set.mem_iUnion]
          exact ⟨command, selected, middle, moved, resumed⟩
        obtain ⟨nextTrace⟩ := app.raw_trace_round initial horizon scheduler first
          (remaining + count) execution next trace' reached
        exact ih remaining next nextTrace
          (preserved (remaining + count) execution trace' holds halt next reached)

end Interaction.ReactiveApplication
