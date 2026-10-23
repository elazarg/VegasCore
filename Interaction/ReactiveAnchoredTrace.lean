/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAnchoredPolicy
import Interaction.ReactiveRoundReachability

/-! # Legal histories are reached by their own anchored replay

Every legal raw history, under any responses, is reached by rounds of the
anchored profile of any later execution whose recall extends its own: at a
scheduler boundary its execution is in the support of those rounds, and at an
activation it is one environment step after such an execution
(`Interaction.ReactiveApplication.anchored_of_trace`). In particular every
execution at a scheduler boundary of a legal history is reached by its own
anchored profile (`Interaction.ReactiveApplication.mem_roundsFrom_anchoredPolicy_of_trace`).
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}

private theorem respond_recall_self' (execution : app.Execution) (who : Principal)
    (action : app.Action) :
    ∃ emitted, (execution.respond app who action).recall who =
      execution.recall who ++ [⟨execution.observe app who, action, emitted⟩] := by
  rcases action with ⟨transmission⟩
  cases transmission <;> simp only [Execution.respond, ↓reduceIte] <;> exact ⟨_, rfl⟩

/-- **Legal histories are anchored rounds.** Along a legal raw history, every
state whose recall is below the anchor's is reached by the anchored profile: at
a scheduler boundary by its rounds, and at an activation one environment step
after them. -/
theorem anchored_of_trace (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (anchor : app.Execution) (players : Principal → app.Policy) :
    ∀ {state} (_ : (app.protocol initial horizon scheduler).Trace state)
      (control : app.Control), state = some control →
      (∀ who, control.execution.recall who <+: anchor.recall who) →
      control.remaining ≤ horizon ∧
      match control.actor with
      | none => control.execution ∈ (app.roundsFrom initial scheduler
          (anchoredPolicy anchor players) (horizon - control.remaining)).support
      | some who => control.remaining < horizon ∧ ∃ prior ∈ (app.roundsFrom initial scheduler
          (anchoredPolicy anchor players) (horizon - control.remaining - 1)).support,
          ∃ command ∈ (scheduler prior.environmentRecall
            (prior.observeEnvironment app)).support,
          command.actor? app = some who ∧
            control.execution ∈ (prior.environmentStep app command).support := by
  intro state trace
  induction trace with
  | start => intro _ initialized; cases initialized
  | @extend before after prior joint _ realized ih =>
      intro control current below
      subst current
      cases before with
      | none =>
          change some control ∈ (initial.map fun state =>
            some ⟨horizon, none, Execution.initial app state⟩).support at realized
          obtain ⟨state, stateMem, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          refine ⟨le_rfl, ?_⟩
          change Execution.initial app state ∈ (app.roundsFrom initial scheduler _
            (horizon - horizon)).support
          rw [Nat.sub_self]
          exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨state, stateMem,
            (PMF.mem_support_pure_iff _ _).mpr rfl⟩
      | some previous =>
          rcases previous with ⟨remaining, current, execution⟩
          cases current with
          | some who =>
              change some control ∈ (PMF.pure (some (⟨remaining, none,
                execution.respond app who ((joint who).getD ⟨none⟩)⟩ : app.Control))).support
                at realized
              cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp realized)
              obtain ⟨emitted, recalled⟩ := respond_recall_self' execution who
                ((joint who).getD ⟨none⟩)
              have priorBelow : ∀ player, execution.recall player <+: anchor.recall player := by
                intro player
                refine List.IsPrefix.trans ?_ (below player)
                by_cases same : player = who
                · subst same
                  change execution.recall player <+: (execution.respond app player _).recall player
                  rw [recalled]
                  exact List.prefix_append _ _
                · change execution.recall player <+: (execution.respond app who _).recall player
                  rw [app.respond_recall_other execution who player same]
              obtain ⟨within, inside, earlier, earlierMem, command, selected, active, moved⟩ :=
                ih _ rfl priorBelow
              have inside' : remaining < horizon := inside
              refine ⟨within, ?_⟩
              change execution.respond app who _ ∈ (app.roundsFrom initial scheduler _
                (horizon - remaining)).support
              rw [show horizon - remaining = (horizon - remaining - 1) + 1 by omega,
                roundsFrom_succ]
              refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨earlier, earlierMem, ?_⟩
              refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨command, selected, ?_⟩
              refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨execution, moved, ?_⟩
              rw [active]
              change _ ∈ ((anchoredPolicy anchor players who (execution.recall who)
                (execution.observe app who)).map (execution.respond app who)).support
              have recorded := below who
              change (execution.respond app who _).recall who <+: anchor.recall who at recorded
              rw [recalled] at recorded
              rw [anchoredPolicy_of_recorded anchor players who (execution.recall who)
                ⟨execution.observe app who, _, emitted⟩ recorded, PMF.pure_map]
              exact (PMF.mem_support_pure_iff _ _).mpr rfl
          | none =>
              cases remaining with
              | zero =>
                  change some control ∈ (PMF.pure (some (⟨0, none, execution⟩ :
                    app.Control))).support at realized
                  cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp realized)
                  exact ih _ rfl below
              | succ remaining =>
                  simp only [ReactiveApplication.protocol, ReactiveApplication.transition,
                    PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image,
                    exists_prop] at realized
                  obtain ⟨command, selected, middle, stepped, same⟩ := realized
                  cases Option.some.inj same
                  have recallEq := app.environmentStep_recall execution middle command stepped
                  have priorBelow : ∀ player, execution.recall player <+: anchor.recall player :=
                    fun player => by
                      have := below player
                      change middle.recall player <+: anchor.recall player at this
                      rwa [recallEq] at this
                  obtain ⟨within, reached⟩ := ih _ rfl priorBelow
                  change remaining + 1 ≤ horizon at within
                  change execution ∈ (app.roundsFrom initial scheduler _
                    (horizon - (remaining + 1))).support at reached
                  refine ⟨show remaining ≤ horizon by omega, ?_⟩
                  change match command.actor? app with
                    | none => middle ∈ (app.roundsFrom initial scheduler _
                        (horizon - remaining)).support
                    | some who => remaining < horizon ∧ ∃ prior ∈ (app.roundsFrom initial
                        scheduler _ (horizon - remaining - 1)).support, ∃ command ∈
                        (scheduler prior.environmentRecall
                          (prior.observeEnvironment app)).support,
                        command.actor? app = some who ∧
                          middle ∈ (prior.environmentStep app command).support
                  cases active : command.actor? app with
                  | none =>
                      rw [show horizon - remaining = (horizon - (remaining + 1)) + 1 by omega,
                        roundsFrom_succ]
                      refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨execution, reached, ?_⟩
                      refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨command, selected, ?_⟩
                      refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨middle, stepped, ?_⟩
                      rw [active]
                      exact (PMF.mem_support_pure_iff _ _).mpr rfl
                  | some who =>
                      refine ⟨by omega, execution, ?_, command, selected, active, stepped⟩
                      rw [show horizon - remaining - 1 = horizon - (remaining + 1) by omega]
                      exact reached

/-- **Boundary executions of legal histories are anchored rounds.** At a
scheduler boundary of a legal raw history, the execution is reached by the
rounds of its own anchored profile, whatever profile it continues with. -/
theorem mem_roundsFrom_anchoredPolicy_of_trace (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (players : Principal → app.Policy) {remaining : Nat}
    {execution : app.Execution}
    (trace : (app.protocol initial horizon scheduler).Trace (some ⟨remaining, none, execution⟩)) :
    remaining ≤ horizon ∧ execution ∈ (app.roundsFrom initial scheduler
      (anchoredPolicy execution players) (horizon - remaining)).support :=
  anchored_of_trace initial horizon scheduler execution players trace _ rfl
    (fun _ => List.prefix_refl _)

end Interaction.ReactiveApplication
