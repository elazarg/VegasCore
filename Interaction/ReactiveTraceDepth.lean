/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveHistory

/-! # Exact history length from completed interaction

Initialization contributes one step. Each scheduler command and each player
response contributes one further step, counted in their respective recalls.
The identity does not assume that histories have positive equilibrium weight.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  (app : ReactiveApplication Principal)

def interactionDepth : app.ProtocolState → Nat
  | none => 0
  | some control => 1 + control.execution.environmentRecall.length +
      ∑ who, (control.execution.recall who).length

theorem respond_total_recall (execution : app.Execution) (who : Principal)
    (action : app.Action) :
    (∑ observer, ((execution.respond app who action).recall observer).length) =
      (∑ observer, (execution.recall observer).length) + 1 := by
  have each (observer : Principal) :
      ((execution.respond app who action).recall observer).length =
        (execution.recall observer).length + if observer = who then 1 else 0 := by
    by_cases same : observer = who
    · subst observer
      have count := congrArg List.length (app.respond_actions execution who action)
      simpa only [List.length_map, List.length_append, List.length_singleton, ↓reduceIte]
        using count
    · rw [app.respond_recall_other execution who observer same action]
      simp only [same, ↓reduceIte, Nat.add_zero]
  simp_rw [each]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem interactionDepth_transition (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (before after : app.ProtocolState)
    (joint : Principal → Option app.Action) (running : ¬ app.terminal before)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    app.interactionDepth after = app.interactionDepth before + 1 := by
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ reached
      simp [interactionDepth, Execution.initial]
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases FinDist.mem_support_pure.mp reached
          simp only [interactionDepth, app.respond_environmentRecall, app.respond_total_recall]
          omega
      | none =>
          cases remaining with
          | zero => exact (running ⟨rfl, rfl⟩).elim
          | succ remaining =>
              obtain ⟨command, _, supported⟩ :=
                Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := FinDist.support_map .. ▸ supported
              have recalls := app.environmentStep_recall execution next command moved
              have schedulerRecall : next.environmentRecall.length =
                  execution.environmentRecall.length + 1 := by
                obtain ⟨updated, _, rfl⟩ := FinDist.support_map .. ▸ moved
                simp only [List.length_append, List.length_singleton]
              simp only [interactionDepth, recalls, schedulerRecall]
              omega

theorem trace_interactionDepth (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) :
    ∀ {state} (trace : (app.protocol initial horizon scheduler).Trace state),
      trace.length = app.interactionDepth state
  | _, .start => rfl
  | _, .extend prior joint legal reached => by
      rw [Trace.length, app.interactionDepth_transition initial horizon scheduler _ _ joint
        legal.1 reached, trace_interactionDepth initial horizon scheduler prior]

theorem trace_length_of_control (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control)) :
    trace.length = 1 + control.execution.environmentRecall.length +
      ∑ who, (control.execution.recall who).length :=
  app.trace_interactionDepth initial horizon scheduler trace

end Interaction.ReactiveApplication
