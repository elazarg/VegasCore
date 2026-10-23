/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveResponseMenu
import Interaction.ReactiveRecallInvariant
import Interaction.ReactiveRecovery
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Actual legal origins of remembered responses -/

noncomputable section

namespace Interaction.ReactiveApplication

/-- A response appends its actual view, action and emitted envelope to own recall. -/
theorem respond_recall_entry {Principal : Type} [DecidableEq Principal]
    (app : ReactiveApplication Principal) (execution : app.Execution) (owner : Principal)
    (action : app.Action) :
    ∃ emitted, (execution.respond app owner action).recall owner =
      execution.recall owner ++ [⟨execution.observe app owner, action, emitted⟩] := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact ⟨none, by simp only [Execution.respond, ↓reduceIte]⟩
  | some material =>
      exact ⟨some (execution.network.submit owner
        (app.packet (app.submit execution.application owner material) owner
          (execution.network.known owner) material)).1, by
            simp only [Execution.respond, ↓reduceIte]⟩

end Interaction.ReactiveApplication

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu)

/-- A specified occurrence in the chronological recall retains its exact
earlier active callback. Equal silent entries cause no ambiguity: the supplied
list split identifies the occurrence, and its whole prior recall is recovered. -/
theorem recorded_response_at
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : (menu.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) (earlier : List app.PlayerEntry) (entry : app.PlayerEntry)
    (later : List app.PlayerEntry)
    (recalled : control.execution.recall who = earlier ++ entry :: later) :
    ∃ (before : app.Control)
      (prior : (menu.protocol initial horizon scheduler).Trace (some before)),
      TracePrefix prior trace ∧ before.actor = some who ∧
      before.execution.recall who = earlier ∧
      entry.beforeView = before.execution.observe app who ∧
      entry.action ∈ menu.actions who earlier (before.execution.observe app who) := by
  have origin : ∀ {state} (_history : (menu.protocol initial horizon scheduler).Trace state),
      state.elim True (fun current => ∀ who earlier entry later,
        current.execution.recall who = earlier ++ entry :: later →
        ∃ (before : app.Control)
          (prior : (menu.protocol initial horizon scheduler).Trace (some before)),
          TracePrefix prior _history ∧ before.actor = some who ∧
          before.execution.recall who = earlier ∧
          entry.beforeView = before.execution.observe app who ∧
          entry.action ∈ menu.actions who earlier (before.execution.observe app who)) := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint legal reached ih =>
        change target ∈ (app.transition initial horizon scheduler source joint).support at reached
        cases source with
        | none =>
            obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
            intro who earlier entry later recalled
            simp only [Execution.initial] at recalled
            have impossible : entry ∈ ([] : List app.PlayerEntry) := by
              rw [recalled]
              exact List.mem_append_right earlier List.mem_cons_self
            exact (List.not_mem_nil impossible).elim
        | some current =>
            rcases current with ⟨remaining, actor, execution⟩
            cases actor with
            | some acting =>
                have localLegal := legal.2 acting
                obtain ⟨action, chosen, permitted⟩ : ∃ action, joint acting = some action ∧
                    action ∈ menu.actions acting (execution.recall acting)
                      (execution.observe app acting) := by
                  cases chosen : joint acting with
                  | none =>
                      rw [chosen] at localLegal
                      exact False.elim (localLegal rfl)
                  | some action =>
                      rw [chosen] at localLegal
                      exact ⟨action, rfl, localLegal.2⟩
                cases (PMF.mem_support_pure_iff _ _).mp reached
                intro who earlier entry later recalled
                simp only [chosen, Option.getD_some] at recalled ⊢
                by_cases same : who = acting
                · subst who
                  obtain ⟨emitted, actual⟩ := app.respond_recall_entry execution acting action
                  rw [actual] at recalled
                  cases later using List.reverseRecOn with
                  | nil =>
                      have lengths := congrArg List.length recalled
                      have sameLength : (execution.recall acting).length = earlier.length := by
                        simp only [List.length_append, List.length_cons, List.length_nil] at lengths
                        omega
                      have splitEq := List.append_inj recalled sameLength
                      have lastEq := List.singleton_inj.mp splitEq.2
                      subst entry
                      refine ⟨⟨remaining, some acting, execution⟩, prior,
                        .extend .refl joint legal reached, rfl, splitEq.1, rfl, ?_⟩
                      rwa [splitEq.1] at permitted
                  | append_singleton middle last =>
                      have equal : execution.recall acting ++
                          [⟨execution.observe app acting, action, emitted⟩] =
                            (earlier ++ entry :: middle) ++ [last] := by
                        simpa only [List.append_assoc, List.cons_append] using recalled
                      have lengths := congrArg List.length equal
                      have sameLength : (execution.recall acting).length =
                          (earlier ++ entry :: middle).length := by
                        simp only [List.length_append, List.length_singleton] at lengths
                        simpa only [List.length_append] using Nat.add_right_cancel lengths
                      have previous := (List.append_inj equal sameLength).1
                      obtain ⟨before, history, isPrefix, active, pastEq, viewed, allowed⟩ :=
                        ih acting earlier entry middle previous
                      exact ⟨before, history, .extend isPrefix joint legal reached, active,
                        pastEq, viewed, allowed⟩
                · rw [app.respond_recall_other execution acting who same action] at recalled
                  obtain ⟨before, history, isPrefix, active, pastEq, viewed, allowed⟩ :=
                    ih who earlier entry later recalled
                  exact ⟨before, history, .extend isPrefix joint legal reached, active,
                    pastEq, viewed, allowed⟩
            | none =>
                cases remaining with
                | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
                | succ remaining =>
                    obtain ⟨command, _, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                    intro who earlier entry later recalled
                    rw [app.environmentStep_recall execution next command supported] at recalled
                    obtain ⟨before, history, isPrefix, active, pastEq, viewed, allowed⟩ :=
                      ih who earlier entry later recalled
                    exact ⟨before, history, .extend isPrefix joint legal reached, active,
                      pastEq, viewed, allowed⟩
  exact origin trace who earlier entry later recalled

/-- Every remembered response retains its actual earlier active menu history,
pre-response observation, complete prior own recall and menu legality. -/
theorem recorded_response_prefix
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : (menu.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) (entry : app.PlayerEntry) (recorded : entry ∈ control.execution.recall who) :
    ∃ (before : app.Control)
      (prior : (menu.protocol initial horizon scheduler).Trace (some before)),
      TracePrefix prior trace ∧
      before.actor = some who ∧ entry.beforeView = before.execution.observe app who ∧
      entry.action ∈ menu.actions who (before.execution.recall who)
        (before.execution.observe app who) ∧
      ∃ after, control.execution.recall who = before.execution.recall who ++ entry :: after := by
  obtain ⟨earlier, later, recalled⟩ := List.mem_iff_append.mp recorded
  obtain ⟨before, prior, isPrefix, active, pastEq, viewed, allowed⟩ :=
    menu.recorded_response_at initial horizon scheduler control trace who earlier entry later
      recalled
  refine ⟨before, prior, isPrefix, active, viewed, ?_, later, ?_⟩
  · rwa [pastEq]
  · rwa [pastEq]

end Interaction.ReactiveApplication.ResponseMenu

end
