/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAnchoredTrace
import Interaction.ReactiveMixtureRounds
import Interaction.ReactiveRecallEntries

/-! # Original private priors at authentic reactive entry executions -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}

omit [DecidableEq Principal] in
/-- Anchoring supports the entire recorded own past, including responses
outside the support of the continuing policy. No source-origin claim is made. -/
theorem anchoredPolicy_consistent (anchor : app.Execution)
    (players : Principal → app.Policy) (who : Principal) :
    (anchoredPolicy anchor players who).Consistent (anchor.recall who) := by
  have prefixConsistent (past : List app.PlayerEntry) (within : past <+: anchor.recall who) :
      (anchoredPolicy anchor players who).Consistent past := by
    induction past using List.reverseRecOn with
    | nil => exact .nil
    | append_singleton past entry ih =>
        apply Policy.Consistent.snoc entry
        · exact ih ((List.prefix_append _ _).trans within)
        · rw [anchoredPolicy_of_recorded anchor players who past entry within]
          exact (PMF.mem_support_pure_iff _ _).mpr rfl
  exact prefixConsistent _ (List.prefix_refl _)

/-- The existing stopped runner preserves the exact continuing execution law
after an authentic anchor; network and all environment/player recall remain. -/
theorem runUntil_anchoredPolicy_of_extends (scheduler : app.Scheduler)
    (anchor : app.Execution) (players : Principal → app.Policy)
    (stop : app.Execution → Prop) [DecidablePred stop] (count : Nat)
    (execution : app.Execution) (extends_ : ∀ who, anchor.recall who <+: execution.recall who) :
    app.runUntil scheduler (anchoredPolicy anchor players) stop count execution =
      app.runUntil scheduler players stop count execution := by
  let invariant : app.Execution → Prop := fun current =>
    ∀ who, anchor.recall who <+: current.recall who
  have preserved : app.PolicyInvariant (anchoredPolicy anchor players) invariant := by
    constructor
    · intro current responder action valid _ who
      exact (valid who).trans (app.respond_recall_prefix current responder who action)
    · intro current next command valid moved who
      rw [app.environmentStep_recall current next command moved]
      exact valid who
  apply app.runUntil_congr_of_agree scheduler (anchoredPolicy anchor players) players stop
    invariant ?_ ?_ count execution extends_
  · intro current valid _ command _ middle moved who _
    apply anchoredPolicy_of_extends
    rw [app.environmentStep_recall current middle command moved]
    exact valid who
  · intro current valid _ next reached
    obtain ⟨command, _selected, moved⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
    exact preserved.dispatch command current next valid moved

namespace ResponseMenu

variable (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat)
  (scheduler : app.Scheduler)

/-- An actual counted entry gives global legality of anchored policies: old
responses were legal at their exact recorded inputs; all future responses are
covered by the continuing policy. Raw evidence/preparation aliases are retained. -/
theorem anchoredPolicy_covered (control : app.Control)
    (trace : (menu.protocol initial horizon scheduler).Trace (some control))
    (players : Principal → app.Policy) (who : Principal)
    (covered : ∀ past view action, action ∈ (players who past view).support →
      action ∈ menu.actions who past view) :
    ∀ past view action,
      action ∈ (anchoredPolicy control.execution players who past view).support →
        action ∈ menu.actions who past view := by
  classical
  intro past view action supported
  unfold anchoredPolicy at supported
  cases found : (control.execution.recall who)[past.length]? with
  | none =>
      rw [found] at supported
      exact covered past view action supported
  | some entry =>
      simp only [found] at supported
      by_cases recorded : past ++ [entry] <+: control.execution.recall who ∧
          entry.beforeView = view
      · rw [ite_eq_left recorded] at supported
        have same := (PMF.mem_support_pure_iff _ _).mp supported
        subst action
        obtain ⟨rest, recalled⟩ := recorded.1
        have recalled' : control.execution.recall who = past ++ entry :: rest := by
          simpa only [List.append_assoc, List.singleton_append] using recalled.symm
        have inside : past.length < (control.execution.recall who).length := by
          rw [recalled']
          simp only [List.length_append, List.length_cons]
          omega
        have taken : (control.execution.recall who).take past.length = past := by
          rw [recalled', List.take_append_of_le_length (Nat.le_refl _), List.take_length]
        have selected : (control.execution.recall who)[past.length] = entry := by
          simp only [recalled', List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
            List.getElem_cons_zero]
        have member := app.recallOwnPlay_entry_mem (control.execution.recall who) past.length
          inside
        rw [taken, selected] at member
        have ownEq : (menu.information initial horizon scheduler).ownPlay who trace =
            app.recallOwnPlay (control.execution.recall who) := by
          calc
            _ = (app.signals initial horizon scheduler).ownPlay who
                (menu.toRawTrace initial horizon scheduler trace) :=
              (menu.ownPlay_toRawTrace initial horizon scheduler who trace).symm
            _ = _ := app.trace_ownPlay initial horizon scheduler who _
        rw [← ownEq] at member
        obtain ⟨chosen, legal, same⟩ :=
          (menu.information initial horizon scheduler).ownPlay_mem_menu who trace member
        cases Option.some.inj same
        rw [← recorded.2]
        exact legal
      · rw [ite_eq_right recorded] at supported
        exact covered past view action supported

end ResponseMenu
end Interaction.ReactiveApplication
