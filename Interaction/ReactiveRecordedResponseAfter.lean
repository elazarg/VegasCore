/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveRecordedResponse

/-! # Exact postresponse prefixes of remembered chronological entries -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu)

/-- A specified remembered occurrence retains its actual response transition,
including the literal postresponse trace and its prefix of the final history. -/
theorem recorded_response_after
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (final : app.Control)
    (trace : (menu.protocol initial horizon scheduler).Trace (some final))
    (who : Principal) (earlier : List app.PlayerEntry) (entry : app.PlayerEntry)
    (later : List app.PlayerEntry)
    (recalled : final.execution.recall who = earlier ++ entry :: later) :
    ∃ (remaining : Nat) (execution : app.Execution)
      (prior : (menu.protocol initial horizon scheduler).Trace
        (some ⟨remaining, some who, execution⟩))
      (postTrace : (menu.protocol initial horizon scheduler).Trace
        (some ⟨remaining, none, execution.respond app who entry.action⟩)),
      TracePrefix postTrace trace ∧ execution.recall who = earlier ∧
        entry.beforeView = execution.observe app who ∧
        entry.action ∈ menu.actions who (execution.recall who)
          (execution.observe app who) ∧
      TracePrefix prior postTrace ∧ postTrace.length = prior.length + 1 := by
  obtain ⟨before, prior, kept, acting, past, viewed, permitted⟩ :=
    menu.recorded_response_at initial horizon scheduler final trace who
      earlier entry later recalled
  rcases before with ⟨remaining, actor, execution⟩
  cases acting
  rw [← past] at permitted
  have path := kept.reachesWithin
  rcases path.eq_or_step with equal | ⟨joint, legal, reached, supported, _fuel, suffix⟩
  · have same : (⟨remaining, some who, execution⟩ : app.Control) = final :=
      Option.some.inj (congrArg History.state equal)
    cases same
    have lengths := congrArg List.length recalled
    rw [past, List.length_append, List.length_cons] at lengths
    omega
  · have moved : reached ∈ (app.transition initial horizon scheduler
        (some ⟨remaining, some who, execution⟩) joint).support := supported
    cases (PMF.mem_support_pure_iff _ _).mp moved
    let action : app.Action := (joint who).getD ⟨none⟩
    obtain ⟨emitted, ownRecall⟩ := app.respond_recall_entry execution who action
    have retained := app.reaches_recall_prefix initial horizon scheduler
      (menu.reaches_raw initial horizon scheduler suffix)
      ⟨remaining, none, execution.respond app who action⟩ final rfl rfl who
    change (execution.respond app who action).recall who <+:
      final.execution.recall who at retained
    rw [ownRecall, past, recalled] at retained
    have first := (List.prefix_append_right_inj earlier).mp retained
    obtain ⟨_tail, heads, _emptyPrefix⟩ := List.cons_prefix_iff.mp first
    have same := (List.cons.inj heads).1.symm
    subst entry
    let postTrace : (menu.protocol initial horizon scheduler).Trace
        (some ⟨remaining, none, execution.respond app who action⟩) :=
      prior.extend joint legal supported
    have postKept : TracePrefix postTrace trace := by
      simpa only [postTrace, History.extend] using suffix.tracePrefix
    exact ⟨remaining, execution, prior, postTrace, postKept, past, viewed, permitted,
      .extend .refl joint legal supported, rfl⟩

end Interaction.ReactiveApplication.ResponseMenu
