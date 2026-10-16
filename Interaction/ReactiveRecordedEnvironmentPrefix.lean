/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecordedRounds
import Interaction.ReactiveRoundTrace

/-! # Genuine idle prefixes at original recorded environment queries -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}

/-- Every original recorded environment entry has a genuine counted idle
prefix under the same initial law, horizon, scheduler and response menu. -/
theorem recorded_environment_prefix (menu : app.ResponseMenu)
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (remaining : Nat) (execution : app.Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace (some ⟨remaining, none, execution⟩))
    (before : List app.EnvironmentEntry) (entry : app.EnvironmentEntry)
    (after : List app.EnvironmentEntry)
    (recorded : execution.environmentRecall = before ++ entry :: after) :
    ∃ used prior, used ≤ horizon ∧
      Nonempty ((menu.protocol initial horizon scheduler).Trace
        (some ⟨horizon - used, none, prior⟩)) ∧
      prior ∈ (app.roundsFrom initial scheduler menu.uniformResponses used).support ∧
      prior.environmentRecall = before ∧ entry.beforeView = prior.observeEnvironment app := by
  have supported := menu.roundSupported_uniform initial horizon scheduler trace
  obtain ⟨state, stateSupported, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported.2)
  have recalled : execution.environmentRecall = (Execution.initial app state).environmentRecall ++
      before ++ entry :: after := by
    simpa only [Execution.initial, List.nil_append] using recorded
  obtain ⟨used, suffix, prior, middle, length, prefixReached, priorRecall, viewEq,
    _chosen, _dispatched, _future⟩ := app.runRounds_recorded_entry scheduler menu.uniformResponses
      execution.environmentRecall.length (Execution.initial app state) execution reached
        before entry after recalled
  have prefixSupported : prior ∈ (app.roundsFrom initial scheduler menu.uniformResponses
      used).support := by
    rw [roundsFrom, PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨state, stateSupported, prefixReached⟩
  have within : used ≤ horizon := by
    have total : execution.environmentRecall.length + remaining = horizon := supported.1
    omega
  have prefixTrace := menu.trace_roundsFrom initial horizon scheduler menu.uniformResponses
    (fun who past view action admitted =>
      (menu.uniformResponses_support who past view action).mp admitted)
    used within prior prefixSupported
  exact ⟨used, prior, within, prefixTrace, prefixSupported,
    by simpa only [Execution.initial, List.nil_append] using priorRecall, viewEq⟩

end Interaction.ReactiveApplication.ResponseMenu
