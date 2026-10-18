/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastAudit
import Vegas.Examples.CommitSeedBroadcastRealization
import Interaction.ReactiveAnchoredMixture

/-! # Original supported seeds on every genuine menu decision -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Every genuine menu prefix is the same complete physical execution
under an original scheduler seed and the same response menu. Anchored responses
retain the recorded preparations and evidence, including at off-path sites. -/
theorem menu_trace_fixed_seed (menu : app.ResponseMenu)
    (silence : ∀ owner past view, (⟨none⟩ : app.Action) ∈ menu.actions owner past view)
    (current : app.Control)
    (trace : (menu.protocol initial horizon scheduler).Trace (some current)) :
    ∃ seed, Nonempty
      ((menu.protocol initial horizon (family seed)).Trace (some current)) := by
  rcases current with ⟨remaining, active, execution⟩
  obtain ⟨seed, _supported, ⟨original⟩⟩ := raw_trace_fixed_seed ⟨remaining, active, execution⟩
    (menu.toRawTrace initial horizon scheduler trace)
  let fallback : Player → app.Policy := fun _ => app.silentPolicy
  let players := ReactiveApplication.anchoredPolicy execution fallback
  have covered (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
      (action : app.Action) (supported : action ∈ (players who past view).support) :
      action ∈ menu.actions who past view := by
    apply menu.anchoredPolicy_covered initial horizon scheduler
      ⟨remaining, active, execution⟩ trace fallback who _ past view action supported
    intro earlier observed response selected
    change response ∈ (app.silentPolicy earlier observed).support at selected
    cases app.mem_silentPolicy_support.mp selected
    exact silence who earlier observed
  have actual := ReactiveApplication.anchored_of_trace initial horizon (family seed) execution
    fallback original ⟨remaining, active, execution⟩ rfl (fun _ => List.prefix_refl _)
  refine ⟨seed, ?_⟩
  cases active with
  | none =>
      have bounded := actual.1
      change remaining ≤ horizon at bounded
      obtain ⟨fixed⟩ := menu.trace_roundsFrom initial horizon (family seed) players
        covered (horizon - remaining) (by omega) execution actual.2
      have distance : horizon - (horizon - remaining) = remaining := by omega
      rw [distance] at fixed
      exact ⟨fixed⟩
  | some owner =>
      obtain ⟨bounded, strict, before, beforeSupport, command, selected, actor, moved⟩ := actual
      change remaining ≤ horizon at bounded
      change remaining < horizon at strict
      obtain ⟨beforeTrace⟩ := menu.trace_roundsFrom initial horizon (family seed) players
        covered (horizon - remaining - 1) (by omega) before beforeSupport
      have distance : horizon - (horizon - remaining - 1) = remaining + 1 := by omega
      rw [distance] at beforeTrace
      obtain ⟨fixed⟩ := menu.trace_environment initial horizon (family seed) remaining
        before execution command beforeTrace selected moved
      rw [actor] at fixed
      exact ⟨fixed⟩

end Vegas.Examples.CommitSeedBroadcast
