/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingCountedContinuation
import Interaction.ReactiveAnchoredMixture

/-! # Original supported seeds on every genuine counted decision -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player)

/-- Every genuine counted prefix is the same complete physical execution
under an original scheduler seed and the same counted menu. Anchored responses
retain the recorded preparations and evidence, including at off-path sites. -/
theorem counted_trace_fixed_seed (current : app.Control)
    (trace : countedProtocol.Trace (some current)) :
    ∃ seed, Nonempty
      ((countedMenu.protocol initial horizon (family seed)).Trace (some current)) := by
  rcases current with ⟨remaining, active, execution⟩
  obtain ⟨seed, ⟨original⟩⟩ := fixed_seed_decision ⟨remaining, active, execution⟩
    (countedMenu.toRawTrace initial horizon scheduler trace)
  let fallback : Player → app.Policy := fun _ => app.silentPolicy
  let players := ReactiveApplication.anchoredPolicy execution fallback
  have covered (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
      (action : app.Action) (supported : action ∈ (players who past view).support) :
      action ∈ countedMenu.actions who past view := by
    apply countedMenu.anchoredPolicy_covered initial horizon scheduler
      ⟨remaining, active, execution⟩ trace fallback who _ past view action supported
    intro earlier observed response selected
    change response ∈ (app.silentPolicy earlier observed).support at selected
    cases app.mem_silentPolicy_support.mp selected
    exact PhaseCount.silence_onePacket runtime leaks bounds who earlier observed
  have actual := ReactiveApplication.anchored_of_trace initial horizon (family seed) execution
    fallback original ⟨remaining, active, execution⟩ rfl (fun _ => List.prefix_refl _)
  refine ⟨seed, ?_⟩
  cases active with
  | none =>
      have bounded := actual.1
      change remaining ≤ horizon at bounded
      obtain ⟨fixed⟩ := countedMenu.trace_roundsFrom initial horizon (family seed) players
        covered (horizon - remaining) (by omega) execution actual.2
      have distance : horizon - (horizon - remaining) = remaining := by omega
      rw [distance] at fixed
      exact ⟨fixed⟩
  | some owner =>
      obtain ⟨bounded, strict, before, beforeSupport, command, selected, actor, moved⟩ := actual
      change remaining ≤ horizon at bounded
      change remaining < horizon at strict
      obtain ⟨beforeTrace⟩ := countedMenu.trace_roundsFrom initial horizon (family seed) players
        covered (horizon - remaining - 1) (by omega) before beforeSupport
      have distance : horizon - (horizon - remaining - 1) = remaining + 1 := by omega
      rw [distance] at beforeTrace
      obtain ⟨fixed⟩ := countedMenu.trace_environment initial horizon (family seed) remaining
        before execution command beforeTrace selected moved
      rw [actor] at fixed
      exact ⟨fixed⟩

end Vegas.Examples.CommitSeedSignalling
