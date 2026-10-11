/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCompletion
import Interaction.ReactiveRawRoundTrace

/-! # Completion boundaries for arbitrary raw continuations -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A completing actual service advances one source event from an initialized
boundary under arbitrary players, without a finite-menu or equilibrium premise. -/
theorem raw_completion_boundary
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (event : (graph setup).EventId)
    (execution stopped : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).support) :
    stopped.environmentRecall.length ≤ horizon ∧
      CompletionBoundary setup leaks scheduler players (event.val + 1) stopped := by
  let app := application setup leaks
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
  have seen : ReadySeen setup leaks event.val execution := by
    intro who entry member query ready
    by_contra greater
    exact boundary.untouched query (by omega) who entry member ready
  obtain ⟨seenLater, prefixLater⟩ := runUntil_completion_prefix setup leaks scheduler players event
    (horizon - execution.environmentRecall.length) execution stopped boundary.ordered seen reached
  obtain ⟨used, within, _, length⟩ := app.runUntil_runRounds scheduler players stop
    (horizon - execution.environmentRecall.length) execution stopped reached
  have stoppedBounded : stopped.environmentRecall.length ≤ horizon := by omega
  have supported := app.roundsFrom_runUntil scheduler players (initialLaw setup) stop
    (horizon - execution.environmentRecall.length) execution stopped boundary.supported reached
  have ordered : stopped.application.config.cut.IsPrefix (event.val + 1) := by
    rcases prefixLater with current | advanced
    · exfalso
      have unfinished : event ∉ stopped.application.config.cut.completed := fun member =>
        Nat.lt_irrefl _ ((current.2 event).mp member)
      rcases app.runUntilHorizon_stopped scheduler players stop horizon
          (horizon - execution.environmentRecall.length) execution stopped
          (by omega) reached with finished | spent
      · exact unfinished finished
      · obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
          stopped.environmentRecall.length stoppedBounded stopped supported
        have terminal := completes _ trace (by
          change horizon - stopped.environmentRecall.length = 0 ∧ _
          exact ⟨by omega, rfl⟩)
        change stopped.application.config.cut.completed = Finset.univ at terminal
        exact unfinished (terminal ▸ Finset.mem_univ _)
    · exact advanced
  refine ⟨stoppedBounded, supported, ordered, ?_⟩
  intro next rankNext observer entry member readyView
  have := seenLater observer entry member next readyView
  omega

end Vegas
