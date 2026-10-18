/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingTailBindingAcceptance
import Interaction.ReactiveRecordedResponseAfter

/-! # Resolved continuation binding success from actual retained declarations -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- A remembered counted declaration at a nonoriginal binding receives a true
receipt at every resolved endpoint of that same actual history. No delivery,
source-value, proper-preparation or callback-prefix premise is supplied. -/
theorem tail_recorded_binding_resolved_accepted (seeds : Seeds) (final : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace (some final))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (binding : graph.outputLayout coordinate.event = .binding owner .bool)
    (entry : app.PlayerEntry) (recorded : entry ∈ final.execution.recall owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)
    (material : WitnessedSubmission graph)
    (transmitted : entry.action.transmission = some material)
    (resolved : coordinate.Resolved final.execution.application) :
    PhaseService.BindingAccepted runtime leaks coordinate owner final.execution := by
  classical
  rcases entry with ⟨entryView, ⟨transmission⟩, emitted⟩
  change transmission = some material at transmitted
  subst transmission
  obtain ⟨earlier, later, recalled⟩ := List.mem_iff_append.mp recorded
  obtain ⟨remaining, execution, prior, postTrace, kept, _past, viewed, permitted⟩ :=
    countedMenu.recorded_response_after initial horizon (family seeds) final trace owner
      earlier ⟨entryView, ⟨some material⟩, emitted⟩ later recalled
  have valid := raw_native_valid (family seeds) _
    (countedMenu.toRawTrace initial horizon (family seeds) prior)
  rw [viewed] at requested
  have request := (execution.application.requests_publicView valid owner coordinate).mp requested
  have coordinateEq : coordinate = ⟨execution.application.attempt, coordinate.event⟩ := by
    cases coordinate with
    | mk attempt event =>
        exact congrArg (fun value => (⟨value, event⟩ : CommitAttemptEvent graph)) request.1
  have actualRetired : execution.application.attempt ≠ originalAttempt := by
    rwa [← request.1]
  have actualRequest : execution.application.SeedRequest owner
      ⟨execution.application.attempt, coordinate.event⟩ := coordinateEq ▸ request
  have actualResolved : (⟨execution.application.attempt, coordinate.event⟩ :
      CommitAttemptEvent graph).Resolved final.execution.application := coordinateEq ▸ resolved
  have actual := tail_counted_binding_submission_resolved_accepted seeds remaining execution owner
    prior actualRetired coordinate.event binding actualRequest material permitted postTrace final
      trace kept actualResolved
  simpa only [← coordinateEq] using actual

end Vegas.Examples.CommitSeedSignalling
