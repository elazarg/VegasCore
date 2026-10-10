/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobResponseState

/-! # Physical service of receiver submissions after arbitrary prefixes

Every non-silent native receiver response is serviced using its actual next
message identifier. Earlier receiver traffic need not be clean or silent.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobSubmissionService

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeBobResponseState

/-- The actual protected inclusion of a newly authored submission. -/
def servicedSubmission (execution : app.Execution) (material : app.Submission) : app.Execution :=
  let submitted := execution.respond app bob ⟨some material⟩
  let id := (bob, execution.network.nextSerial bob)
  let included := submitted.includePending app id
  { included with environmentRecall := submitted.environmentRecall ++
    [⟨submitted.observeEnvironment app, .include id⟩] }

theorem submission_round (weight : ℝ) (nonnegative : 0 ≤ weight) (remaining : Nat)
    (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining, some bob, execution⟩))
    (material : app.Submission) (players : Player → app.Policy) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (execution.respond app bob ⟨some material⟩) =
        PMF.pure (servicedSubmission execution material) := by
  have chosen := protected_response_scheduler weight nonnegative
    ⟨remaining, some bob, execution⟩ trace bob rfl ⟨some material⟩ (Or.inl rfl)
  have serials := app.serialsBeforeNext_history
    (LateOpeningRuntimeService.scheduler weight nonnegative) initial
      LateOpeningRuntimeService.horizon trace
  have selected := latestAuthor_after_submit execution bob material serials
  rw [ReactiveApplication.round, chosen, selected, PMF.pure_bind,
    ReactiveApplication.dispatch]
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
    PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
  rfl

theorem submission_physical (weight : ℝ) (nonnegative : 0 ≤ weight) (remaining : Nat)
    (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨remaining, some bob, execution⟩))
    (material : app.Submission) :
    (servicedSubmission execution material).application =
      responseState execution ⟨some material⟩ := by
  have serials := app.serialsBeforeNext_history
    (LateOpeningRuntimeService.scheduler weight nonnegative) initial
      LateOpeningRuntimeService.horizon trace
  have lookup := serials.lookup_submit bob
    (app.packet (app.submit execution.application bob material) bob
      (execution.network.known bob) material)
  have emitted : (execution.respond app bob ⟨some material⟩).network.lookup
      (bob, execution.network.nextSerial bob) =
        some ⟨(bob, execution.network.nextSerial bob),
          app.packet (app.submit execution.application bob material) bob
            (execution.network.known bob) material⟩ := lookup
  change ((execution.respond app bob ⟨some material⟩).includePending app
    (bob, execution.network.nextSerial bob)).application = _
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [emitted]
  rfl

end Vegas.Examples.LateOpeningRuntimeBobSubmissionService
