/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingContract
import Vegas.Examples.CommitSeedSignallingPayoffs
import Vegas.Pending.PhaseEntryOwnRecall

/-! # The first publication suffix retains no earlier publication callback -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- Before leaving the original commitment, every retained callback was in
that same commitment namespace. In particular none requested an owner's
publication, even at an arbitrary other physical coordinate. -/
theorem original_prefix_no_publication_request (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (owner : Player) (entry : app.PlayerEntry)
    (recorded : entry ∈ current.execution.recall owner)
    (coordinate : CommitAttemptEvent graph) (publication : coordinate.event = revealEvent owner) :
    ¬ PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate := by
  have initialized : ∀ state ∈ initial.support, state.Ordered := by
    intro state supported
    rw [initial_eq_pure] at supported
    cases (PMF.mem_support_pure_iff _ _).mp supported
    exact PhaseRuntimeState.initial_ordered plan _
  have earlier := phase_ownRecall_namespace_le_history runtime leaks initial initialized horizon
    selected trace owner entry recorded
  rw [original] at earlier
  have entryOriginal : entry.beforeView.application.2.attempt = originalAttempt := by
    cases address : entry.beforeView.application.2.attempt with
    | mk phase generation =>
        simp only [address, originalAttempt] at earlier
        have phaseZero : phase = 0 := by omega
        have generationZero : generation = 0 := by omega
        simp only [phaseZero, generationZero, originalAttempt]
  obtain ⟨before, prior, _acting, viewed⟩ := app.recorded_response_prefix initial horizon selected
    current trace owner entry recorded
  have beforeOriginal : before.execution.application.attempt = originalAttempt := by
    rw [viewed] at entryOriginal
    exact entryOriginal
  have phases := original_phases selected before prior.some beforeOriginal
  have phaseView : entry.beforeView.application.2.phase = some (.commitment, 0, 2) := by
    rw [viewed]
    change before.execution.application.phases.head?.map
      (fun phase => (phase.kind, phase.low, phase.high)) = _
    rw [phases]
    rfl
  intro requested
  obtain ⟨_same, ⟨kind, low, high, installed, _lower, upper⟩, _active⟩ := requested
  rw [phaseView] at installed
  have descriptor : (.commitment, 0, 2) = (kind, low, high) := Option.some.inj installed
  have highEq : high = 2 := (congrArg (fun value : RuntimePhaseKind × Nat × Nat => value.2.2)
    descriptor).symm
  have revealLower : 2 ≤ coordinate.event.val := by
    rw [publication]
    fin_cases owner <;> decide
  rw [highEq] at upper
  omega

/-- An environment inclusion adds no own response record. Thus the first
publication entry reached from the original commitment has no old own
publication request, without any restriction on its old silent word. -/
theorem original_environment_no_prior_publication_request (selected : app.Scheduler)
    (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (original : current.execution.application.attempt = originalAttempt)
    (next : app.Execution) (command : app.Command)
    (moved : next ∈ (current.execution.environmentStep app command).support)
    (owner : Player) (entry : app.PlayerEntry) (recorded : entry ∈ next.recall owner)
    (coordinate : CommitAttemptEvent graph) (publication : coordinate.event = revealEvent owner) :
    ¬ PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate := by
  rw [app.environmentStep_recall current.execution next command moved] at recorded
  exact original_prefix_no_publication_request selected current trace original owner entry recorded
    coordinate publication

end Vegas.Examples.CommitSeedSignalling
