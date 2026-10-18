/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastProperOpening
import Vegas.Pending.PhaseBindingMenuShape
import Vegas.Pending.PhaseCountedOpeningSubmission

/-! # Exact submission shapes at concrete counted callbacks -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction

/-- The real counted publication menu fixes its emitted opening call. -/
theorem counted_submission_opening_shape (selected : app.Scheduler)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon selected).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (material : WitnessedSubmission graph)
    (allowed : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner)) :
    ∃ (candidate : Handle graph) (raw : Raw simpleExpr),
      material.call.packet = .opening (revealEvent owner) candidate raw := by
  have compiledTrace := trace
  rw [initial_eq_compiled] at compiledTrace
  exact PhaseCount.submitted_opening_packet runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
    (setup.initialLaw.map encodeInputs) horizon selected remaining owner execution compiledTrace
      (revealEvent owner) .bool (revealEvent_layout owner) request material allowed

/-- The real counted binding menu retains the preparation, evidence, bounded
slot and actual candidate freshness of its sole admitted declaration. -/
theorem counted_submission_binding_shape (selected : app.Scheduler)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon selected).Trace
      (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (payload : simpleExpr.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, event⟩)
    (material : WitnessedSubmission graph)
    (allowed : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner)) :
    ∃ (serial : Nat) (preparation : Option (Raw simpleExpr)) (evidence : EvidenceRequest graph),
      material = ⟨⟨.commitment event (owner, .prepared serial), preparation⟩, evidence⟩ ∧
      serial < bounds.candidateCount ∧
      execution.application.current.native.candidates.lookup (owner, .prepared serial) =
        .fresh := by
  have compiledTrace := trace
  rw [initial_eq_compiled] at compiledTrace
  exact PhaseCount.onePacket_binding_shape runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
    (setup.initialLaw.map encodeInputs) horizon selected remaining owner execution compiledTrace
      event payload binding request material allowed

end Vegas.Examples.CommitSeedBroadcast
