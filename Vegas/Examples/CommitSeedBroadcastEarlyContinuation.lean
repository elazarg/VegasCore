/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialHelperAdmission

/-! # Actual original admission after a permitted current early transmission -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- A permitted original clock-zero transmission admits every original under
unchanged assessed foreign policies, retaining the actual initial prefix and
allowing arbitrary count-covered focal future behavior. -/
theorem early_response_original_admissions
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (remaining : Nat) (execution : app.Execution) (focal : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some focal, execution⟩))
    (request : execution.application.SeedRequest focal (originalCoordinate focal))
    (clock : execution.application.current.native.clock = 0)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions focal
      (execution.recall focal) (execution.observe app focal))
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (selected : ∀ owner, owner ≠ focal →
      players owner = countedMenu.decodeProfile initial horizon scheduler
        (countedAssessmentProfile assessment) owner)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining
      (execution.respond app focal ⟨some material⟩)).support) :
    ∀ owner, PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have earlyPosition := original_zero_clock_index seed ⟨remaining, some focal, execution⟩ raw
    request.1.symm clock
  change execution.environmentRecall.length ≤ 3 at earlyPosition
  have budget := app.raw_trace_horizon initial horizon (family seed) raw
  change execution.environmentRecall.length + remaining = horizon at budget
  let count := 5 - execution.environmentRecall.length
  have framePosition : execution.environmentRecall.length + count = 5 := by
    dsimp only [count]
    omega
  have enough : count ≤ remaining := by
    dsimp only [count, horizon] at *
    omega
  have split : remaining = count + (remaining - count) := by omega
  have actual := reached
  rw [split, app.runRounds_add] at actual
  obtain ⟨frame, stage, following⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ actual)
  obtain ⟨respondedTrace⟩ := countedMenu.trace_respond initial horizon (family seed) remaining
    execution focal ⟨some material⟩ trace offered
  have source : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨(remaining - count) + count, none,
        execution.respond app focal ⟨some material⟩⟩) := by
    simpa only [Nat.sub_add_cancel enough] using respondedTrace
  obtain ⟨frameTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    (remaining - count) count (execution.respond app focal ⟨some material⟩) frame source stage
  have position : frame.environmentRecall.length = 5 := by
    have length := app.runRounds_environmentRecall_length (family seed) players count
      (execution.respond app focal ⟨some material⟩) frame stage
    change frame.environmentRecall.length = execution.environmentRecall.length + count at length
    exact length.trans framePosition
  obtain ⟨emitted, recalled⟩ := app.respond_recall_entry execution focal ⟨some material⟩
  let entry : app.PlayerEntry := ⟨execution.observe app focal, ⟨some material⟩, emitted⟩
  have member : entry ∈ frame.recall focal :=
    (rounds_recall_retained (family seed) players count
      (execution.respond app focal ⟨some material⟩) frame stage focal).subset (by
        rw [recalled]
        exact List.mem_append_right _ (List.mem_singleton_self _))
  exact frame_focal_early_original_admissions assessment equilibrium seed supportedSeed
    (remaining - count) frame frameTrace position focal ⟨entry, member, by simp [entry]⟩
    players covered selected final following

end Vegas.Examples.CommitSeedBroadcast
