/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalUnusableAdmission
import Vegas.Examples.CommitSeedBroadcastSubmissionShape
import Vegas.Examples.CommitSeedBroadcastHelperWrongTransmission

/-! # Original clock-two preparation losses in actual continuations -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- A current unusable binding has the fixed loss on the actual branch where
all original bindings are admitted, under any covered continuation. -/
theorem current_unusable_binding_all_admissions_payoff
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner))
    (unusable : (material.call.opening.bind fun raw => raw.as? .bool) = none)
    (players : Player → app.Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ countedMenu.actions who past view)
    (after : app.Execution)
    (reached : after ∈ (app.runRounds (family seed) players remaining
      (execution.respond app owner ⟨some material⟩)).support)
    (admitted : ∀ who, PhaseService.BindingAccepted runtime leaks
      (originalCoordinate who) who after) :
    netPayoff (app.finished after) owner = -(3 / 2) := by
  classical
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have currentRequest : execution.application.SeedRequest owner
      ⟨execution.application.attempt, bindingEvent owner⟩ := by
    simpa only [original, originalCoordinate] using request
  obtain ⟨serial, preparation, evidence, materialEq, _bounded, fresh⟩ :=
    counted_submission_binding_shape (family seed) remaining execution owner trace
      (bindingEvent owner) .bool (bindingEvent_layout owner) currentRequest material offered
  subst material
  obtain ⟨responseTrace⟩ := countedMenu.trace_respond initial horizon (family seed) remaining
    execution owner (⟨some ⟨⟨.commitment (bindingEvent owner) (owner, .prepared serial),
      preparation⟩, evidence⟩⟩ : app.Action) trace offered
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 remaining _ after (by simpa only [Nat.zero_add] using responseTrace) reached
  obtain ⟨emitted, recalled⟩ := app.respond_recall_entry execution owner
    (⟨some ⟨⟨.commitment (bindingEvent owner) (owner, .prepared serial), preparation⟩,
      evidence⟩⟩ : app.Action)
  let entry : app.PlayerEntry := ⟨execution.observe app owner,
    ⟨some ⟨⟨.commitment (bindingEvent owner) (owner, .prepared serial), preparation⟩, evidence⟩⟩,
      emitted⟩
  have member : entry ∈ (execution.respond app owner
      ⟨some ⟨⟨.commitment (bindingEvent owner) (owner, .prepared serial), preparation⟩,
        evidence⟩⟩).recall owner := by
    rw [recalled]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have remembered := runRounds_recall_mono (family seed) players remaining _ after reached owner
    member
  have entryOriginal : entry.beforeView.application.2.attempt = originalAttempt := original
  have entryFresh : entry.beforeView.application.1.candidates (.prepared serial) = .fresh := fresh
  have failed := all_original_admissions_unusable_record_failed seed after finalTrace admitted owner
    entry remembered entryOriginal serial preparation evidence rfl entryFresh unusable
  have raw := countedMenu.toRawTrace initial horizon (family seed) finalTrace
  have complete := family_completesPlay seed ⟨0, none, after⟩ raw ⟨rfl, rfl⟩
  have valid := raw_native_valid (family seed) ⟨0, none, after⟩ raw
  have compiled := raw
  rw [initial_eq_compiled] at compiled
  have coverage := phaseFailureCoverage_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon (family seed) compiled
  have published := failed_binding_publication after.application.current.native valid.active
    complete owner failed
  have excluded := coverage.active.covered (revealEvent owner) owner (reveal_actor owner)
    (Or.inr published)
  rw [counted_fixed_endpoint_payoff seed after finalTrace owner, ite_eq_left excluded]

/-- A counted clock-two transmission uses the sole original packet. On a bad
seed its value is the fixed loss, independently of its private preparation. -/
theorem current_bad_clock_two_transmission_payoff
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (bad : seed.2 owner = false)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner))
    (players : Player → app.Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ countedMenu.actions who past view)
    (after : app.Execution)
    (reached : after ∈ (app.runRounds (family seed) players remaining
      (execution.respond app owner ⟨some material⟩)).support) :
    netPayoff (app.finished after) owner = -(3 / 2) := by
  obtain ⟨responseTrace⟩ := countedMenu.trace_respond initial horizon (family seed) remaining
    execution owner ⟨some material⟩ trace offered
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 remaining _ after (by simpa only [Nat.zero_add] using responseTrace) reached
  obtain ⟨emitted, recalled⟩ := app.respond_recall_entry execution owner
    (⟨some material⟩ : app.Action)
  let entry : app.PlayerEntry := ⟨execution.observe app owner, ⟨some material⟩, emitted⟩
  have member : entry ∈ (execution.respond app owner ⟨some material⟩).recall owner := by
    rw [recalled]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have remembered := runRounds_recall_mono (family seed) players remaining _ after reached owner
    member
  have valid := raw_native_valid (family seed) ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) trace)
  have publicRequest : PhaseRuntimeState.requests entry.beforeView.application.2 owner
      (originalCoordinate owner) :=
    (execution.application.requests_publicView valid owner (originalCoordinate owner)).mpr request
  exact bad_clock_two_record_terminal_payoff seed after finalTrace owner bad entry remembered
    publicRequest material rfl clock

/-- A permitted current transmission at the good clock-two slot obtains its
actual original receipt by the terminal endpoint, for every covered future. -/
theorem current_good_clock_two_transmission_accepted
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (good : seed.2 owner = true)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner))
    (players : Player → app.Policy)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ countedMenu.actions who past view)
    (after : app.Execution)
    (reached : after ∈ (app.runRounds (family seed) players remaining
      (execution.respond app owner ⟨some material⟩)).support) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner after := by
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have currentRequest : execution.application.SeedRequest owner
      ⟨execution.application.attempt, bindingEvent owner⟩ := by
    simpa only [original, originalCoordinate] using request
  obtain ⟨serial, preparation, evidence, materialEq, _bounded, _fresh⟩ :=
    counted_submission_binding_shape (family seed) remaining execution owner trace
      (bindingEvent owner) .bool (bindingEvent_layout owner) currentRequest material offered
  have named : material.call.packet.event? graph = some (bindingEvent owner) := by
    rw [materialEq]
    rfl
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seed) remaining
    execution owner ⟨some material⟩ trace offered
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 remaining _ after (by simpa only [Nat.zero_add] using responded) reached
  have accounted := (countedMenu.roundSupported_uniform initial horizon (family seed) finalTrace).1
  have enough : 30 ≤ after.environmentRecall.length := by
    change after.environmentRecall.length + 0 = 128 at accounted
    omega
  have resolved := original_bindings_resolved seed ⟨0, none, after⟩
    (countedMenu.toRawTrace initial horizon (family seed) finalTrace) enough owner
  exact original_eligible_response_resolved_accepted seed remaining execution owner trace request
    (clock.trans (by rw [good]; rfl)) material offered named players covered after reached resolved

end Vegas.Examples.CommitSeedBroadcast
