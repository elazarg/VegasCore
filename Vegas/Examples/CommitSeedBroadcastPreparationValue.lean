/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPreparationLoss
import Vegas.Examples.CommitSeedBroadcastRegularContinuation
import Vegas.Examples.CommitSeedBroadcastGoodReceiptForecast

/-! # Quantitative value comparisons for original private preparations -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- On an actual regular original seed, any unusable current declaration has
the fixed loss under unchanged assessed opponents and any covered own tail. -/
theorem regular_unusable_clock_two_finish_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = [])
    (regular : regularFirstLateControl seed (some ⟨remaining, some owner, execution⟩))
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner))
    (unusable : (material.call.opening.bind fun raw => raw.as? .bool) = none)
    (tail : app.Policy)
    (tailCovered : ∀ past view response, response ∈ (tail past view).support →
      response ∈ countedMenu.actions owner past view) :
    expect (app.finish initial horizon (family seed)
      (Function.update
        (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
        owner tail) (some ⟨remaining, none, execution.respond app owner ⟨some material⟩⟩))
          (fun state => netPayoff state owner) = -(3 / 2) := by
  classical
  let players := Function.update
    (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
      owner tail
  have covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ countedMenu.actions who past view := by
    intro who past view response supported
    by_cases same : who = owner
    · subst who
      exact tailCovered past view response
        (by simpa only [players, Function.update_self] using supported)
    · dsimp only [players] at supported
      rw [Function.update_of_ne same] at supported
      exact countedMenu.decode_embedPolicy_covered initial horizon scheduler who
        (countedAssessmentProfile assessment who) past view response supported
  change expect (app.finish initial horizon (family seed) players _)
    (fun state => netPayoff state owner) = _
  rw [← expect_constant (app.finish initial horizon (family seed) players
    (some ⟨remaining, none, execution.respond app owner ⟨some material⟩⟩)) (-(3 / 2) : ℝ)]
  apply expect_congr_on_support
  intro state supported
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind] at supported
  obtain ⟨after, reached, rfl⟩ := PMF.support_map .. ▸ supported
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seed) remaining
    execution owner ⟨some material⟩ trace offered
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 remaining _ after (by simpa only [Nat.zero_add] using responded) reached
  have accounted := (countedMenu.roundSupported_uniform initial horizon (family seed) finalTrace).1
  have enough : 30 ≤ after.environmentRecall.length := by
    change after.environmentRecall.length + 0 = 128 at accounted
    omega
  have resolved := original_bindings_resolved seed ⟨0, none, after⟩
    (countedMenu.toRawTrace initial horizon (family seed) finalTrace) enough
  have admitted := regular_assessed_original_admission assessment equilibrium seed supportedSeed
    remaining execution owner trace request clock empty regular ⟨some material⟩ offered
      (by intro impossible; cases impossible) tail tailCovered after reached resolved
  exact current_unusable_binding_all_admissions_payoff seed remaining execution owner trace request
    material offered unusable players covered after reached admitted

/-- A supported original seed's genuine counted terminal control is also a
genuine counted control of the installed mixture, by the original joint law. -/
theorem counted_fixed_terminal_mixed_trace (seed : Seeds)
    (supportedSeed : seed ∈ nativeSeedLaw.support) (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, execution⟩)) :
    Nonempty (countedProtocol.Trace (some ⟨0, none, execution⟩)) := by
  have roundSupport := countedMenu.roundSupported_uniform initial horizon (family seed) trace
  have accounted : execution.environmentRecall.length = horizon := by
    have length := roundSupport.1
    change execution.environmentRecall.length + 0 = horizon at length
    omega
  have fixed : execution ∈ (app.runRounds (family seed) countedMenu.uniformResponses horizon
      initialExecution).support := by
    have actual := roundSupport.2
    change execution ∈ (app.roundsFrom initial (family seed) countedMenu.uniformResponses
      execution.environmentRecall.length).support at actual
    rw [accounted] at actual
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using actual
  have paired : (execution, seed) ∈ (nativeSeedLaw.bind fun chosen =>
      (app.runRounds (family chosen) countedMenu.uniformResponses horizon initialExecution).map
        fun next => (next, chosen)).support := by
    rw [PMF.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨seed, supportedSeed,
      (PMF.mem_support_map_iff _ _ _).mpr ⟨execution, fixed, rfl⟩⟩
  dsimp only [initialExecution] at paired
  rw [app.schedulerMixture_joint nativeSeedLaw family countedMenu.uniformResponses horizon
    initialState] at paired
  obtain ⟨next, actual, posterior⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ paired)
  obtain ⟨chosen, _supported, same⟩ := PMF.support_map .. ▸ posterior
  have nextEq : next = execution := congrArg Prod.fst same
  subst next
  have mixed : execution ∈
      (app.roundsFrom initial scheduler countedMenu.uniformResponses horizon).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution,
      scheduler, implementation] using actual
  obtain ⟨history⟩ := countedMenu.trace_roundsFrom initial horizon scheduler
    countedMenu.uniformResponses (fun who past view action supported =>
      (countedMenu.uniformResponses_support who past view action).mp supported)
        horizon le_rfl execution mixed
  exact ⟨by simpa only [Nat.sub_self] using history⟩

/-- The native failed-publication readout is unchanged when its terminal
control is witnessed under a supported original seed. -/
theorem counted_fixed_missing_original_publication_failed (seed : Seeds)
    (supportedSeed : seed ∈ nativeSeedLaw.support) (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨0, none, execution⟩)) (owner : Player)
    (missing : ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      execution) :
    RecoveryState.publicationFailed execution.application.current.native (revealEvent owner) =
      true := by
  obtain ⟨mixed⟩ := counted_fixed_terminal_mixed_trace seed supportedSeed execution trace
  exact counted_endpoint_missing_original_publication_failed execution mixed owner missing

/-- Proper clock-two play reaches the reward ceiling on every foreign-original
miss at a good seed, with no assumption on foreign private preparations. -/
theorem proper_clock_two_foreign_miss_fixed_finish_payoff
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (good : seed.2 owner = true)
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner))
    (players : Player → app.Policy) (selected : players owner = scheduledProperPolicy 2 owner)
    (covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ countedMenu.actions who past view)
    (past : (scheduledProperPolicy 2 owner).Consistent (execution.recall owner))
    (after : app.Execution)
    (reached : app.finished after ∈ (app.finish initial horizon (family seed) players
      (some ⟨remaining, some owner, execution⟩)).support)
    (foreign : ∃ other : Player, other ≠ owner ∧
      ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate other) other after) :
    netPayoff (app.finished after) owner = 1 := by
  obtain ⟨_accepted, active⟩ := scheduled_proper_eligible_finish_survives 2 seed remaining execution
    owner trace request clock (by rw [good]; rfl) unsent players selected covered past after reached
  obtain ⟨finalTrace⟩ := countedMenu.finish_trace initial horizon (family seed) players covered
    (some ⟨remaining, some owner, execution⟩) trace (app.finished after) reached
  obtain ⟨other, different, missing⟩ := foreign
  have failed := counted_fixed_missing_original_publication_failed seed supportedSeed after
    finalTrace other missing
  rw [counted_fixed_endpoint_payoff seed after finalTrace owner, ite_eq_right active,
    ite_eq_left ⟨other, different, failed⟩]

end Vegas.Examples.CommitSeedBroadcast
