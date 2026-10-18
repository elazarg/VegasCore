/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPreparationMass
import Vegas.Examples.CommitSeedBroadcastPreparationMask
import Vegas.Examples.CommitSeedBroadcastPreparationValue

/-! # Pointwise native preparation comparisons before averaging original seeds -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

open Classical in
/-- The comparison value read from the original seed and physical prefix. -/
def preparationReferenceValue (seed : Seeds) (execution : app.Execution) (owner : Player) : ℝ :=
  if seed.2 owner then
    if ∀ other, other ≠ owner → originalReceiptForecast seed execution other then 0 else 1
  else -(3 / 2)

/-- A complete proper clock-two continuation starts with an actual permitted
response; its later physical law is the original fixed-family continuation. -/
theorem proper_clock_two_finish_response
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2)
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner))
    (players : Player → app.Policy) (selected : players owner = scheduledProperPolicy 2 owner)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (after : app.Execution)
    (reached : app.finished after ∈ (app.finish initial horizon (family seed) players
      (some ⟨remaining, some owner, execution⟩)).support) :
    ∃ action : app.Action,
      action ∈ countedMenu.actions owner (execution.recall owner) (execution.observe app owner) ∧
      after ∈ (app.runRounds (family seed) players remaining
        (execution.respond app owner action)).support := by
  obtain ⟨serial, _bounded, proper, _slot, _fresh, _result⟩ := proper_original_clock_response
    (family seed) remaining execution owner
      (countedInRaw.trace initial horizon (family seed) trace) request 2 clock unsent
  let action := phaseBindingResponse runtime leaks owner (bindingEvent owner) .bool
    (.success true) serial
  have literal : scheduledProperPolicy 2 owner (execution.recall owner)
      (execution.observe app owner) = PMF.pure action := by
    unfold scheduledProperPolicy
    rw [ite_eq_right (fun both => by
      have zero := both.2.1
      change execution.application.current.native.clock = 0 at zero
      omega)]
    exact proper
  have offered := covered owner (execution.recall owner) (execution.observe app owner) action
    (by rw [selected, literal]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  refine ⟨action, offered, ?_⟩
  change app.finished after ∈ (((app.resume players (some owner) execution).bind
    (app.runRounds (family seed) players remaining)).map app.finished).support at reached
  rw [ReactiveApplication.resume, ReactiveApplication.invoke, selected, literal,
    PMF.pure_map, PMF.pure_bind, PMF.support_map] at reached
  obtain ⟨final, supported, equal⟩ := reached
  have same : final = after :=
    congrArg ReactiveApplication.Control.execution (Option.some.inj equal)
  exact same ▸ supported

/-- The proper policy attains the reward ceiling whenever the original
foreign receipt forecast contains a miss, including old off-path omissions. -/
theorem proper_clock_two_preparation_reference_lower
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
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some (originalCoordinate owner))
    (past : (scheduledProperPolicy 2 owner).Consistent (execution.recall owner)) :
    preparationReferenceValue seed execution owner ≤
      expect (app.finish initial horizon (family seed)
        (Function.update
          (countedMenu.decodeProfile initial horizon scheduler
            (countedAssessmentProfile assessment))
          owner (scheduledProperPolicy 2 owner)) (some ⟨remaining, some owner, execution⟩))
            (fun state => netPayoff state owner) := by
  classical
  have bounded (state : app.ProtocolState) : |netPayoff state owner| ≤ (9 / 2 : ℝ) := by
    have range := netPayoff_mem_Icc state owner
    exact abs_le.mpr ⟨range.1, by linarith [range.2]⟩
  let players := Function.update
    (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
      owner (scheduledProperPolicy 2 owner)
  have covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view := by
    intro who past view action chosen
    by_cases same : who = owner
    · subst who
      exact scheduledProperPolicy_counted 2 owner past view action
        (by simpa only [players, Function.update_self] using chosen)
    · dsimp only [players] at chosen
      rw [Function.update_of_ne same] at chosen
      exact countedMenu.decode_embedPolicy_covered initial horizon scheduler who
        (countedAssessmentProfile assessment who) past view action chosen
  have selected : players owner = scheduledProperPolicy 2 owner := Function.update_self ..
  change preparationReferenceValue seed execution owner ≤
    expect (app.finish initial horizon (family seed) players _) _
  cases good : seed.2 owner with
  | false =>
      simpa only [preparationReferenceValue, good, Bool.false_eq_true, ite_false] using
        counted_fixed_finish_value_lower seed ⟨remaining, some owner, execution⟩ trace owner
          players covered
  | true =>
      by_cases all : ∀ other, other ≠ owner → originalReceiptForecast seed execution other
      · have reference : preparationReferenceValue seed execution owner = 0 := by
          change (if seed.2 owner then _ else _) = _
          rw [good]
          exact ite_eq_left all
        rw [reference]
        exact proper_clock_two_good_fixed_finish_value_nonnegative seed remaining execution owner
          trace request clock good unsent players selected covered past
      · have reference : preparationReferenceValue seed execution owner = 1 := by
          change (if seed.2 owner then _ else _) = _
          rw [good]
          exact ite_eq_right all
        rw [reference]
        rw [← expect_constant (app.finish initial horizon (family seed) players
          (some ⟨remaining, some owner, execution⟩)) (1 : ℝ)]
        apply expect_mono ?_ (payoffIntegrable_constant _ _)
          (payoffIntegrable_of_bounded _ _ bounded)
        intro state reached
        obtain ⟨after, _continued, equal⟩ := PMF.support_map .. ▸ reached
        subst state
        obtain ⟨action, offered, actual⟩ := proper_clock_two_finish_response seed remaining
          execution
          owner trace request clock unsent players selected covered after reached
        obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seed) remaining
          execution owner action trace offered
        obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players
          covered 0 remaining _ after (by simpa only [Nat.zero_add] using responded) actual
        have length := (countedMenu.roundSupported_uniform initial horizon (family seed)
          finalTrace).1
        have enough : 30 ≤ after.environmentRecall.length := by
          change after.environmentRecall.length + 0 = 128 at length
          omega
        have resolved := original_bindings_resolved seed ⟨0, none, after⟩
          (countedMenu.toRawTrace initial horizon (family seed) finalTrace) enough
        push Not at all
        obtain ⟨other, otherNe, absent⟩ := all
        have forecast := foreign_clock_two_preparation_receipt_forecast assessment equilibrium seed
          supportedSeed remaining execution owner trace request clock empty good action offered
            (scheduledProperPolicy 2 owner) (scheduledProperPolicy_counted 2 owner) after actual
              resolved other otherNe
        have ceiling := proper_clock_two_foreign_miss_fixed_finish_payoff seed supportedSeed
          remaining execution owner trace request clock good unsent players selected covered past
            after reached ⟨other, otherNe, fun accepted => absent (forecast.mp accepted)⟩
        exact le_of_eq ceiling.symm

/-- An unusable declaration loses the whole fixed stake whenever the same
original forecast admits every foreign owner. No equality of future draws is assumed. -/
theorem unusable_clock_two_preparation_reference_upper
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
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner))
    (unusable : (material.call.opening.bind fun raw => raw.as? .bool) = none)
    (tail : app.Policy)
    (tailCovered : ∀ past view action, action ∈ (tail past view).support →
      action ∈ countedMenu.actions owner past view) :
    expect (app.finish initial horizon (family seed)
      (Function.update
        (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
        owner tail) (some ⟨remaining, none, execution.respond app owner ⟨some material⟩⟩))
          (fun state => netPayoff state owner) ≤
      preparationReferenceValue seed execution owner -
        preparationAdvantageMark seed (some ⟨remaining, some owner, execution⟩) owner := by
  classical
  have bounded (state : app.ProtocolState) : |netPayoff state owner| ≤ (9 / 2 : ℝ) := by
    have range := netPayoff_mem_Icc state owner
    exact abs_le.mpr ⟨range.1, by linarith [range.2]⟩
  let players := Function.update
    (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
      owner tail
  have covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view := by
    intro who past view action chosen
    by_cases same : who = owner
    · subst who
      exact tailCovered past view action
        (by simpa only [players, Function.update_self] using chosen)
    · dsimp only [players] at chosen
      rw [Function.update_of_ne same] at chosen
      exact countedMenu.decode_embedPolicy_covered initial horizon scheduler who
        (countedAssessmentProfile assessment who) past view action chosen
  change expect (app.finish initial horizon (family seed) players _) _ ≤ _
  apply expect_le_const _ _ (payoffIntegrable_of_bounded _ _ bounded)
  intro state reached
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind] at reached
  obtain ⟨after, actual, rfl⟩ := PMF.support_map .. ▸ reached
  cases good : seed.2 owner with
  | false =>
      have loss := current_bad_clock_two_transmission_payoff seed remaining execution owner trace
        request clock good material offered players covered after actual
      rw [loss]
      simp only [preparationReferenceValue, preparationAdvantageMark, good, Bool.false_eq_true,
        ite_false, false_and, sub_zero]
      norm_num
  | true =>
      by_cases all : ∀ other, other ≠ owner → originalReceiptForecast seed execution other
      · have admitted (who : Player) :
            PhaseService.BindingAccepted runtime leaks (originalCoordinate who) who after := by
          by_cases same : who = owner
          · subst who
            exact current_good_clock_two_transmission_accepted seed remaining execution owner trace
              request clock good material offered players covered after actual
          · obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seed) remaining
              execution owner ⟨some material⟩ trace offered
            obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players
              covered 0 remaining _ after (by simpa only [Nat.zero_add] using responded) actual
            have length := (countedMenu.roundSupported_uniform initial horizon (family seed)
              finalTrace).1
            have enough : 30 ≤ after.environmentRecall.length := by
              change after.environmentRecall.length + 0 = 128 at length
              omega
            have resolved := original_bindings_resolved seed ⟨0, none, after⟩
              (countedMenu.toRawTrace initial horizon (family seed) finalTrace) enough
            exact (foreign_clock_two_preparation_receipt_forecast assessment equilibrium seed
              supportedSeed remaining execution owner trace request clock empty good ⟨some material⟩
                offered tail tailCovered after actual resolved who same).mpr (all who same)
        have loss := current_unusable_binding_all_admissions_payoff seed remaining execution owner
          trace request material offered unusable players covered after actual admitted
        rw [loss]
        have reference : preparationReferenceValue seed execution owner = 0 := by
          change (if seed.2 owner then _ else _) = _
          rw [good]
          exact ite_eq_left all
        have mark : preparationAdvantageMark seed
            (some ⟨remaining, some owner, execution⟩) owner = 3 / 2 := by
          exact ite_eq_left ⟨good, all⟩
        rw [reference, mark]
        norm_num
      · have upper := (netPayoff_mem_Icc (app.finished after) owner).2
        have reference : preparationReferenceValue seed execution owner = 1 := by
          change (if seed.2 owner then _ else _) = _
          rw [good]
          exact ite_eq_right all
        have mark : preparationAdvantageMark seed
            (some ⟨remaining, some owner, execution⟩) owner = 0 := by
          exact ite_eq_right (fun both => all both.2)
        rw [reference, mark, sub_zero]
        exact upper

end Vegas.Examples.CommitSeedBroadcast
