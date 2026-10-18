/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastBadOwnerCallback
import Vegas.Examples.CommitSeedBroadcastOriginalPacketWord
import Vegas.Examples.CommitSeedBroadcastHelperClockTwoTiming
import Vegas.Examples.CommitSeedBroadcastClockThreeTiming
import Vegas.Examples.CommitSeedBroadcastRegularAdmission

/-! # Original bad-owner admission from the retained initial public packet word -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- An initial helper packet gives every still-unpolled bad owner its actual
clock-three service. The old initial word is retained, and all other policies
remain arbitrary count-covered kernels. -/
theorem foreign_singleton_bad_helper_original_admission
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (remaining : Nat) (anchor : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, anchor⟩))
    (owner : Player) (bad : seed.2 owner = false)
    (started : 5 ≤ anchor.environmentRecall.length)
    (ahead : anchor.environmentRecall.length ≤ 11 + (seed.1.symm owner).val)
    (first : app.PlayerEntry) (word : anchor.recall owner = [first])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (zero : first.beforeView.application.2.native.clock = 0)
    (helper : initialPublicPackets anchor ≠ ∅)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view)
    (selected : players owner = countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment) owner)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining anchor).support)
    (resolved : (originalCoordinate owner).Resolved final.application) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final := by
  classical
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 remaining anchor final (by simpa only [Nat.zero_add] using trace) reached
  have retained := rounds_recall_retained (family seed) players remaining anchor final reached owner
  have firstMember : first ∈ final.recall owner := retained.subset (by
    rw [word]; exact List.mem_singleton_self _)
  by_cases silent : first.action.transmission = none
  · have outputs := silent_own_outputs_of_history (family seed) _
      (countedMenu.toRawTrace initial horizon (family seed) trace) owner (by
        intro entry member
        rw [word, List.mem_singleton] at member
        subst entry
        exact silent)
    have missing := outputs_empty_original_unaccepted seed remaining anchor trace owner outputs
    have request := original_request_of_unaccepted_before_expiry seed _
      (countedMenu.toRawTrace initial horizon (family seed) trace) owner missing (by
        change anchor.environmentRecall.length < 28
        have rank := (seed.1.symm owner).isLt
        omega)
    let count := 11 + (seed.1.symm owner).val - anchor.environmentRecall.length
    have target : anchor.environmentRecall.length + count = 11 + (seed.1.symm owner).val := by
      dsimp only [count]
      omega
    have budget := (countedMenu.roundSupported_uniform initial horizon (family seed) trace).1
    change anchor.environmentRecall.length + remaining = horizon at budget
    have rank := (seed.1.symm owner).isLt
    have enough : count + 1 + 7 ≤ remaining := by dsimp only [horizon] at budget; omega
    have split : remaining = (count + 1) + (remaining - (count + 1)) := by omega
    have actual := reached
    rw [split, app.runRounds_add] at actual
    obtain ⟨middle, stage, following⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ actual)
    obtain ⟨before, observed, action, _before, _observed, _command, ⟨observedTrace⟩,
      observedRequest, observedClock, observedWord, chosen, middleEq⟩ :=
        bad_owner_firstLate_callback seed remaining anchor owner bad trace request
          (by rw [outputs]; exact fun _ member => (List.not_mem_nil member).elim) started ahead
          players covered middle stage
    have countdown : remaining - count - 1 = remaining - (count + 1) := by omega
    change (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining - count - 1, some owner, observed⟩) at observedTrace
    rw [countdown] at observedTrace
    have wordTwo : observed.recall owner = [first] := observedWord.trans word
    have packets : initialPublicPackets observed = initialPublicPackets anchor := by
      have preserved := runRounds_initialPublicPackets (family seed) players (count + 1) anchor
        middle (by omega) stage
      rw [middleEq] at preserved
      exact preserved
    have receipted : observed.receipts ≠ [] := by
      intro empty
      have noPackets := (bad_firstLate_receipts_empty_iff_initial_packets seed _
        (countedMenu.toRawTrace initial horizon (family seed) observedTrace) owner rfl
          observedRequest.1.symm observedClock bad).mp empty
      exact helper (packets.symm.trans noPackets)
    obtain ⟨mixed⟩ := counted_fixed_decision_mixed seed supportedSeed _ observed owner observedTrace
    let source : countedProtocol.History := ⟨_, mixed⟩
    have waited := counted_helper_clock_two_response_wait assessment equilibrium source _ observed
      owner rfl observedRequest observedClock receipted first wordTwo firstRequest silent zero
    rw [selected, waited, PMF.mem_support_pure_iff] at chosen
    subst action
    have secondSplit : remaining - (count + 1) = 7 + (remaining - (count + 1) - 7) := by omega
    rw [secondSplit, app.runRounds_add] at following
    obtain ⟨later, seven, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ following)
    rw [middleEq] at seven
    have outputsTwo : app.outputs (observed.recall owner) = [] := by
      rw [observedWord]
      exact outputs
    obtain ⟨_enough, _prior, finalCallback, finalAction, _priorLaw, _observed, _command,
      ⟨callbackTrace⟩, callbackRequest, callbackClock, callbackWord, callbackChosen, laterEq⟩ :=
        helper_wait_reaches_clock_three seed (remaining - (count + 1)) observed owner observedTrace
          observedRequest observedClock bad outputsTwo players covered later seven
    let second : app.PlayerEntry := ⟨observed.observe app owner, ⟨none⟩, none⟩
    have postWord : (observed.respond app owner ⟨none⟩).recall owner = [first, second] := by
      simp only [ReactiveApplication.Execution.respond, ite_true]
      change observed.recall owner ++ [second] = _
      rw [wordTwo]
      rfl
    have wordThree : finalCallback.recall owner = [first, second] := callbackWord.trans postWord
    have validTwo := raw_native_valid (family seed) _
      (countedMenu.toRawTrace initial horizon (family seed) observedTrace)
    have secondRequest : PhaseRuntimeState.requests second.beforeView.application.2 owner
        (originalCoordinate owner) :=
      (observed.application.requests_publicView validTwo owner (originalCoordinate owner)).mpr
        observedRequest
    obtain ⟨mixedThree⟩ := counted_fixed_decision_mixed seed supportedSeed _ finalCallback owner
      callbackTrace
    let sourceThree : countedProtocol.History := ⟨_, mixedThree⟩
    have responseLaw := counted_assessment_response_law assessment equilibrium sourceThree _
      finalCallback owner rfl
    have rawChosen : finalAction ∈ (rawMenu.decodeProfile initial horizon scheduler
        assessment.strategy owner (finalCallback.recall owner)
          (finalCallback.observe app owner)).support := by
      rw [← responseLaw, ← selected]
      exact callbackChosen
    have neverWait := raw_clock_three_response_ne_wait assessment equilibrium sourceThree _
      finalCallback owner rfl callbackRequest callbackClock first second wordThree firstRequest
        secondRequest observedClock receipted silent rfl zero
    have nonsilent : finalAction.transmission ≠ none := by
      intro empty
      have actionEq : finalAction = (⟨none⟩ : app.Action) := by
        have eta : finalAction = ⟨finalAction.transmission⟩ := by cases finalAction; rfl
        exact eta.trans (congrArg ReactiveApplication.Action.mk empty)
      rw [actionEq] at rawChosen
      exact neverWait rawChosen
    obtain ⟨material, sent⟩ := Option.ne_none_iff_exists'.mp nonsilent
    obtain ⟨emitted, recalled⟩ := app.respond_recall_entry finalCallback owner finalAction
    let entry : app.PlayerEntry := ⟨finalCallback.observe app owner, finalAction, emitted⟩
    rw [laterEq] at tail
    have member : entry ∈ final.recall owner :=
      (rounds_recall_retained (family seed) players _ _ final tail owner).subset (by
        rw [recalled]
        exact List.mem_append_right _ (List.mem_singleton_self _))
    have validThree := raw_native_valid (family seed) _
      (countedMenu.toRawTrace initial horizon (family seed) callbackTrace)
    have entryRequest : PhaseRuntimeState.requests entry.beforeView.application.2 owner
        (originalCoordinate owner) :=
      (finalCallback.application.requests_publicView validThree owner
        (originalCoordinate owner)).mpr
        callbackRequest
    have emittedClock := original_recorded_transmission_clock seed 0 final finalTrace owner entry
      member entryRequest material sent 3 callbackClock
    apply (original_binding_accepted_iff_clocks seed _ finalTrace owner resolved).mpr
    right
    rw [bad]
    exact emittedClock
  · obtain ⟨material, sent⟩ := Option.ne_none_iff_exists'.mp silent
    apply (original_binding_accepted_iff_clocks seed _ finalTrace owner resolved).mpr
    exact Or.inl (original_recorded_transmission_clock seed 0 final finalTrace owner first
      firstMember firstRequest material sent 0 zero)

end Vegas.Examples.CommitSeedBroadcast
