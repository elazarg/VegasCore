/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperProperResponse
import Vegas.Examples.CommitSeedSignallingHelperSafeValue
import Vegas.Examples.CommitSeedSignallingHelperWaitedCallback

/-! # Entire native futures of the seed-informed proper comparator -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- The known seed bit selects an ordinary whole policy at the real clock-two
input. Its current response and every subsequent callback are evaluated under
the same original timing seed and opposing kernels. -/
theorem helper_clock_two_proper_rule_future_outcome (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (mixed : rawProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (known : Bool) (bit : seedBits seed alice = known)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (input : marker ∈ execution.network.inputs) (sender : marker.sender = bob)
    (identified : marker.id = (bob, 0)) (permitted : PhaseCount.permits [] marker = true)
    (bobAccepted : known = true → PhaseService.BindingAccepted runtime leaks
      (originalCoordinate bob) bob execution)
    (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view)
    (proper : players alice = properPolicy (helperTimingRule known) alice)
    (action : app.Action)
    (supported : action ∈ (players alice (execution.recall alice)
      (execution.observe app alice)).support)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining
      (execution.respond app alice action)).support) :
    alice ∉ final.application.current.excluded ∧ 0 ≤ netPayoff (app.finished final) alice := by
  cases known with
  | false =>
      obtain ⟨serial, _bounded, response, _slot, fresh, _result⟩ :=
        helper_eligible_proper_response seed remaining execution fixed request false clock quiet
          (fun impossible => by cases impossible)
      have chosen := supported
      rw [proper, response] at chosen
      have same := (PMF.mem_support_pure_iff _ _).mp chosen
      subst action
      let material : WitnessedSubmission graph :=
        ⟨⟨.commitment (bindingEvent alice) (alice, .prepared serial), some ⟨.bool, true⟩⟩, .none⟩
      have literal : phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool
          (.success true) serial = (⟨some material⟩ : app.Action) := rfl
      have offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
          (execution.recall alice) (execution.observe app alice) := by
        exact properPolicy_counted (helperTimingRule false) alice (execution.recall alice)
          (execution.observe app alice) ⟨some material⟩ (by
            rw [response, literal]
            exact (PMF.mem_support_pure_iff _ _).mpr rfl)
      have declared : (⟨some material⟩ : app.Action) =
          phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool
            (.success true) serial := literal.symm
      have sourceFresh : (execution.observe app alice).application.1.candidates
          (.prepared serial) = .fresh := fresh
      rw [literal] at reached
      exact helper_clock_two_proper_future_outcome seed remaining execution mixed fixed bit request
        clock quiet marker input sender identified permitted material offered serial declared
          sourceFresh (helperTimingRule false) players covered proper final reached
  | true =>
      have response := helper_clock_two_proper_wait seed remaining execution fixed request clock
      have chosen := supported
      rw [proper, response] at chosen
      have same := (PMF.mem_support_pure_iff _ _).mp chosen
      subst action
      have rawFixed := countedInRaw.trace initial horizon (family seed) fixed
      have empty := alice_clock_two_initial_wait_outputs_empty seed remaining execution rawFixed
        request clock quiet
      have unsent : ∀ message ∈ app.outputs (execution.recall alice),
          PhaseCount.event? message.payload ≠ some (originalCoordinate alice) := by
        rw [empty]
        exact fun _ member => (List.not_mem_nil member).elim
      have indexed := original_first_late_input_index seed ⟨remaining, some alice, execution⟩
        rawFixed alice rfl request.1.symm clock
      change execution.environmentRecall.length = 4 + if seedBits seed alice then 3 else 1
        at indexed
      rw [bit] at indexed
      have accounted := (countedMenu.roundSupported_uniform initial horizon (family seed) fixed).1
      have enough : 3 ≤ remaining := by
        change execution.environmentRecall.length + remaining = 64 at accounted
        simp only [ite_true] at indexed
        omega
      rw [show remaining = 3 + (remaining - 3) by omega, app.runRounds_add,
        PMF.support_bind] at reached
      obtain ⟨next, firstReached, tailReached⟩ := Set.mem_iUnion₂.mp reached
      obtain ⟨_before, observed, nextAction, _beforeReached, _observedEq, _nextCommand,
          ⟨observedTrace⟩,
          requestThree, clockThree, positionThree, recallThree, receiptThree, actionThree,
            afterThree⟩ := helper_wait_reaches_clock_three seed remaining execution fixed bit
        request clock unsent (bobAccepted rfl) players covered next firstReached
      have quietThree : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ observed.recall alice := by
        rw [recallThree, respond_originalResponseEntry]
        exact List.mem_append_left _ quiet
      let helper := originalResponseEntry execution alice ⟨none⟩
      have remembered : helper ∈ observed.recall alice := by
        rw [recallThree, respond_originalResponseEntry]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      have helperClock : helper.beforeView.application.2.native.clock = 2 := clock
      obtain ⟨serial, _bounded, sendThree, _slot, fresh, _result⟩ :=
        helper_eligible_proper_response seed (remaining - 3) observed observedTrace requestThree
          true clockThree quietThree (fun _ => ⟨helper, remembered, helperClock, rfl⟩)
      rw [proper, sendThree] at actionThree
      have same := (PMF.mem_support_pure_iff _ _).mp actionThree
      subst nextAction
      subst next
      let material : WitnessedSubmission graph :=
        ⟨⟨.commitment (bindingEvent alice) (alice, .prepared serial), some ⟨.bool, true⟩⟩, .none⟩
      have literal : phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool
          (.success true) serial = (⟨some material⟩ : app.Action) := rfl
      have offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
          (observed.recall alice) (observed.observe app alice) := by
        exact properPolicy_counted (helperTimingRule true) alice (observed.recall alice)
          (observed.observe app alice) ⟨some material⟩ (by
            rw [sendThree, literal]
            exact (PMF.mem_support_pure_iff _ _).mpr rfl)
      have declared : (⟨some material⟩ : app.Action) =
          phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool
            (.success true) serial := literal.symm
      have sourceFresh : (observed.observe app alice).application.1.candidates
          (.prepared serial) = .fresh := fresh
      rw [literal] at tailReached
      exact helper_clock_three_proper_future_outcome seed (remaining - 3) observed observedTrace bit
        requestThree clockThree positionThree receiptThree material offered serial declared
          sourceFresh (helperTimingRule true) players covered proper final tailReached

/-- After the literal clock-two WAIT, the same proper whole comparator chooses
its fresh declaration at the actual clock-three input and survives thereafter. -/
theorem helper_clock_three_proper_rule_future_outcome (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (bit : seedBits seed alice = true)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 3)
    (position : execution.environmentRecall.length = 10)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (helper : app.PlayerEntry) (remembered : helper ∈ execution.recall alice)
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (waited : helper.action.transmission = none)
    (bobAccepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      execution)
    (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view)
    (proper : players alice = properPolicy (helperTimingRule true) alice)
    (action : app.Action)
    (supported : action ∈ (players alice (execution.recall alice)
      (execution.observe app alice)).support)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players remaining
      (execution.respond app alice action)).support) :
    alice ∉ final.application.current.excluded ∧ 0 ≤ netPayoff (app.finished final) alice := by
  obtain ⟨serial, _bounded, response, _slot, fresh, _result⟩ :=
    helper_eligible_proper_response seed remaining execution fixed request true clock quiet
      (fun _ => ⟨helper, remembered, helperClock, waited⟩)
  have chosen := supported
  rw [proper, response] at chosen
  have same := (PMF.mem_support_pure_iff _ _).mp chosen
  subst action
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment (bindingEvent alice) (alice, .prepared serial), some ⟨.bool, true⟩⟩, .none⟩
  have literal : phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool
      (.success true) serial = (⟨some material⟩ : app.Action) := rfl
  have offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (execution.recall alice) (execution.observe app alice) := by
    exact properPolicy_counted (helperTimingRule true) alice (execution.recall alice)
      (execution.observe app alice) ⟨some material⟩ (by
        rw [response, literal]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have declared : (⟨some material⟩ : app.Action) =
      phaseBindingResponse runtime leaks alice (bindingEvent alice) .bool
        (.success true) serial := literal.symm
  have sourceFresh : (execution.observe app alice).application.1.candidates
      (.prepared serial) = .fresh := fresh
  rw [literal] at reached
  exact helper_clock_three_proper_future_outcome seed remaining execution fixed bit request clock
    position bobAccepted material offered serial declared sourceFresh (helperTimingRule true)
      players covered proper final reached
end Vegas.Examples.CommitSeedSignalling
