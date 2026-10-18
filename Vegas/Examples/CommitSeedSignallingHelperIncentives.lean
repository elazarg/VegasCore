/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperBindingChoice
import Vegas.Examples.CommitSeedSignallingHelperUsableWindow
import Vegas.Examples.CommitSeedSignallingHelperSeedSupport
import Vegas.Examples.CommitSeedSignallingPublicationAssessed
import Vegas.Examples.CommitSeedSignallingHelperFirstCallback
import Vegas.Examples.CommitSeedSignallingTimingIncentives

/-! # Actual helper responses and incumbent native survival -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem counted_assessment_finish_law
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (history : countedProtocol.History) :
    app.finish initial horizon scheduler
      (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
        history.state =
      app.finish initial horizon scheduler
        (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) history.state := by
  let fuel := app.rank horizon history.state
  have law := congrArg (fun distribution => distribution.map History.state)
    ((countedInRaw.actionRestriction initial horizon scheduler).runFrom_law
      (countedAssessmentProfile assessment) assessment.strategy
      (raw_equilibrium_extends_counted assessment equilibrium) fuel history)
  rw [PMF.map_comp] at law
  change (countedModel.runBehavioralFrom (countedAssessmentProfile assessment) fuel history).map
      History.state =
    (rawModel.runBehavioralFrom assessment.strategy fuel
      (countedInRaw.history initial horizon scheduler history)).map History.state at law
  rw [countedMenu.run_eq_finish initial horizon scheduler _ fuel history le_rfl,
    rawMenu.run_eq_finish initial horizon scheduler _ fuel
      (countedInRaw.history initial horizon scheduler history) le_rfl] at law
  exact law

/-- After a useful helper declaration has really entered a fresh publication
suffix, every original-seed continuation of the counted incumbent also survives.
The proof transfers the actual physical law back to the assessed raw opponents,
where whole-fiber publication optimality applies. -/
theorem helper_assessed_publication_fixed_future_survives
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, none, execution⟩))
    (supportedSeed : seed ∈ (implementation.posterior execution.environmentRecall).support)
    (tail : execution.application.phases <:+ [publicationPhase])
    (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent alice)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout alice).symm)
        (PublicationResult.success value)))
    (unserved : ∀ entry ∈ execution.recall alice,
      ∀ coordinate : CommitAttemptEvent graph, coordinate.event = revealEvent alice →
        ¬ PhaseRuntimeState.requests entry.beforeView.application.2 alice coordinate)
    (active : alice ∉ execution.application.current.excluded)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed)
      (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
        remaining execution).support) : alice ∉ final.application.current.excluded := by
  let players := countedMenu.decodeProfile initial horizon scheduler
    (countedAssessmentProfile assessment)
  have actual := (helper_fixed_prefix_supported players remaining execution final seed
    supportedSeed reached).1
  let history : countedProtocol.History := ⟨some ⟨remaining, none, execution⟩, trace⟩
  have physical : some (⟨0, none, final⟩ : app.Control) ∈
      (app.finish initial horizon scheduler players history.state).support := by
    change some (⟨0, none, final⟩ : app.Control) ∈ (((PMF.pure execution).bind
      (app.runRounds scheduler players remaining)).map app.finished).support
    rw [PMF.pure_bind]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, actual, rfl⟩
  rw [counted_assessment_finish_law assessment equilibrium history] at physical
  change some (⟨0, none, final⟩ : app.Control) ∈ (((PMF.pure execution).bind
    (app.runRounds scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) remaining)).map
        app.finished).support at physical
  rw [PMF.pure_bind] at physical
  obtain ⟨after, rounds, same⟩ := PMF.support_map .. ▸ physical
  change (some (⟨0, none, after⟩ : app.Control) : app.ProtocolState) =
    some (⟨0, none, final⟩ : app.Control) at same
  have identical : after = final := congrArg (fun control : app.Control => control.execution)
    (Option.some.inj same)
  subst after
  exact assessed_publication_run_survives assessment equilibrium remaining execution trace tail
    alice value stored unserved active final rounds

/-- A literal current response and its original-seed window remain genuine
under the assessed scheduler, with the same seed in the updated posterior. -/
theorem helper_response_prefix_supported (seed : Seeds) (remaining count : Nat)
    (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (supportedSeed : seed ∈ (implementation.posterior execution.environmentRecall).support)
    (action : app.Action)
    (offered : action ∈ countedMenu.actions alice (execution.recall alice)
      (execution.observe app alice))
    (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view)
    (enough : count ≤ remaining) (next : app.Execution)
    (reached : next ∈ (app.runRounds (family seed) players count
      (execution.respond app alice action)).support) :
    Nonempty (countedProtocol.Trace (some ⟨remaining - count, none, next⟩)) ∧
      seed ∈ (implementation.posterior next.environmentRecall).support := by
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon scheduler remaining execution
    alice action trace offered
  have seedAfter : seed ∈ (implementation.posterior
      (execution.respond app alice action).environmentRecall).support := by
    simpa only [app.respond_environmentRecall] using supportedSeed
  obtain ⟨actual, posterior⟩ := helper_fixed_prefix_supported players count
    (execution.respond app alice action) next seed seedAfter reached
  have before : countedProtocol.Trace
      (some ⟨(remaining - count) + count, none, execution.respond app alice action⟩) := by
    rw [Nat.sub_add_cancel enough]
    exact responded
  obtain ⟨nextTrace⟩ := countedMenu.trace_runRounds initial horizon scheduler players covered
    (remaining - count) count (execution.respond app alice action) next before actual
  exact ⟨⟨nextTrace⟩, posterior⟩

/-- A supported usable clock-two declaration survives its entire assessed
future. The actual admitted Bool may be either value; no proper future is imposed. -/
theorem helper_usable_clock_two_future_survives
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (supportedSeed : seed ∈ (implementation.posterior execution.environmentRecall).support)
    (bit : seedBits seed alice = false)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (input : marker ∈ execution.network.inputs) (sender : marker.sender = bob)
    (identified : marker.id = (bob, 0)) (permitted : PhaseCount.permits [] marker = true)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (execution.recall alice) (execution.observe app alice))
    (value : Bool) (usable : (material.call.opening.bind fun raw => raw.as? .bool) = some value)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed)
      (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
        remaining (execution.respond app alice ⟨some material⟩)).support) :
    alice ∉ final.application.current.excluded := by
  let players := countedMenu.decodeProfile initial horizon scheduler
    (countedAssessmentProfile assessment)
  have covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view := by
    intro owner
    exact countedMenu.decode_embedPolicy_covered initial horizon scheduler owner
      (countedAssessmentProfile assessment owner)
  have enough := family_requested_remaining seed ⟨remaining, some alice, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) fixed) (originalCoordinate alice) alice
      request
  change 9 < remaining at enough
  rw [show remaining = 3 + (remaining - 3) by omega, app.runRounds_add,
    PMF.support_bind] at reached
  obtain ⟨next, window, future⟩ := Set.mem_iUnion₂.mp reached
  obtain ⟨_fixedNext, tail, stored, clear, unserved⟩ := helper_clock_two_usable_publication
    seed remaining execution (countedInRaw.trace initial horizon scheduler trace) fixed bit request
      clock quiet marker input sender identified permitted material offered value usable players
        covered next window
  obtain ⟨⟨nextTrace⟩, nextSeed⟩ := helper_response_prefix_supported seed remaining 3 execution
    trace supportedSeed ⟨some material⟩ offered players covered (by omega) next window
  have active : alice ∉ next.application.current.excluded := by rw [clear]; simp
  exact helper_assessed_publication_fixed_future_survives assessment equilibrium seed
    (remaining - 3) next nextTrace nextSeed tail value stored unserved active final future

/-- The actual clock-three usable declaration is followed by the same
assessed publication future after its one real inclusion round. -/
theorem helper_usable_clock_three_future_survives
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (supportedSeed : seed ∈ (implementation.posterior execution.environmentRecall).support)
    (bit : seedBits seed alice = true)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 3)
    (position : execution.environmentRecall.length = 10)
    (bobAccepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      execution)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions alice
      (execution.recall alice) (execution.observe app alice))
    (value : Bool) (usable : (material.call.opening.bind fun raw => raw.as? .bool) = some value)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed)
      (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
        remaining (execution.respond app alice ⟨some material⟩)).support) :
    alice ∉ final.application.current.excluded := by
  let players := countedMenu.decodeProfile initial horizon scheduler
    (countedAssessmentProfile assessment)
  have covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view := by
    intro owner
    exact countedMenu.decode_embedPolicy_covered initial horizon scheduler owner
      (countedAssessmentProfile assessment owner)
  have enough := family_requested_remaining seed ⟨remaining, some alice, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) fixed) (originalCoordinate alice) alice
      request
  change 9 < remaining at enough
  rw [show remaining = 1 + (remaining - 1) by omega, app.runRounds_add,
    PMF.support_bind] at reached
  obtain ⟨next, window, future⟩ := Set.mem_iUnion₂.mp reached
  have round : next ∈ (app.round (family seed) players
      (execution.respond app alice ⟨some material⟩)).support := by
    simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using window
  obtain ⟨_fixedNext, tail, stored, clear, unserved⟩ := helper_clock_three_usable_publication
    seed remaining execution fixed bit request clock position bobAccepted material offered value
      usable players covered next round
  obtain ⟨⟨nextTrace⟩, nextSeed⟩ := helper_response_prefix_supported seed remaining 1 execution
    trace supportedSeed ⟨some material⟩ offered players covered (by omega) next window
  have active : alice ∉ next.application.current.excluded := by rw [clear]; simp
  exact helper_assessed_publication_fixed_future_survives assessment equilibrium seed
    (remaining - 1) next nextTrace nextSeed tail value stored unserved active final future

/-- At the useful second late callback every supported incumbent response
has its actual usable value admitted, then survives under the incumbent future. -/
theorem helper_clock_three_assessed_future_survives
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (supportedSeed : seed ∈ (implementation.posterior execution.environmentRecall).support)
    (bit : seedBits seed alice = true)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 3)
    (position : execution.environmentRecall.length = 10)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (helper : app.PlayerEntry) (remembered : helper ∈ execution.recall alice)
    (helperRequest : PhaseRuntimeState.requests helper.beforeView.application.2 alice
      (originalCoordinate alice))
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (waited : helper.action.transmission = none)
    (marker : Message Player (CommitAttemptPacket graph))
    (sender : marker.sender = bob) (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ helper.beforeView.messages.leaked ∨
      marker ∈ helper.beforeView.messages.ledger)
    (receipted : ∃ accepted, (marker.id, accepted) ∈ helper.beforeView.receipts)
    (bobAccepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob
      execution)
    (action : app.Action)
    (chosen : action ∈ (countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment) alice (execution.recall alice)
        (execution.observe app alice)).support)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed)
      (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
        remaining (execution.respond app alice action)).support) :
    alice ∉ final.application.current.excluded := by
  let source : countedProtocol.History := ⟨some ⟨remaining, some alice, execution⟩, trace⟩
  obtain ⟨material, value, transmitted, offered, usable⟩ :=
    helper_eligible_counted_response_usable_at_source assessment equilibrium source remaining
      execution rfl request true clock quiet helper (Or.inl remembered) helperRequest helperClock
        (fun _ => waited) marker sender addressed visible
          ⟨fun _ => rfl, fun _ => receipted⟩
          action chosen
  have literal : action = (⟨some material⟩ : app.Action) := by
    cases action
    exact congrArg ReactiveApplication.Action.mk transmitted
  subst action
  exact helper_usable_clock_three_future_survives assessment equilibrium seed remaining execution
    trace fixed supportedSeed bit request clock position bobAccepted material offered value usable
      final reached

/-- The incumbent survives from the first helper callback on each supported
original seed. When the first late slot is wrong, its literal WAIT leads to the
real second callback and preserves both the old own word and the original seed. -/
theorem helper_clock_two_assessed_future_survives
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, some alice, execution⟩))
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (supportedSeed : seed ∈ (implementation.posterior execution.environmentRecall).support)
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (marker : Message Player (CommitAttemptPacket graph))
    (input : marker ∈ execution.network.inputs) (sender : marker.sender = bob)
    (addressed : marker.payload.attempt = originalAttempt)
    (visible : marker ∈ (execution.observe app alice).messages.leaked ∨
      marker ∈ (execution.observe app alice).messages.ledger)
    (action : app.Action)
    (chosen : action ∈ (countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment) alice (execution.recall alice)
        (execution.observe app alice)).support)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed)
      (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
        remaining (execution.respond app alice action)).support) :
    alice ∉ final.application.current.excluded := by
  let players := countedMenu.decodeProfile initial horizon scheduler
    (countedAssessmentProfile assessment)
  have covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view := by
    intro owner
    exact countedMenu.decode_embedPolicy_covered initial horizon scheduler owner
      (countedAssessmentProfile assessment owner)
  let source : countedProtocol.History := ⟨some ⟨remaining, some alice, execution⟩, trace⟩
  have rawFixed := countedInRaw.trace initial horizon (family seed) fixed
  have sourceValid := raw_native_valid scheduler ⟨remaining, some alice, execution⟩
    (countedMenu.toRawTrace initial horizon scheduler trace)
  have publicRequest := (execution.application.requests_publicView sourceValid alice
    (originalCoordinate alice)).mpr request
  have readout := (alice_helper_clock_two_seed seed ⟨remaining, some alice, execution⟩ rawFixed
    rfl request clock marker sender addressed visible).symm
  have position := original_first_late_input_index seed ⟨remaining, some alice, execution⟩
    rawFixed alice rfl request.1.symm clock
  change execution.environmentRecall.length = 4 + if seedBits seed alice then 3 else 1 at position
  have early : execution.environmentRecall.length ≤ 12 := by split_ifs at position <;> omega
  obtain ⟨identified, permitted⟩ := observed_helper_packet_permission seed
    ⟨remaining, some alice, execution⟩ trace rawFixed request early marker input sender
  cases bit : seedBits seed alice with
  | false =>
      let helper := originalResponseEntry execution alice (⟨none⟩ : app.Action)
      obtain ⟨material, value, transmitted, offered, usable⟩ :=
        helper_eligible_counted_response_usable_at_source assessment equilibrium source remaining
          execution rfl request false clock quiet helper (Or.inr rfl) publicRequest clock
            (fun impossible => by cases impossible) marker sender addressed visible
              (by
                change (∃ accepted,
                  (marker.id, accepted) ∈ (execution.observe app alice).receipts) ↔ false = true
                simpa only [bit] using readout) action chosen
      have literal : action = (⟨some material⟩ : app.Action) := by
        cases action
        exact congrArg ReactiveApplication.Action.mk transmitted
      subst action
      exact helper_usable_clock_two_future_survives assessment equilibrium seed remaining execution
        trace fixed supportedSeed bit request clock quiet marker input sender identified permitted
          material offered value usable final reached
  | true =>
      have receipted : ∃ accepted, (marker.id, accepted) ∈ (execution.observe app alice).receipts :=
        readout.mpr bit
      have waitLaw := helper_wrong_slot_counted_decoded_wait_at_source assessment equilibrium
        source remaining execution rfl request clock quiet marker sender addressed visible receipted
      rw [waitLaw] at chosen
      have same := (PMF.mem_support_pure_iff _ _).mp chosen
      subst action
      have empty := alice_clock_two_initial_wait_outputs_empty seed remaining execution rawFixed
        request clock quiet
      have unsent : ∀ message ∈ app.outputs (execution.recall alice),
          PhaseCount.event? message.payload ≠ some (originalCoordinate alice) := by
        rw [empty]
        exact fun _ member => (List.not_mem_nil member).elim
      have bobAccepted := counted_helper_bob_binding_accepted seed
        ⟨remaining, some alice, execution⟩ trace fixed request quiet early
          (by
            change 6 ≤ execution.environmentRecall.length
            rw [bit] at position
            simp only [ite_true] at position
            omega) marker input sender
      have enough := family_requested_remaining seed ⟨remaining, some alice, execution⟩
        (countedMenu.toRawTrace initial horizon (family seed) fixed) (originalCoordinate alice)
          alice request
      change 9 < remaining at enough
      rw [show remaining = 3 + (remaining - 3) by omega, app.runRounds_add,
        PMF.support_bind] at reached
      obtain ⟨next, window, future⟩ := Set.mem_iUnion₂.mp reached
      obtain ⟨before, observed, nextAction, beforeReached, observedEq, command, ⟨observedFixed⟩,
          requestThree, clockThree, positionThree, recallThree, receiptThree, actionThree,
            nextEq⟩ := helper_wait_reaches_clock_three seed remaining execution fixed bit request
        clock unsent bobAccepted players covered next window
      obtain ⟨repliedTrace⟩ := countedMenu.trace_respond initial horizon scheduler remaining
        execution alice ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds alice _ _)
      have repliedSeed : seed ∈ (implementation.posterior
          (execution.respond app alice ⟨none⟩).environmentRecall).support := by
        simpa only [app.respond_environmentRecall] using supportedSeed
      have repliedSource : countedProtocol.Trace
          (some ⟨((remaining - 3) + 1) + 2, none, execution.respond app alice ⟨none⟩⟩) := by
        rw [show (remaining - 3 + 1) + 2 = remaining by omega]
        exact repliedTrace
      obtain ⟨⟨observedTrace⟩, observedSeed⟩ := helper_fixed_activation_counted_trace seed
        (remaining - 3) 2 (execution.respond app alice ⟨none⟩) repliedSource repliedSeed players
          covered before beforeReached alice (by
            rw [command]
            exact (PMF.mem_support_pure_iff _ _).mpr rfl)
      rw [← observedEq] at observedTrace observedSeed
      have quietThree : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ observed.recall alice := by
        rw [recallThree, respond_originalResponseEntry]
        exact List.mem_append_left _ quiet
      let helper := originalResponseEntry execution alice (⟨none⟩ : app.Action)
      have remembered : helper ∈ observed.recall alice := by
        rw [recallThree, respond_originalResponseEntry]
        exact List.mem_append_right _ (List.mem_singleton_self _)
      subst next
      exact helper_clock_three_assessed_future_survives assessment equilibrium seed
        (remaining - 3) observed observedTrace observedFixed observedSeed bit requestThree
          clockThree positionThree quietThree helper remembered publicRequest clock rfl marker
            sender addressed visible receipted receiptThree nextAction actionThree final future

/-- At a genuine idle counted prefix the unchanged raw equilibrium and its
decoded counted restriction have the same physical continuation support. -/
theorem helper_assessed_counted_run_support
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, none, execution⟩))
    (final : app.Execution)
    (reached : final ∈ (app.runRounds scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        remaining execution).support) :
    final ∈ (app.runRounds scheduler
      (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
        remaining execution).support := by
  let history : countedProtocol.History := ⟨some ⟨remaining, none, execution⟩, trace⟩
  have same := counted_assessment_finish_law assessment equilibrium history
  have physical : app.finished final ∈ (app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        history.state).support := by
    change app.finished final ∈ (((PMF.pure execution).bind (app.runRounds scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) remaining)).map
        app.finished).support
    rw [PMF.pure_bind]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨final, reached, rfl⟩
  rw [← same] at physical
  change app.finished final ∈ (((PMF.pure execution).bind (app.runRounds scheduler
    (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
      remaining)).map app.finished).support at physical
  rw [PMF.pure_bind] at physical
  obtain ⟨next, supported, identical⟩ := PMF.support_map .. ▸ physical
  change (some (⟨0, none, next⟩ : app.Control) : app.ProtocolState) =
    some (⟨0, none, final⟩ : app.Control) at identical
  have sameExecution : next = final := congrArg (fun control : app.Control => control.execution)
    (Option.some.inj identical)
  subst next
  exact supported

/-- Sending any admitted early Bob packet supplies the helper. Alice's
actual assessed strategy survives on every continuation, including continuations
from the forced initial WAIT outside the incumbent's support. -/
theorem bobQuiet_counted_transmission_alice_survives
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (material : app.Submission)
    (allowed : (⟨some material⟩ : app.Action) ∈ countedMenu.actions bob []
      ((bobFirst ⟨none⟩).observe app bob))
    (final : app.Execution)
    (reached : final ∈ (app.runRounds scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) 62
        ((bobFirst ⟨none⟩).respond app bob ⟨some material⟩)).support) :
    alice ∉ final.application.current.excluded := by
  let players := countedMenu.decodeProfile initial horizon scheduler
    (countedAssessmentProfile assessment)
  have covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ countedMenu.actions owner past view := by
    intro owner
    exact countedMenu.decode_embedPolicy_covered initial horizon scheduler owner
      (countedAssessmentProfile assessment owner)
  let start := (bobFirst ⟨none⟩).respond app bob ⟨some material⟩
  obtain ⟨quietTrace⟩ := counted_bobQuiet_trace
  have offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions bob
      ((bobFirst ⟨none⟩).recall bob) ((bobFirst ⟨none⟩).observe app bob) := by
    rw [bobFirst_recall]
    exact allowed
  obtain ⟨startTrace⟩ := countedMenu.trace_respond initial horizon scheduler 62 (bobFirst ⟨none⟩)
    bob ⟨some material⟩ quietTrace offered
  have countedReached := helper_assessed_counted_run_support assessment equilibrium 62 start
    startTrace final reached
  have realized := implementation.realize players 62 start
  simp only [implementation, app.schedulerMixture_runJoint, PMF.map_bind,
    PMF.map_comp, Function.comp_def] at realized
  change (implementation.posterior start.environmentRecall).bind (fun seed =>
    (app.runRounds (family seed) players 62 start).map id) =
      app.runRounds scheduler players 62 start at realized
  simp only [PMF.map_id] at realized
  rw [← realized, PMF.support_bind] at countedReached
  obtain ⟨seed, supportedSeed, fixedReached⟩ := Set.mem_iUnion₂.mp countedReached
  let count := 2 + if seedBits seed alice then 2 else 0
  have countBound : count ≤ 4 := by dsimp only [count]; split_ifs <;> omega
  have split : 62 = (count + 1) + (61 - count) := by omega
  rw [split, app.runRounds_add, PMF.support_bind] at fixedReached
  obtain ⟨next, window, future⟩ := Set.mem_iUnion₂.mp fixedReached
  obtain ⟨before, observed, action, marker, beforeReached, observedEq, command, ⟨fixedTrace⟩,
      request, clock, quietWord, markerInput, sender, addressed, visible, chosen, nextEq⟩ :=
    bob_early_first_helper_callback seed material allowed players covered next window
  have initial : countedProtocol.Trace
      (some ⟨((61 - count) + 1) + count, none, start⟩) := by
    rw [show ((61 - count) + 1) + count = 62 by omega]
    exact startTrace
  obtain ⟨⟨mixedTrace⟩, observedSeed⟩ := helper_fixed_activation_counted_trace seed (61 - count)
    count start initial supportedSeed players covered before beforeReached alice (by
      rw [command]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  rw [← observedEq] at mixedTrace observedSeed
  have quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ observed.recall alice := by
    rw [quietWord]
    exact List.mem_singleton_self _
  rw [nextEq] at future
  exact helper_clock_two_assessed_future_survives assessment equilibrium seed (61 - count)
    observed mixedTrace fixedTrace observedSeed request clock quiet marker markerInput sender
      addressed visible action chosen final future

end Vegas.Examples.CommitSeedSignalling
