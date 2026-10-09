/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLatePrefixKernel
import Vegas.Examples.LateOpeningRuntimeAliceFirstWitness
import Vegas.Examples.LateOpeningRuntimeProtectedOpening

/-! # The actual final sender law after an early silent receiver response

Every raw first sender response is retained. After Bob's actual early silence,
the author service waits, the clock advances, and Alice is activated without
foreign pending packets. Her original response law then enters the exact
all-identifier lottery, expiry and final Bob observation kernel.

The genuine-first, silent-retry case has exactly one canonical opening packet;
its inclusion lottery is the existing probability weight/(1+weight). The
first-silent case keeps Alice's entire raw final response law.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeLateResponseKernel

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLateAcceptance LateOpeningRuntimeAliceFirstWitness
  LateOpeningRuntimeLatePrefixKernel LateOpeningRuntimeBobBindingService

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def firstSent (bit : Bool) (label : Fin 3) (response : app.Action) : app.Execution :=
  (firstLateDecision bit label).respond app alice response

def earlyQuiet (bit : Bool) (label : Fin 3) (response : app.Action)
    (selected : Finset (MessageId Player)) : app.Execution :=
  ((firstSent bit label response).sampledActivation app bob selected).respond app bob ⟨none⟩

def finalDecision (bit : Bool) (label : Fin 3) (response : app.Action)
    (selected : Finset (MessageId Player)) : app.Execution :=
  let early := earlyQuiet bit label response selected
  let waited := recorded early .wait early.application
  let ticked := clocked waited
  recorded ticked (.activate alice) ticked.application

theorem early_cursor (bit : Bool) (label : Fin 3) (response : app.Action)
    (selected : Finset (MessageId Player)) :
    (earlyQuiet bit label response selected).environmentRecall.length = 5 := by
  rw [earlyQuiet, app.respond_environmentRecall]
  change ((firstSent bit label response).environmentRecall ++ [_]).length = 5
  rw [List.length_append, List.length_singleton, firstSent, app.respond_environmentRecall]
  rfl

private theorem early_latestBob (bit : Bool) (label : Fin 3) (response : app.Action)
    (selected : Finset (MessageId Player)) :
    latestAuthor bob ((earlyQuiet bit label response selected).observeEnvironment app) = .wait := by
  rcases response with ⟨transmission⟩
  cases transmission <;> rfl

private theorem final_foreign_empty (bit : Bool) (label : Fin 3) (response : app.Action)
    (selected : Finset (MessageId Player)) :
    foreignPending alice (earlyQuiet bit label response selected).network.pending = ∅ := by
  rcases response with ⟨transmission⟩
  cases transmission <;> rfl

theorem final_cursor (bit : Bool) (label : Fin 3) (response : app.Action)
    (selected : Finset (MessageId Player)) :
    (finalDecision bit label response selected).environmentRecall.length = 8 := by
  simp only [finalDecision, clocked, recorded, List.length_append, List.length_singleton,
    early_cursor]

/-- The exact last Alice response law is evaluated at her unchanged raw
private recall, including any alias used for her first submission. -/
theorem final_decision_rounds (bit : Bool) (label : Fin 3) (response : app.Action)
    (selected : Finset (MessageId Player)) (players : Player → app.Policy) :
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 3
      (earlyQuiet bit label response selected) =
        app.invoke players alice (finalDecision bit label response selected) := by
  let early := earlyQuiet bit label response selected
  let waited := recorded early .wait early.application
  let ticked := clocked waited
  let activated := recorded ticked (.activate alice) ticked.application
  have earlyCursor : early.environmentRecall.length = 5 := early_cursor bit label response selected
  have waitCursor : waited.environmentRecall.length = 6 := by
    change (early.environmentRecall ++ [_]).length = 6
    rw [List.length_append, List.length_singleton, earlyCursor]
  have tickCursor : ticked.environmentRecall.length = 7 := by
    change (waited.environmentRecall ++ [_]).length = 7
    rw [List.length_append, List.length_singleton, waitCursor]
  have first : app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players early =
      PMF.pure waited := by
    rw [fixed_round weight nonnegative players early waited 5 .wait earlyCursor
      (by
        change PMF.pure (latestAuthor bob _) = PMF.pure .wait
        rw [early_latestBob]) (recorded_wait early)]
    rfl
  have second : app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players waited =
      PMF.pure ticked :=
    (fixed_round weight nonnegative players waited ticked 6 (.application .advanceClock)
      waitCursor rfl (recorded_clock waited)).trans rfl
  have foreign : foreignPending alice ticked.network.pending = ∅ :=
    final_foreign_empty bit label response selected
  have third : app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players ticked =
      app.invoke players alice activated := by
    rw [fixed_round weight nonnegative players ticked activated 7 (.activate alice)
      tickCursor rfl (recorded_activation ticked alice foreign)]
    rfl
  rw [ReactiveApplication.runRounds, first, PMF.pure_bind,
    ReactiveApplication.runRounds, second, PMF.pure_bind,
    ReactiveApplication.runRounds, third]
  change (app.invoke players alice activated).bind PMF.pure = _
  rw [PMF.bind_pure]
  rfl

def finalResponses (bit : Bool) (label : Fin 3) (response : app.Action)
    (selected : Finset (MessageId Player)) (players : Player → app.Policy) : PMF app.Action :=
  players alice ((finalDecision bit label response selected).recall alice)
    ((finalDecision bit label response selected).observe app alice)

def finalResponseLaw (bit : Bool) (label : Fin 3) (response : app.Action)
    (selected : Finset (MessageId Player)) (players : Player → app.Policy) : PMF app.Execution :=
  (finalResponses bit label response selected players).bind fun action =>
    settlementKernel weight nonnegative
      ((finalDecision bit label response selected).respond app alice action)

/-- All raw final responses and every original player policy are retained
in the complete physical continuation after the actual early quiet response. -/
theorem after_early_quiet_law (bit : Bool) (label : Fin 3) (response : app.Action)
    (selected : Finset (MessageId Player)) (players : Player → app.Policy) :
    afterEarly weight nonnegative players (earlyQuiet bit label response selected) =
      finalResponseLaw weight nonnegative bit label response selected players := by
  unfold afterEarly
  rw [show 6 = 3 + 3 from rfl, ReactiveApplication.runRounds_add,
    final_decision_rounds weight nonnegative, PMF.bind_bind]
  unfold ReactiveApplication.invoke finalResponseLaw finalResponses
  rw [PMF.bind_map]
  apply bind_congr_on_support
  intro action _
  simp only [Function.comp_apply]
  exact settlement_activation weight nonnegative players _
    (by rw [app.respond_environmentRecall, final_cursor])

private theorem silent_first_round (bit : Bool) (label : Fin 3)
    (players : Player → app.Policy) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
        (firstSent bit label ⟨none⟩) =
      app.invoke players bob ((firstSent bit label ⟨none⟩).sampledActivation app bob ∅) := by
  let execution := firstSent bit label ⟨none⟩
  let activated := recorded execution (.activate bob) execution.application
  have moved := recorded_activation execution bob (by rfl)
  rw [fixed_round weight nonnegative players execution activated 4 (.activate bob)
    rfl rfl moved]
  simp only [ReactiveApplication.Execution.sampledActivation, MessageNetwork.learn_empty]
  rfl

/-- The actual silent first response retains Bob's original policy at the
empty sample, without assigning a new observation or changing player menus. -/
theorem silent_first_binding_law (bit : Bool) (label : Fin 3)
    (players : Player → app.Policy) :
    firstBindingLaw weight nonnegative (decisionHistory weight nonnegative bit label)
        ⟨none⟩ players =
      (app.invoke players bob ((firstSent bit label ⟨none⟩).sampledActivation app bob ∅)).bind
        (afterEarly weight nonnegative players) := by
  unfold firstBindingLaw
  change ((app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 7
    (firstSent bit label ⟨none⟩)).bind _ ) = _
  rw [ReactiveApplication.runRounds, PMF.bind_bind, silent_first_round weight nonnegative]
  rfl

/-- The silent-first path keeps the entire original raw final response law
and the exact original early receiver silence multiplier. -/
theorem silent_first_silent_event_probability (bit : Bool) (label : Fin 3)
    (players : Player → app.Policy) (event : Set app.Execution)
    (quiet : ∀ final ∈ event, SilentRecall final) :
    ((firstBindingLaw weight nonnegative (decisionHistory weight nonnegative bit label)
      ⟨none⟩ players).toOuterMeasure event).toReal =
        (players bob (((firstSent bit label ⟨none⟩).sampledActivation app bob ∅).recall bob)
          (((firstSent bit label ⟨none⟩).sampledActivation app bob ∅).observe app bob)
            ⟨none⟩).toReal *
          ((finalResponseLaw weight nonnegative bit label ⟨none⟩ ∅ players).toOuterMeasure
            event).toReal := by
  rw [silent_first_binding_law, early_silence_event_probability weight nonnegative
    players _ event quiet]
  change _ * ((afterEarly weight nonnegative players
    (earlyQuiet bit label ⟨none⟩ ∅)).toOuterMeasure event).toReal = _
  rw [after_early_quiet_law weight nonnegative]

theorem final_pending (bit : Bool) (label : Fin 3) (response : app.Action)
    (selected : Finset (MessageId Player)) :
    (finalDecision bit label response selected).network.pending =
      (firstSent bit label response).network.pending := rfl

/-- Genuine first submissions may use arbitrary private raw aliases. -/
theorem genuine_first_pending (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (decisionHistory weight nonnegative bit label) submission)
    (selected : Finset (MessageId Player)) :
    ((finalDecision bit label ⟨some submission⟩ selected).respond app alice
      ⟨none⟩).network.pending =
      [openingMessage bit] := by
  change (finalDecision bit label ⟨some submission⟩ selected).network.pending = _
  rw [final_pending]
  have pending := LateOpeningRuntimeFirstObservation.submitted_pending weight nonnegative
    (decisionHistory weight nonnegative bit label) submission
  change (firstSent bit label ⟨some submission⟩).network.pending = [_] at pending
  rw [pending]
  change [(⟨(alice, 0), app.packet (app.submit (firstLateDecision bit label).application alice
    submission) alice ((firstLateDecision bit label).network.known alice) submission⟩ :
      Message Player app.Payload)] = _
  change app.packet (app.submit (firstLateDecision bit label).application alice submission) alice
    ((firstLateDecision bit label).network.known alice) submission =
      (openingMessage bit).payload at genuine
  exact congrArg (fun payload : app.Payload =>
    [(⟨(alice, 0), payload⟩ : Message Player app.Payload)]) genuine

theorem genuine_first_physical (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (decisionHistory weight nonnegative bit label) submission)
    (selected : Finset (MessageId Player)) :
    (finalDecision bit label ⟨some submission⟩ selected).application =
      { initialPhysical bit label with clock := 2 } := by
  change { app.submit (firstLateDecision bit label).application alice submission with
    clock := (app.submit (firstLateDecision bit label).application alice submission).clock + 1 } = _
  have unchanged := LateOpeningRuntimeAliceFirstDecision.opening_submission_unchanged
    weight nonnegative (decisionHistory weight nonnegative bit label) submission genuine
  change app.submit (firstLateDecision bit label).application alice submission =
    (firstLateDecision bit label).application at unchanged
  rw [unchanged]
  rfl

/-- The included canonical packet really publishes the initialized bit.
The proof uses the actual handler and immutable store through expiry. -/
theorem genuine_retry_included_publication (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (decisionHistory weight nonnegative bit label) submission)
    (selected : Finset (MessageId Player)) (final : app.Execution)
    (reached : final ∈ (settled
      ((finalDecision bit label ⟨some submission⟩ selected).respond app alice ⟨none⟩)
        (some (alice, 0))).support) :
    final.application.config.store (.inr aliceEvent) = some (.success bit) := by
  let execution := (finalDecision bit label ⟨some submission⟩ selected).respond app alice ⟨none⟩
  have pending := genuine_first_pending weight nonnegative bit label submission genuine selected
  have physical : execution.application = { initialPhysical bit label with clock := 2 } :=
    genuine_first_physical weight nonnegative bit label submission genuine selected
  have found : execution.network.lookup (alice, 0) = some (openingMessage bit) := by
    rw [MessageNetwork.lookup, pending]
    rfl
  have handled : app.handle execution.application (openingMessage bit) =
      some (openedPhysical bit label) := by
    have original := handle_late_opening bit label 0 false
    rw [beforeLottery_physical] at original
    rwa [physical]
  have included : (lotteryOutcome execution (some (alice, 0))).application =
      openedPhysical bit label := by
    change (execution.includePending app (alice, 0)).application = _
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [found]
    change (app.handle execution.application (openingMessage bit)).getD execution.application = _
    rw [handled]
    rfl
  have stored : (clocked (lotteryOutcome execution (some (alice, 0)))).application.config.store
      (.inr aliceEvent) = some (.success bit) := by
    change (lotteryOutcome execution (some (alice, 0))).application.config.store
      (.inr aliceEvent) = _
    rw [included, openedPhysical_bit]
  exact (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr aliceEvent)
    (.success bit)).environmentStep _ final (.application (.expire aliceEvent)) stored reached

/-- The outside lottery outcome really expires the initialized publication;
no player action occurs between that omission and expiry. -/
theorem genuine_retry_omitted_publication (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (decisionHistory weight nonnegative bit label) submission)
    (selected : Finset (MessageId Player)) (final : app.Execution)
    (reached : final ∈ (settled
      ((finalDecision bit label ⟨some submission⟩ selected).respond app alice ⟨none⟩)
        none).support) :
    final.application.config.store (.inr aliceEvent) =
      some (.failure : PublicationResult Bool) := by
  let execution := (finalDecision bit label ⟨some submission⟩ selected).respond app alice ⟨none⟩
  let ticked := clocked (lotteryOutcome execution none)
  have physical : ticked.application = { initialPhysical bit label with clock := 3 } := by
    change { execution.application with clock := execution.application.clock + 1 } = _
    have previous := genuine_first_physical weight nonnegative bit label submission genuine selected
    change execution.application = _ at previous
    rw [previous]
  have ready : ticked.application.config.cut.Ready aliceEvent := by
    rw [physical]
    change aliceEvent ∉ (∅ : Finset nativeGraph.EventId) ∧
      nativeGraph.order.predecessors aliceEvent ⊆ ∅
    decide
  have activated : ticked.application.activatedAt aliceEvent = some 0 := by
    rw [physical]
    rfl
  have clock : ticked.application.clock = 3 := by rw [physical]
  change final ∈ (ticked.environmentStep app (.application (.expire aliceEvent))).support at reached
  rw [LateOpeningRuntimeProtectedOpening.expired_environment ticked ready activated clock]
    at reached
  cases (PMF.mem_support_pure_iff _ _).mp reached
  exact LateOpeningRuntimeProtectedOpening.expired_store ticked ready

/-- After a genuine first packet and a silent retry, the actual singleton
lottery supplies both acceptance and omission branches without dropping recall. -/
theorem genuine_retry_silent_kernel (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (decisionHistory weight nonnegative bit label) submission)
    (selected : Finset (MessageId Player)) :
    let execution := (finalDecision bit label ⟨some submission⟩ selected).respond app alice ⟨none⟩
    settlementKernel weight nonnegative execution =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        ((settled execution (some (alice, 0))).bind
          (fun before => before.environmentStep app (.activate bob)))
        ((settled execution none).bind
          (fun before => before.environmentStep app (.activate bob))) := by
  dsimp only
  rw [settlementKernel, genuine_first_pending weight nonnegative bit label submission genuine]
  change (MessageNetwork.chooseWithOutside weight nonnegative {(alice, 0)}).bind _ = _
  rw [MessageNetwork.chooseWithOutside]
  simp only [Finset.card_singleton]
  rw [MessageNetwork.chooseUniform_singleton, mix_bind, PMF.pure_bind, PMF.pure_bind]

private theorem genuine_retry_branch_publication (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (decisionHistory weight nonnegative bit label) submission)
    (selected : Finset (MessageId Player)) (included : Bool) (final : app.Execution)
    (reached : final ∈ ((settled
      ((finalDecision bit label ⟨some submission⟩ selected).respond app alice ⟨none⟩)
        (if included then some (alice, 0) else none)).bind
          (fun before => before.environmentStep app (.activate bob))).support) :
    final.application.config.store (.inr aliceEvent) =
      some (if included then .success bit else (.failure : PublicationResult Bool)) := by
  obtain ⟨before, settled, activated⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  have publication : before.application.config.store (.inr aliceEvent) =
      some (if included then .success bit else (.failure : PublicationResult Bool)) := by
    cases included
    · exact genuine_retry_omitted_publication weight nonnegative bit label submission genuine
        selected before settled
    · exact genuine_retry_included_publication weight nonnegative bit label submission genuine
        selected before settled
  exact (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks (.inr aliceEvent)
    (if included then .success bit else (.failure : PublicationResult Bool))).environmentStep
      before final (.activate bob) publication activated

private theorem genuine_retry_branch_law (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (decisionHistory weight nonnegative bit label) submission)
    (selected : Finset (MessageId Player)) (included : Bool) :
    (((settled
      ((finalDecision bit label ⟨some submission⟩ selected).respond app alice ⟨none⟩)
        (if included then some (alice, 0) else none)).bind
          (fun before => before.environmentStep app (.activate bob))).map
            (fun final => final.application.config.store (.inr aliceEvent))) =
      PMF.pure (some (if included then .success bit else (.failure : PublicationResult Bool))) := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro value supported
  obtain ⟨final, reached, rfl⟩ := PMF.support_map .. ▸ supported
  exact genuine_retry_branch_publication weight nonnegative bit label submission genuine
    selected included final reached

/-- The exact typed publication law holds for all genuine private first
submission aliases, independently of the receiver's earlier sample. -/
theorem genuine_retry_publication_law (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (decisionHistory weight nonnegative bit label) submission)
    (selected : Finset (MessageId Player)) :
    ((settlementKernel weight nonnegative
      ((finalDecision bit label ⟨some submission⟩ selected).respond app alice ⟨none⟩)).map
        (fun final => final.application.config.store (.inr aliceEvent))) =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure (some (.success bit))) (PMF.pure (some (.failure : PublicationResult Bool))) := by
  rw [genuine_retry_silent_kernel weight nonnegative bit label submission genuine selected, mix_map]
  have accepted := genuine_retry_branch_law weight nonnegative bit label submission genuine
    selected true
  have omitted := genuine_retry_branch_law weight nonnegative bit label submission genuine
    selected false
  simpa only [Bool.false_eq_true, ↓reduceIte] using
    congrArg₂ (mix (inclusionProbability weight)
      (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
      (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le) accepted omitted

end Vegas.Examples.LateOpeningRuntimeLateResponseKernel
