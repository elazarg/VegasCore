/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLateResponseKernel
import Vegas.Examples.LateOpeningRuntimeAliceEmptyWitness
import Vegas.Examples.LateOpeningRuntimeAliceOpeningAliases

/-! # Receiver information after the actual late opening lottery

The projection retains Bob's entire remembered transcript and current native
view. Genuine raw submission aliases remain distinct in the original histories;
only their observations by Bob are equal. Included openings publish their bit.
Omitted openings can remain in pending-message knowledge, and the final fair
sample can disclose an opening missed by the earlier sample.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBindingObservation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeLateAcceptance LateOpeningRuntimeProtectedOpening
  LateOpeningRuntimeLatePrefixKernel LateOpeningRuntimeLateResponseKernel

abbrev BobInformation := List app.PlayerEntry × app.PlayerView

def bobInformation (execution : app.Execution) : BobInformation :=
  (execution.recall bob, execution.observe app bob)

theorem bobInformation_eraseRecall (execution : app.Execution) :
    bobInformation (execution.eraseRecall app alice) = bobInformation execution := by
  unfold bobInformation
  rw [app.eraseRecall_recall_other execution alice bob (by decide), app.eraseRecall_observe]

private theorem erased_clocked (execution : app.Execution) :
    (clocked execution).eraseRecall app alice = clocked (execution.eraseRecall app alice) := rfl

private theorem erased_sampled (execution : app.Execution)
    (selected : Finset (MessageId Player)) :
    (execution.sampledActivation app bob selected).eraseRecall app alice =
      (execution.eraseRecall app alice).sampledActivation app bob selected := rfl

private theorem erased_alice_silence (execution : app.Execution) :
    (execution.respond app alice ⟨none⟩).eraseRecall app alice =
      execution.eraseRecall app alice := by
  simp only [ReactiveApplication.Execution.respond, ReactiveApplication.Execution.eraseRecall]
  congr 1
  funext who
  by_cases owner : who = alice
  · subst who
    simp only [↓reduceIte]
  · simp only [owner, ↓reduceIte]

private def lastActivation (execution : app.Execution) : app.Execution :=
  let waited := recorded execution .wait execution.application
  let ticked := clocked waited
  recorded ticked (.activate alice) ticked.application

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

/-- A genuine first opening emits the same complete packet and leaves the
application unchanged, regardless of its private raw submission syntax. -/
theorem genuine_first_erased (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) :
    (firstSent bit label ⟨some submission⟩).eraseRecall app alice =
      (beforeBob bit label 0).eraseRecall app alice := by
  have unchanged := LateOpeningRuntimeAliceFirstDecision.opening_submission_unchanged
    weight nonnegative (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative
      bit label) submission genuine
  change app.submit (firstLateDecision bit label).application alice submission =
    (firstLateDecision bit label).application at unchanged
  change app.packet (app.submit (firstLateDecision bit label).application alice submission) alice
    ((firstLateDecision bit label).network.known alice) submission =
      (openingMessage bit).payload at genuine
  rw [unchanged] at genuine
  have canonical : app.packet (firstLateDecision bit label).application alice
      ((firstLateDecision bit label).network.known alice)
        (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩)) =
          (openingMessage bit).payload := firstLate_opening_packet bit label
  have canonicalUnchanged : app.submit (firstLateDecision bit label).application alice
      (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩)) =
        (firstLateDecision bit label).application := rfl
  change ((firstLateDecision bit label).respond app alice ⟨some submission⟩).eraseRecall
    app alice = ((firstLateDecision bit label).respond app alice
      ⟨some (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩))⟩).eraseRecall
        app alice
  simp only [ReactiveApplication.Execution.respond, unchanged, canonicalUnchanged,
    canonical, genuine,
    ReactiveApplication.Execution.eraseRecall]
  congr 1
  funext who
  by_cases owner : who = alice
  · subst who
    simp only [↓reduceIte]
  · simp only [owner, ↓reduceIte]

/-- Bob's actual early remembered response is preserved across every genuine
first-submission alias, with the chosen pending sample retained. -/
theorem genuine_early_erased (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) (seen : Bool) :
    (earlyQuiet bit label ⟨some submission⟩ (if seen then {(alice, 0)} else ∅)).eraseRecall
        app alice = (bobObserved bit label 0 seen).eraseRecall app alice := by
  unfold earlyQuiet bobObserved
  rw [app.eraseRecall_respond_other _ alice bob (by decide), erased_sampled,
    genuine_first_erased weight nonnegative bit label submission genuine,
    ← erased_sampled, ← app.eraseRecall_respond_other _ alice bob (by decide)]

theorem genuine_retry_erased (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) (seen : Bool) :
    ((finalDecision bit label ⟨some submission⟩
      (if seen then {(alice, 0)} else ∅)).respond app alice ⟨none⟩).eraseRecall app alice =
        (beforeLottery bit label 0 seen).eraseRecall app alice := by
  rw [erased_alice_silence]
  change (lastActivation
    (earlyQuiet bit label ⟨some submission⟩ (if seen then {(alice, 0)} else ∅))).eraseRecall
      app alice = ((secondLateDecision bit label 0 seen).respond app alice ⟨none⟩).eraseRecall
        app alice
  rw [erased_alice_silence]
  change lastActivation ((earlyQuiet bit label ⟨some submission⟩
    (if seen then {(alice, 0)} else ∅)).eraseRecall app alice) =
      lastActivation ((bobObserved bit label 0 seen).eraseRecall app alice)
  exact congrArg lastActivation
    (genuine_early_erased weight nonnegative bit label submission genuine seen)

/-- A genuine final opening following both earlier Alice silences has the
same physical state and full receiver recall as the initialized late witness. -/
theorem genuine_final_erased (bit : Bool) (label : Fin 3) (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceOpeningContinuation.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label)
        submission) :
    ((finalDecision bit label ⟨none⟩ ∅).respond app alice ⟨some submission⟩).eraseRecall
        app alice = (beforeLottery bit label 1 false).eraseRecall app alice := by
  have canonical := LateOpeningRuntimeAliceOpeningContinuation.canonical_emits_opening
    weight nonnegative (LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative
      bit label)
  exact LateOpeningRuntimeAliceOpeningAliases.submitted_erasedRecall_eq weight nonnegative
    (LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label) submission
    (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩)) genuine canonical

private theorem erased_lottery (execution : app.Execution) (selected : Option (MessageId Player)) :
    (lotteryOutcome execution selected).eraseRecall app alice =
      lotteryOutcome (execution.eraseRecall app alice) selected := by
  cases selected with
  | none => rfl
  | some id =>
      simp only [lotteryOutcome, ReactiveApplication.Execution.eraseRecall,
        ReactiveApplication.Execution.includePending, MessageNetwork.includePending]
      cases execution.network.lookup id <;> rfl

def branchLaw (execution : app.Execution) (selected : Option (MessageId Player)) :
    PMF app.Execution :=
  (settled execution selected).bind fun before => before.environmentStep app (.activate bob)

/-- The actual branch law can depend on Alice's private aliases only through
her recall, which Bob does not observe after Alice's final callback. -/
theorem branch_information_eq (first second : app.Execution)
    (same : first.eraseRecall app alice = second.eraseRecall app alice)
    (selected : Option (MessageId Player)) :
    (branchLaw first selected).map bobInformation =
      (branchLaw second selected).map bobInformation := by
  have settledSame : (settled first selected).map (fun next => next.eraseRecall app alice) =
      (settled second selected).map (fun next => next.eraseRecall app alice) := by
    unfold settled
    rw [app.eraseRecall_environmentStep, app.eraseRecall_environmentStep,
      erased_clocked, erased_clocked, erased_lottery, erased_lottery, same]
  have branchSame : (branchLaw first selected).map (fun next => next.eraseRecall app alice) =
      (branchLaw second selected).map (fun next => next.eraseRecall app alice) := by
    unfold branchLaw
    rw [PMF.map_bind, PMF.map_bind]
    simp_rw [app.eraseRecall_environmentStep]
    change (settled first selected).bind
      ((fun execution => execution.environmentStep app (.activate bob)) ∘
        (fun execution => execution.eraseRecall app alice)) =
      (settled second selected).bind
        ((fun execution => execution.environmentStep app (.activate bob)) ∘
          (fun execution => execution.eraseRecall app alice))
    rw [← PMF.bind_map, ← PMF.bind_map, settledSame]
  have projected := congrArg (PMF.map bobInformation) branchSame
  simpa only [PMF.map_comp, Function.comp_def, bobInformation_eraseRecall] using projected

theorem genuine_retry_information_law (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceFirstDecision.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        submission) (seen : Bool) (selected : Option (MessageId Player)) :
    (branchLaw ((finalDecision bit label ⟨some submission⟩
      (if seen then {(alice, 0)} else ∅)).respond app alice ⟨none⟩) selected).map bobInformation =
        (branchLaw (beforeLottery bit label 0 seen) selected).map bobInformation :=
  branch_information_eq _ _ (genuine_retry_erased weight nonnegative bit label submission
    genuine seen) selected

theorem genuine_final_information_law (bit : Bool) (label : Fin 3)
    (submission : app.Submission)
    (genuine : LateOpeningRuntimeAliceOpeningContinuation.EmitsOpening weight nonnegative
      (LateOpeningRuntimeAliceEmptyWitness.decisionHistory weight nonnegative bit label)
        submission) (selected : Option (MessageId Player)) :
    (branchLaw ((finalDecision bit label ⟨none⟩ ∅).respond app alice ⟨some submission⟩)
      selected).map bobInformation =
        (branchLaw (beforeLottery bit label 1 false) selected).map bobInformation :=
  branch_information_eq _ _ (genuine_final_erased weight nonnegative bit label submission
    genuine) selected

theorem included_branch_law (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    branchLaw (beforeLottery bit label slot seen) (some (alice, 0)) =
      PMF.pure (answerDecision bit label slot seen) := by
  have completed : aliceEvent ∈
      (clocked (acceptedLottery bit label slot seen)).application.config.cut.completed := by
    change aliceEvent ∈ (acceptedLottery bit label slot seen).application.config.cut.completed
    rw [acceptedLottery_physical]
    exact openedPhysical_done bit label
  have settlement : settled (beforeLottery bit label slot seen) (some (alice, 0)) =
      PMF.pure (beforeAnswer bit label slot seen) := by
    unfold settled
    change (clocked (acceptedLottery bit label slot seen)).environmentStep app
      (.application (.expire aliceEvent)) = _
    have environment : app.environment (clocked (acceptedLottery bit label slot seen)).application
        (.expire aliceEvent) =
          PMF.pure (clocked (acceptedLottery bit label slot seen)).application :=
      environmentStep_expire_of_not_ready LateOpeningRuntimeService.runtime _ aliceEvent
        (fun ready => ready.1 completed)
    simp only [ReactiveApplication.Execution.environmentStep]
    rw [environment, PMF.pure_map, PMF.pure_map]
    rfl
  rw [branchLaw, settlement, PMF.pure_bind, answerDecision_activation]

theorem included_information_law (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (branchLaw (beforeLottery bit label slot seen) (some (alice, 0))).map bobInformation =
      PMF.pure (bobInformation (answerDecision bit label slot seen)) := by
  rw [included_branch_law, PMF.pure_map]

private theorem omitted_ready (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (clocked (omittedLottery bit label slot seen)).application.config.cut.Ready aliceEvent := by
  change (beforeLottery bit label slot seen).application.config.cut.Ready aliceEvent
  rw [beforeLottery_physical]
  change aliceEvent ∉ (∅ : Finset nativeGraph.EventId) ∧
    nativeGraph.order.predecessors aliceEvent ⊆ ∅
  decide

def beforeFailedAnswer (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) : app.Execution :=
  expired (clocked (omittedLottery bit label slot seen)) (omitted_ready bit label slot seen)

def failedAnswerDecision (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool) : app.Execution :=
  (beforeFailedAnswer bit label slot earlySeen).sampledActivation app bob
    (if finalSeen then {(alice, 0)} else ∅)

theorem omitted_settlement (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    settled (beforeLottery bit label slot seen) none =
      PMF.pure (beforeFailedAnswer bit label slot seen) := by
  have physical : (clocked (omittedLottery bit label slot seen)).application =
      { initialPhysical bit label with clock := 3 } := by
    change { (beforeLottery bit label slot seen).application with
      clock := (beforeLottery bit label slot seen).application.clock + 1 } = _
    rw [beforeLottery_physical]
  unfold settled
  exact expired_environment _ (omitted_ready bit label slot seen)
    (by rw [physical]; rfl) (by rw [physical])

theorem omitted_branch_law (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    branchLaw (beforeLottery bit label slot seen) none =
      mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure (failedAnswerDecision bit label slot seen true))
        (PMF.pure (failedAnswerDecision bit label slot seen false)) := by
  have pending : (beforeFailedAnswer bit label slot seen).network.pending = [openingMessage bit] :=
    beforeLottery_pending bit label slot seen
  have foreign : foreignPending bob (beforeFailedAnswer bit label slot seen).network.pending =
      {(alice, 0)} := by rw [pending]; rfl
  have sampled : app.observePending bob (beforeFailedAnswer bit label slot seen).network.pending =
      mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure {(alice, 0)}) (PMF.pure ∅) :=
    LateOpeningRuntimeObservation.leaks_singleton bob _ (alice, 0) foreign
  rw [branchLaw, omitted_settlement, PMF.pure_bind,
    ReactiveApplication.Execution.activation_samples,
    sampled, mix_map, PMF.pure_map, PMF.pure_map]
  rfl

theorem omitted_information_law (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (branchLaw (beforeLottery bit label slot seen) none).map bobInformation =
      mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure (bobInformation (failedAnswerDecision bit label slot seen true)))
        (PMF.pure (bobInformation (failedAnswerDecision bit label slot seen false))) := by
  rw [omitted_branch_law, mix_map, PMF.pure_map, PMF.pure_map]

theorem failedAnswerDecision_recall (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool) :
    (failedAnswerDecision bit label slot earlySeen finalSeen).recall bob =
      (bobObserved bit label slot earlySeen).recall bob := rfl

theorem failedAnswerDecision_network (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool) :
    (failedAnswerDecision bit label slot earlySeen finalSeen).network.observe bob =
      ⟨if finalSeen = true ∨ (earlySeen = true ∧ slot.val = 0)
        then [openingMessage bit] else [], []⟩ := by
  fin_cases slot
  · change (((beforeBob bit label 0).network.learn bob
      (if earlySeen then {(alice, 0)} else ∅)).learn bob
        (if finalSeen then {(alice, 0)} else ∅)).observe bob = _
    rw [beforeBob_first_network]
    cases earlySeen <;> cases finalSeen <;> rfl
  · change ((((MessageNetwork.empty : MessageNetwork Player app.Payload).submit alice
      (app.packet (secondLateDecision bit label 1 earlySeen).application alice []
        (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩)))).2.learn bob
          (if finalSeen then {(alice, 0)} else ∅)).observe bob) = _
    rw [secondLate_opening_packet]
    cases earlySeen <;> cases finalSeen <;> rfl

theorem failedAnswerDecision_receipts (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool) :
    (failedAnswerDecision bit label slot earlySeen finalSeen).receipts = [] := rfl

def failedPhysical (bit : Bool) (label : Fin 3) : app.State :=
  ({ initialPhysical bit label with clock := 3 } : app.State).complete aliceEvent
    (by
      change aliceEvent ∉ (∅ : Finset nativeGraph.EventId) ∧
        nativeGraph.order.predecessors aliceEvent ⊆ ∅
      decide) false (.failure : PublicationResult Bool)

theorem failedAnswerDecision_physical (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool) :
    (failedAnswerDecision bit label slot earlySeen finalSeen).application =
      failedPhysical bit label := by
  change ((clocked (omittedLottery bit label slot earlySeen)).application.complete
    aliceEvent _ false (.failure : PublicationResult Bool)) = _
  have physical : (clocked (omittedLottery bit label slot earlySeen)).application =
      { initialPhysical bit label with clock := 3 } := by
    change { (beforeLottery bit label slot earlySeen).application with
      clock := (beforeLottery bit label slot earlySeen).application.clock + 1 } = _
    rw [beforeLottery_physical]
  simp only [failedPhysical, physical]

theorem failedAnswerDecision_publication (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool) :
    (failedAnswerDecision bit label slot earlySeen finalSeen).application.config.store
      (.inr aliceEvent) = some (.failure : PublicationResult Bool) :=
  expired_store _ (omitted_ready bit label slot earlySeen)

theorem failedAnswerDecision_binding_ready (bit : Bool) (label : Fin 3) (slot : Fin 2)
    (earlySeen finalSeen : Bool) :
    (failedAnswerDecision bit label slot earlySeen finalSeen).application.config.cut.Ready
      bobBindEvent := by
  rw [failedAnswerDecision_physical]
  change bobBindEvent ∉ insert aliceEvent (∅ : Finset nativeGraph.EventId) ∧
    nativeGraph.order.predecessors bobBindEvent ⊆ insert aliceEvent ∅
  decide

/-- Publication failure itself discloses neither initialized bit nor label
in the application view. Pending-message knowledge remains a separate field. -/
theorem failedPhysical_bobView (bit otherBit : Bool) (label otherLabel : Fin 3) :
    (failedPhysical bit label).playerView bob =
      (failedPhysical otherBit otherLabel).playerView bob := by
  have initial : ({ initialPhysical bit label with clock := 3 } : app.State).playerView bob =
      ({ initialPhysical otherBit otherLabel with clock := 3 } : app.State).playerView bob :=
    congrArg (fun view : EventGraphRuntime.PlayerView nativeGraph =>
      { view with publicView := { view.publicView with clock := 3 } })
        (initialBobView bit otherBit label otherLabel)
  exact State.complete_playerView_congr _ _ bob
    (congrArg PlayerView.publicView initial)
    (State.playerView_observation_eq _ _ bob initial)
    (congrArg PlayerView.candidates initial) aliceEvent
    (by
      change aliceEvent ∉ (∅ : Finset nativeGraph.EventId) ∧
        nativeGraph.order.predecessors aliceEvent ⊆ ∅
      decide)
    (by
      change aliceEvent ∉ (∅ : Finset nativeGraph.EventId) ∧
        nativeGraph.order.predecessors aliceEvent ⊆ ∅
      decide) false false (.failure : PublicationResult Bool) (.failure : PublicationResult Bool)
      (fun _ => rfl) (fun _ => rfl)

theorem failed_information_label (bit : Bool) (label otherLabel : Fin 3)
    (slot : Fin 2) (earlySeen finalSeen : Bool) :
    bobInformation (failedAnswerDecision bit label slot earlySeen finalSeen) =
      bobInformation (failedAnswerDecision bit otherLabel slot earlySeen finalSeen) := by
  unfold bobInformation
  apply Prod.ext
  · change (failedAnswerDecision bit label slot earlySeen finalSeen).recall bob =
      (failedAnswerDecision bit otherLabel slot earlySeen finalSeen).recall bob
    rw [failedAnswerDecision_recall, failedAnswerDecision_recall]
    fin_cases slot
    · change (bobObserved bit label 0 earlySeen).recall bob =
        (bobObserved bit otherLabel 0 earlySeen).recall bob
      rw [bobObserved_first_recall, bobObserved_first_recall,
        bobObservationRecord_label bit label otherLabel earlySeen]
    · cases earlySeen <;>
        change [bobObservationRecord bit label false] = [bobObservationRecord bit otherLabel false]
      all_goals rw [bobObservationRecord_label bit label otherLabel false]
  · change (failedAnswerDecision bit label slot earlySeen finalSeen).observe app bob =
      (failedAnswerDecision bit otherLabel slot earlySeen finalSeen).observe app bob
    unfold ReactiveApplication.Execution.observe
    rw [failedAnswerDecision_network, failedAnswerDecision_network,
      failedAnswerDecision_physical, failedAnswerDecision_physical,
      failedAnswerDecision_receipts, failedAnswerDecision_receipts]
    change ReactiveApplication.PlayerView.mk (app := app) _
      ((failedPhysical bit label).playerView bob) _ =
        ReactiveApplication.PlayerView.mk (app := app) _
          ((failedPhysical bit otherLabel).playerView bob) _
    rw [failedPhysical_bobView bit bit label otherLabel]

/-- An unseen first opening and a final opening have identical failed-branch
receiver information for the same final sample, including their earlier record. -/
theorem failed_unseen_timing_information (bit : Bool) (label otherLabel : Fin 3)
    (finalSeen : Bool) :
    bobInformation (failedAnswerDecision bit label 0 false finalSeen) =
      bobInformation (failedAnswerDecision bit otherLabel 1 false finalSeen) := by
  unfold bobInformation
  apply Prod.ext
  · change (failedAnswerDecision bit label 0 false finalSeen).recall bob =
      (failedAnswerDecision bit otherLabel 1 false finalSeen).recall bob
    rw [failedAnswerDecision_recall, failedAnswerDecision_recall,
      unseen_timing_recall bit label otherLabel]
  · change (failedAnswerDecision bit label 0 false finalSeen).observe app bob =
      (failedAnswerDecision bit otherLabel 1 false finalSeen).observe app bob
    unfold ReactiveApplication.Execution.observe
    rw [failedAnswerDecision_network, failedAnswerDecision_network,
      failedAnswerDecision_physical, failedAnswerDecision_physical,
      failedAnswerDecision_receipts, failedAnswerDecision_receipts]
    change ReactiveApplication.PlayerView.mk (app := app) _
      ((failedPhysical bit label).playerView bob) _ =
        ReactiveApplication.PlayerView.mk (app := app) _
          ((failedPhysical bit otherLabel).playerView bob) _
    rw [failedPhysical_bobView bit bit label otherLabel]
    cases finalSeen <;> rfl

/-- Once Bob remembers the early opening, the later fair sample does not
change his full information, even when the opening was omitted from the ledger. -/
theorem failed_seen_sample_information (bit : Bool) (label : Fin 3) :
    bobInformation (failedAnswerDecision bit label 0 true true) =
      bobInformation (failedAnswerDecision bit label 0 true false) := by
  unfold bobInformation
  apply Prod.ext
  · rfl
  · unfold ReactiveApplication.Execution.observe
    rw [failedAnswerDecision_network, failedAnswerDecision_network,
      failedAnswerDecision_physical, failedAnswerDecision_physical,
      failedAnswerDecision_receipts, failedAnswerDecision_receipts]
    rfl

theorem omitted_seen_information_law (bit : Bool) (label : Fin 3) :
    (branchLaw (beforeLottery bit label 0 true) none).map bobInformation =
      PMF.pure (bobInformation (failedAnswerDecision bit label 0 true false)) := by
  rw [omitted_information_law, failed_seen_sample_information]
  exact mix_self _ _ _ _

theorem failed_empty_information_inputs (bit otherBit : Bool) (label otherLabel : Fin 3) :
    bobInformation (failedAnswerDecision bit label 0 false false) =
      bobInformation (failedAnswerDecision otherBit otherLabel 0 false false) := by
  unfold bobInformation
  apply Prod.ext
  · change (failedAnswerDecision bit label 0 false false).recall bob =
      (failedAnswerDecision otherBit otherLabel 0 false false).recall bob
    rw [failedAnswerDecision_recall, failedAnswerDecision_recall,
      bobObserved_first_recall, bobObserved_first_recall]
    unfold bobObservationRecord
    rw [firstLate_BobView bit otherBit label otherLabel]
    rfl
  · change (failedAnswerDecision bit label 0 false false).observe app bob =
      (failedAnswerDecision otherBit otherLabel 0 false false).observe app bob
    unfold ReactiveApplication.Execution.observe
    rw [failedAnswerDecision_network, failedAnswerDecision_network,
      failedAnswerDecision_physical, failedAnswerDecision_physical,
      failedAnswerDecision_receipts, failedAnswerDecision_receipts]
    change ReactiveApplication.PlayerView.mk (app := app) _
      ((failedPhysical bit label).playerView bob) _ =
        ReactiveApplication.PlayerView.mk (app := app) _
          ((failedPhysical otherBit otherLabel).playerView bob) _
    rw [failedPhysical_bobView bit otherBit label otherLabel]
    rfl

end Vegas.Examples.LateOpeningRuntimeBindingObservation
