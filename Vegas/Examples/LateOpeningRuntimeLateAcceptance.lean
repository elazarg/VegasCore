/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLatePrefix
import Vegas.Examples.LateOpeningRuntimeServiceContract
import Vegas.Pending.EventCompletionObservation

/-! # Actual late inclusion of Alice's certified opening

Both sending times reach the same public one-envelope lottery. The sender's
packet is genuine, arrives while the source event is ready, and can be accepted
before expiry. Bob retains his earlier privately sampled record.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeLateAcceptance

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
open LateOpeningRuntimeLatePrefix

def secondLateDecision (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) : app.Execution :=
  let observed := bobObserved bit label slot seen
  let waited := recorded observed .wait observed.application
  let ticked := recorded waited (.application .advanceClock)
    { waited.application with clock := waited.application.clock + 1 }
  recorded ticked (.activate alice) ticked.application

def beforeLottery (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) : app.Execution :=
  (secondLateDecision bit label slot seen).respond app alice
    (if slot.val = 1 then opening bit else ⟨none⟩)

theorem beforeLottery_run (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit slot) 3
      (bobObserved bit label slot seen) = PMF.pure (beforeLottery bit label slot seen) := by
  let e5 := bobObserved bit label slot seen
  let e6 := recorded e5 .wait e5.application
  let e7 := recorded e6 (.application .advanceClock)
    { e6.application with clock := e6.application.clock + 1 }
  let p7 := recorded e7 (.activate alice) e7.application
  have noBob : latestAuthor bob (e5.observeEnvironment app) = .wait := by
    fin_cases slot <;> cases seen <;> rfl
  have noForeign : foreignPending alice e7.network.pending = ∅ := by
    fin_cases slot <;> cases seen <;> rfl
  have s5 : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit slot) e5 = PMF.pure e6 := by
    rw [fixed_round weight nonnegative (latePlayers bit slot) e5 e6 5 .wait rfl
      (by change PMF.pure (latestAuthor bob _) = PMF.pure .wait; rw [noBob])
      (recorded_wait e5)]
    rfl
  have s6 : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit slot) e6 = PMF.pure e7 := by
    rw [fixed_round weight nonnegative (latePlayers bit slot) e6 e7 6
      (.application .advanceClock) rfl rfl (recorded_clock e6)]
    rfl
  have s7 : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit slot) e7 = PMF.pure (beforeLottery bit label slot seen) := by
    rw [fixed_round weight nonnegative (latePlayers bit slot) e7 p7 7 (.activate alice)
      rfl rfl (recorded_activation e7 alice noForeign)]
    change (PMF.pure (if alice = alice ∧ 2 = 1 + slot.val then opening bit else ⟨none⟩)).map
      (p7.respond app alice) = _
    have test : 2 = 1 + slot.val ↔ slot.val = 1 := by omega
    simp only [true_and, test, PMF.pure_map]
    rfl
  rw [ReactiveApplication.runRounds, s5, PMF.pure_bind,
    ReactiveApplication.runRounds, s6, PMF.pure_bind,
    ReactiveApplication.runRounds, s7, PMF.pure_bind,
    ReactiveApplication.runRounds]

theorem secondLate_opening_packet (bit : Bool) (label : Fin 3) (seen : Bool) :
    app.packet (secondLateDecision bit label 1 seen).application alice []
      (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩)) =
        (openingMessage bit).payload := by
  rw [LateOpeningRuntimeService.runtime.windowOpening_packet leaks alice aliceEvent aliceCandidate
    ⟨.bool, bit⟩ _ [] rfl (by rfl)]
  congr 1

theorem beforeLottery_pending (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (beforeLottery bit label slot seen).network.pending = [openingMessage bit] := by
  fin_cases slot
  · change (beforeBob bit label 0).network.pending = _
    rw [beforeBob_first_network]
    rfl
  · change [(⟨(alice, 0), app.packet (secondLateDecision bit label 1 seen).application alice []
      (disclosureSubmission (.opening aliceEvent aliceCandidate ⟨.bool, bit⟩))⟩ :
        Message Player app.Payload)] = _
    rw [secondLate_opening_packet]
    rfl

theorem beforeLottery_physical (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (beforeLottery bit label slot seen).application =
      { initialPhysical bit label with clock := 2 } := by
  fin_cases slot <;> rfl

theorem beforeLottery_bobRecall (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (beforeLottery bit label slot seen).recall bob =
      (bobObserved bit label slot seen).recall bob := rfl

abbrev inclusionProbability (weight : ℝ) : ℝ := MessageNetwork.inclusionMass weight 1

theorem inclusionProbability_eq (weight : ℝ) :
    inclusionProbability weight = weight / (1 + weight) := by
  simp [inclusionProbability, MessageNetwork.inclusionMass]

theorem lottery_command_law (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    stageChoice weight nonnegative 8 ((beforeLottery bit label slot seen).observeEnvironment app) =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure (.include (alice, 0))) (PMF.pure .wait) := by
  change (MessageNetwork.chooseWithOutside weight nonnegative
    (MessageNetwork.pendingIds (beforeLottery bit label slot seen).network.pending)).map _ = _
  rw [beforeLottery_pending]
  change (MessageNetwork.chooseWithOutside weight nonnegative {(alice, 0)}).map _ = _
  rw [MessageNetwork.chooseWithOutside]
  simp only [Finset.card_singleton]
  rw [MessageNetwork.chooseUniform_singleton, mix_map, PMF.pure_map, PMF.pure_map]
  rfl

private theorem initial_opening_ready (bit : Bool) (label : Fin 3) :
    ({ initialPhysical bit label with clock := 2 } : app.State).config.cut.Ready aliceEvent := by
  refine ⟨?_, ?_⟩
  · change aliceEvent ∉ (∅ : Finset nativeGraph.EventId)
    decide
  · change (∅ : Finset nativeGraph.EventId) ⊆ ∅
    exact Finset.empty_subset _

def openedPhysical (bit : Bool) (label : Fin 3) : app.State :=
  ({ initialPhysical bit label with clock := 2 } : app.State).complete aliceEvent
    (initial_opening_ready bit label) true (.success bit)

/-- The actual contract accepts the certified late envelope before its
deadline and stores Alice's initialized immutable bit as a successful publication. -/
theorem handle_late_opening (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    app.handle (beforeLottery bit label slot seen).application (openingMessage bit) =
      some (openedPhysical bit label) := by
  rw [beforeLottery_physical,
    LateOpeningRuntimeService.runtime.reactiveApplication_handle_of_tokenValid leaks
      _ _ (by rfl)]
  exact handle_opening_eq LateOpeningRuntimeService.runtime _ (alice, 0) aliceEvent aliceCandidate
    alice .bool aliceBinding [] rfl rfl rfl (initial_opening_ready bit label)
    (by change 2 - 0 < 3; decide) rfl rfl rfl bit rfl rfl (.success bit) rfl

theorem beforeLottery_lookup (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (beforeLottery bit label slot seen).network.lookup (alice, 0) = some (openingMessage bit) := by
  rw [MessageNetwork.lookup, beforeLottery_pending]
  rfl

def acceptedLottery (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) : app.Execution :=
  let pending := beforeLottery bit label slot seen
  { pending.includePending app (alice, 0) with
    environmentRecall := pending.environmentRecall ++
      [⟨pending.observeEnvironment app, .include (alice, 0)⟩] }

def omittedLottery (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) : app.Execution :=
  let pending := beforeLottery bit label slot seen
  recorded pending .wait pending.application

theorem acceptedLottery_physical (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (acceptedLottery bit label slot seen).application = openedPhysical bit label := by
  change ((beforeLottery bit label slot seen).includePending app (alice, 0)).application = _
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending, beforeLottery_lookup]
  change (app.handle (beforeLottery bit label slot seen).application
    (openingMessage bit)).getD _ = _
  rw [handle_late_opening]
  rfl

theorem acceptedLottery_receipt (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    ((alice, 0), true) ∈ (acceptedLottery bit label slot seen).receipts := by
  change ((alice, 0), true) ∈ ((beforeLottery bit label slot seen).includePending app
    (alice, 0)).receipts
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending, beforeLottery_lookup]
  change ((alice, 0), true) ∈ (beforeLottery bit label slot seen).receipts ++
    [((alice, 0), (app.handle (beforeLottery bit label slot seen).application
      (openingMessage bit)).isSome)]
  rw [handle_late_opening]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem acceptedLottery_pending (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (acceptedLottery bit label slot seen).network.pending = [] := by
  change ((beforeLottery bit label slot seen).includePending app (alice, 0)).network.pending = _
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending, beforeLottery_lookup]
  change MessagePool.removeFirst (alice, 0) (beforeLottery bit label slot seen).network.pending = []
  rw [beforeLottery_pending]
  rfl

theorem lottery_round (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit slot)
      (beforeLottery bit label slot seen) =
      mix (inclusionProbability weight)
        (MessageNetwork.inclusionMass_nonnegative weight nonnegative 1)
        (MessageNetwork.inclusionMass_below_one weight nonnegative 1).le
        (PMF.pure (acceptedLottery bit label slot seen))
        (PMF.pure (omittedLottery bit label slot seen)) := by
  rw [ReactiveApplication.round]
  change (stageChoice weight nonnegative 8 _).bind _ = _
  rw [lottery_command_law, mix_bind, PMF.pure_bind, PMF.pure_bind]
  congr 1
  · simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
      ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
    rfl
  · simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
    rw [recorded_wait, PMF.pure_bind]
    rfl

theorem openedPhysical_done (bit : Bool) (label : Fin 3) :
    aliceEvent ∈ (openedPhysical bit label).config.cut.completed := by
  change aliceEvent ∈ insert aliceEvent (∅ : Finset nativeGraph.EventId)
  exact Finset.mem_insert_self _ _

theorem openedPhysical_bit (bit : Bool) (label : Fin 3) :
    (openedPhysical bit label).config.store (.inr aliceEvent) = some (.success bit) := by
  rfl

def beforeAnswer (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) : app.Execution :=
  let accepted := acceptedLottery bit label slot seen
  let ticked := recorded accepted (.application .advanceClock)
    { accepted.application with clock := accepted.application.clock + 1 }
  recorded ticked (.application (.expire aliceEvent)) ticked.application

def answerDecision (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) : app.Execution :=
  let waiting := beforeAnswer bit label slot seen
  recorded waiting (.activate bob) waiting.application

private theorem recorded_completed_expiry (execution : app.Execution)
    (completed : aliceEvent ∈ execution.application.config.cut.completed) :
    execution.environmentStep app (.application (.expire aliceEvent)) =
      PMF.pure (recorded execution (.application (.expire aliceEvent)) execution.application) := by
  rw [ReactiveApplication.Execution.environmentStep]
  change ((environmentStep LateOpeningRuntimeService.runtime execution.application
    (.expire aliceEvent)).map _).map _ = _
  rw [environmentStep_expire_of_not_ready LateOpeningRuntimeService.runtime _ aliceEvent
    (fun ready => ready.1 completed), PMF.pure_map, PMF.pure_map]
  rfl

theorem beforeAnswer_run (weight : ℝ) (nonnegative : 0 ≤ weight)
    (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) (latePlayers bit slot) 2
      (acceptedLottery bit label slot seen) = PMF.pure (beforeAnswer bit label slot seen) := by
  let accepted := acceptedLottery bit label slot seen
  let ticked := recorded accepted (.application .advanceClock)
    { accepted.application with clock := accepted.application.clock + 1 }
  have s9 : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit slot) accepted = PMF.pure ticked := by
    rw [fixed_round weight nonnegative (latePlayers bit slot) accepted ticked 9
      (.application .advanceClock) rfl rfl (recorded_clock accepted)]
    rfl
  have completed : aliceEvent ∈ ticked.application.config.cut.completed := by
    change aliceEvent ∈ accepted.application.config.cut.completed
    rw [acceptedLottery_physical]
    exact openedPhysical_done bit label
  have s10 : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      (latePlayers bit slot) ticked = PMF.pure (beforeAnswer bit label slot seen) := by
    rw [fixed_round weight nonnegative (latePlayers bit slot) ticked
      (beforeAnswer bit label slot seen) 10 (.application (.expire aliceEvent)) rfl rfl
      (recorded_completed_expiry ticked completed)]
    rfl
  rw [ReactiveApplication.runRounds, s9, PMF.pure_bind,
    ReactiveApplication.runRounds, s10, PMF.pure_bind, ReactiveApplication.runRounds]

theorem answerDecision_activation (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (beforeAnswer bit label slot seen).environmentStep app (.activate bob) =
      PMF.pure (answerDecision bit label slot seen) := by
  exact recorded_activation _ bob (by
    change foreignPending bob (acceptedLottery bit label slot seen).network.pending = ∅
    rw [acceptedLottery_pending]
    rfl)

theorem answerDecision_physical (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (answerDecision bit label slot seen).application =
      { openedPhysical bit label with clock := 3 } := by
  change { (acceptedLottery bit label slot seen).application with
    clock := (acceptedLottery bit label slot seen).application.clock + 1 } = _
  rw [acceptedLottery_physical]
  rfl

theorem answerDecision_bobRecall (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (answerDecision bit label slot seen).recall bob =
      (bobObserved bit label slot seen).recall bob := by
  change ((beforeLottery bit label slot seen).includePending app (alice, 0)).recall bob = _
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending, beforeLottery_lookup]
  rfl

theorem openedPhysical_bobView_label (bit : Bool) (label otherLabel : Fin 3) :
    (openedPhysical bit label).playerView bob = (openedPhysical bit otherLabel).playerView bob := by
  have initial : ({ initialPhysical bit label with clock := 2 } : app.State).playerView bob =
      ({ initialPhysical bit otherLabel with clock := 2 } : app.State).playerView bob :=
    congrArg (fun view : EventGraphRuntime.PlayerView nativeGraph =>
      { view with publicView := { view.publicView with clock := 2 } })
      (initialBobView bit bit label otherLabel)
  exact State.complete_playerView_congr _ _ bob
    (congrArg PlayerView.publicView initial)
    (State.playerView_observation_eq _ _ bob initial)
    (congrArg PlayerView.candidates initial) aliceEvent
    (initial_opening_ready bit label) (initial_opening_ready bit otherLabel)
    true true (.success bit) (.success bit) (fun _ => rfl) (fun _ => rfl)

theorem answerDecision_bobApplication_label (bit : Bool) (label otherLabel : Fin 3)
    (slot otherSlot : Fin 2) (seen otherSeen : Bool) :
    (answerDecision bit label slot seen).application.playerView bob =
      (answerDecision bit otherLabel otherSlot otherSeen).application.playerView bob := by
  rw [answerDecision_physical, answerDecision_physical]
  exact congrArg (fun view : EventGraphRuntime.PlayerView nativeGraph =>
    { view with publicView := { view.publicView with clock := 3 } })
      (openedPhysical_bobView_label bit label otherLabel)

theorem acceptedLottery_receipts_eq (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (acceptedLottery bit label slot seen).receipts = [((alice, 0), true)] := by
  change ((beforeLottery bit label slot seen).includePending app (alice, 0)).receipts = _
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending, beforeLottery_lookup]
  change (beforeLottery bit label slot seen).receipts ++
    [((alice, 0), (app.handle (beforeLottery bit label slot seen).application
      (openingMessage bit)).isSome)] = _
  rw [handle_late_opening]
  rfl

theorem beforeLottery_bobNetwork (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (beforeLottery bit label slot seen).network.observe bob =
      ⟨if seen = true ∧ slot.val = 0 then [openingMessage bit] else [], []⟩ := by
  fin_cases slot
  · change ((beforeBob bit label 0).network.learn bob
      (if seen then {(alice, 0)} else ∅)).observe bob = _
    rw [beforeBob_first_network]
    cases seen <;> rfl
  · cases seen <;> rfl

theorem answerDecision_bobNetwork (bit : Bool) (label : Fin 3) (slot : Fin 2) (seen : Bool) :
    (answerDecision bit label slot seen).network.observe bob =
      ⟨if seen = true ∧ slot.val = 0 then [openingMessage bit] else [], [openingMessage bit]⟩ := by
  change ((beforeLottery bit label slot seen).includePending app (alice, 0)).network.observe bob = _
  unfold ReactiveApplication.Execution.includePending
  rw [MessageNetwork.includePending, beforeLottery_lookup]
  change MessageNetwork.PlayerView.mk ((beforeLottery bit label slot seen).network.leaked bob)
    ((beforeLottery bit label slot seen).network.ledger ++
      ([openingMessage bit] : List (Message Player app.Payload))) = _
  have previous := beforeLottery_bobNetwork bit label slot seen
  have leaked := congrArg MessageNetwork.PlayerView.leaked previous
  have ledger := congrArg MessageNetwork.PlayerView.ledger previous
  change (beforeLottery bit label slot seen).network.leaked bob =
    if seen = true ∧ slot.val = 0 then [openingMessage bit] else [] at leaked
  change (beforeLottery bit label slot seen).network.ledger = [] at ledger
  rw [leaked, ledger]
  rfl

theorem answerDecision_view_label (bit : Bool) (label otherLabel : Fin 3)
    (slot : Fin 2) (seen : Bool) :
    (answerDecision bit label slot seen).observe app bob =
      (answerDecision bit otherLabel slot seen).observe app bob := by
  unfold ReactiveApplication.Execution.observe
  change ReactiveApplication.PlayerView.mk (app := app) _
    ((answerDecision bit label slot seen).application.playerView bob) _ =
      ReactiveApplication.PlayerView.mk (app := app) _
        ((answerDecision bit otherLabel slot seen).application.playerView bob) _
  rw [answerDecision_bobNetwork, answerDecision_bobNetwork,
    answerDecision_bobApplication_label bit label otherLabel slot slot seen seen]
  change ReactiveApplication.PlayerView.mk (app := app) _ _
    (acceptedLottery bit label slot seen).receipts =
      ReactiveApplication.PlayerView.mk (app := app) _ _
        (acceptedLottery bit otherLabel slot seen).receipts
  rw [acceptedLottery_receipts_eq, acceptedLottery_receipts_eq]

theorem answerDecision_first_label_info (bit : Bool) (label otherLabel : Fin 3) (seen : Bool) :
    ((answerDecision bit label 0 seen).recall bob,
      (answerDecision bit label 0 seen).observe app bob) =
      ((answerDecision bit otherLabel 0 seen).recall bob,
        (answerDecision bit otherLabel 0 seen).observe app bob) := by
  apply Prod.ext
  · rw [answerDecision_bobRecall, answerDecision_bobRecall,
      bobObserved_first_recall, bobObserved_first_recall,
      bobObservationRecord_label bit label otherLabel seen]
  · exact answerDecision_view_label bit label otherLabel 0 seen

theorem answerDecision_second_label_info (bit : Bool) (label otherLabel : Fin 3) :
    ((answerDecision bit label 1 false).recall bob,
      (answerDecision bit label 1 false).observe app bob) =
      ((answerDecision bit otherLabel 1 false).recall bob,
        (answerDecision bit otherLabel 1 false).observe app bob) := by
  apply Prod.ext
  · rw [answerDecision_bobRecall, answerDecision_bobRecall,
      bobObserved_second_recall, bobObserved_second_recall,
      bobObservationRecord_label bit label otherLabel false]
  · exact answerDecision_view_label bit label otherLabel 1 false

/-- On the accepted-success branch, Bob's whole current view and remembered
record agree between first-late sending missed by the sampler and second-late
sending. The private preference label is also absent from that information. -/
theorem answerDecision_unseen_timing_info (bit : Bool) (label otherLabel : Fin 3) :
    ((answerDecision bit label 0 false).recall bob,
      (answerDecision bit label 0 false).observe app bob) =
      ((answerDecision bit otherLabel 1 false).recall bob,
        (answerDecision bit otherLabel 1 false).observe app bob) := by
  apply Prod.ext
  · rw [answerDecision_bobRecall, answerDecision_bobRecall,
      unseen_timing_recall bit label otherLabel]
  · unfold ReactiveApplication.Execution.observe
    change ReactiveApplication.PlayerView.mk (app := app) _
      ((answerDecision bit label 0 false).application.playerView bob) _ =
        ReactiveApplication.PlayerView.mk (app := app) _
          ((answerDecision bit otherLabel 1 false).application.playerView bob) _
    rw [answerDecision_bobNetwork, answerDecision_bobNetwork,
      answerDecision_bobApplication_label bit label otherLabel 0 1 false false]
    change ReactiveApplication.PlayerView.mk (app := app) _ _
      (acceptedLottery bit label 0 false).receipts =
        ReactiveApplication.PlayerView.mk (app := app) _ _
          (acceptedLottery bit otherLabel 1 false).receipts
    rw [acceptedLottery_receipts_eq, acceptedLottery_receipts_eq]
    simp only [Bool.false_eq_true, false_and, ↓reduceIte]

end Vegas.Examples.LateOpeningRuntimeLateAcceptance
