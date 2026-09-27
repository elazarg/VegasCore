/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.Restricted
import Vegas.Examples.MonitoredGuessing.NativeHonest
import Vegas.Examples.MonitoredGuessing.Source

/-! # Both source choices in the restricted native service

Source refusal is implemented by silence and the existing expiry command.
Successful disclosure uses the initialized matching certificate. The equations
below concern the actual interaction kernels and retain application results.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem opening_eq (execution : nativeApp.Execution) (who : Player)
    (event : nativeGraph.EventId) (handle : Handle nativeGraph) (value : Bool)
    (owner : handle.1 = who)
    (candidate : execution.application.candidates.lookup handle = .openable ⟨.bool, value⟩)
    (unseen : EvidenceRequest.forwardingPacket
      (ReactiveApplication.ResponseMenu.knownPackets (execution.recall who)
        (execution.observe nativeApp who)) ⟨handle, ⟨.bool, value⟩⟩ = none) :
    opening who (execution.recall who) (execution.observe nativeApp who) event handle value =
      nativeOpeningAction event handle value := by
  have normal := EvidenceRequest.normalize_owned_of_no_forward who
    (execution.observe nativeApp who).application.candidates
    (ReactiveApplication.ResponseMenu.knownPackets (execution.recall who)
      (execution.observe nativeApp who)) ⟨handle, ⟨.bool, value⟩⟩ owner
        (by
          change execution.application.candidates.lookup (who, handle.2) = _
          simpa only [← owner, Prod.mk.eta] using candidate) unseen
  simpa only [opening, normalization, nativeOpeningAction,
    ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
    WitnessedSubmission.normalizeReactive, Submission.normalizeReactive_none,
    Submission.candidateAfter_opening] using
      congrArg (fun request : EvidenceRequest nativeGraph =>
        (⟨some (.submit ⟨⟨.opening event handle ⟨.bool, value⟩, none⟩, request⟩)⟩ :
          nativeApp.Action)) normal

def choiceAction (event : nativeGraph.EventId) (handle : Handle nativeGraph)
    (value disclose : Bool) : nativeApp.Action :=
  if disclose then nativeOpeningAction event handle value else nativeSilent

def silentBobResponse (bit : Bool) : nativeApp.Execution :=
  (quietBob bit).respond nativeApp bob nativeSilent

def silentBobIncluded (bit : Bool) : nativeApp.Execution :=
  let before := silentBobResponse bit
  { before with environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment nativeApp, .wait⟩] }

def silentBobTicked (bit : Bool) : nativeApp.Execution :=
  let before := silentBobIncluded bit
  { before with
    application := { before.application with clock := before.application.clock + 1 }
    environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment nativeApp, .application .advanceClock⟩] }

theorem silent_bob_ready (bit : Bool) :
    (silentBobTicked bit).application.config.cut.Ready bobPublication :=
  initial_bob_ready bit

def silentBobExpired (bit : Bool) : nativeApp.Execution :=
  let before := silentBobTicked bit
  { before with
    application := before.application.complete bobPublication (silent_bob_ready bit)
      false .failure
    environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment nativeApp, .application (.expire bobPublication)⟩] }

theorem silent_bob_inclusion (players : Player → nativeApp.Policy) (bit : Bool) :
    nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest bobPublication bob) (silentBobResponse bit) =
        FinDist.pure (silentBobIncluded bit) := by
  have pending : (silentBobResponse bit).network.pending = [] := by
    change (quietBob bit).network.pending = []
    rw [quiet_bob_network]
    rfl
  simp only [interactionStep, interactionInstruction, reactiveLatest,
    ReactiveApplication.Execution.observeEnvironment, MessageNetwork.publicView,
    pending, List.reverse_nil,
    List.find?_nil, FinDist.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume]
  rfl

theorem silent_bob_tick (bit : Bool) :
    (silentBobIncluded bit).environmentStep nativeApp (.application .advanceClock) =
      FinDist.pure (silentBobTicked bit) := by
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    environmentStep, FinDist.map_pure]
  rfl

theorem silent_bob_expiry (bit : Bool) :
    (silentBobTicked bit).environmentStep nativeApp (.application (.expire bobPublication)) =
      FinDist.pure (silentBobExpired bit) := by
  have expiry := environmentStep_expire_resolve_eq nativeRuntime
    (silentBobTicked bit).application bobPublication (silent_bob_ready bit) 0 rfl
    (by change 1 ≤ 1; omega) bob .bool bobBindingRef [] rfl rfl bob_node
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    expiry, FinDist.map_pure]
  rfl

theorem silent_bob_service (players : Player → nativeApp.Policy) (bit : Bool) :
    nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      [.includeLatest bobPublication bob, .tick, .expire bobPublication]
      (silentBobResponse bit) = FinDist.pure (silentBobExpired bit) := by
  rw [runInteractionPlan, silent_bob_inclusion, FinDist.pure_bind]
  simp only [runInteractionPlan, interactionStep, interactionInstruction,
    FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume, silent_bob_tick, silent_bob_expiry]

theorem silent_bob_publication (bit : Bool) :
    bobPublicationRef.get? (silentBobExpired bit).application.config.store = some .failure := by
  simp [silentBobExpired, State.complete, EventGraph.Config.store,
    bobPublicationRef, EventGraph.FieldRef.get?]

def afterBob (bit guess : Bool) : nativeApp.Execution :=
  if guess then quietGuessExpired bit true else silentBobExpired bit

def grantedAlice (bit guess : Bool) : nativeApp.Execution :=
  let before := afterBob bit guess
  { before with
    application := { before.application with serviceGrant := some alicePublication }
    environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment nativeApp, .application (.grant alicePublication)⟩] }

def beforeAlice (bit guess : Bool) : nativeApp.Execution :=
  let before := grantedAlice bit guess
  { before with environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment nativeApp, .activate alice⟩] }

theorem bob_service (players : Player → nativeApp.Policy) (bit guess : Bool) :
    nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      [.includeLatest bobPublication bob, .tick, .expire bobPublication]
      ((quietBob bit).respond nativeApp bob (choiceAction bobPublication bobHandle true guess)) =
        FinDist.pure (afterBob bit guess) := by
  cases guess with
  | false => exact silent_bob_service players bit
  | true =>
      change nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork _
        (quietGuessRespond bit true) = _
      rw [runInteractionPlan, quiet_guess_included, FinDist.pure_bind]
      simp only [runInteractionPlan, interactionStep, interactionInstruction,
        FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, quiet_guess_tick, quiet_guess_expiry]
      rfl

theorem after_bob_stored (bit guess : Bool) :
    bobPublicationRef.get? (afterBob bit guess).application.config.store =
      some (guessResult guess) := by
  cases guess with
  | false => exact silent_bob_publication bit
  | true => exact (quiet_guess_results bit true).1

theorem after_bob_ready (bit guess : Bool) :
    (afterBob bit guess).application.config.cut.Ready alicePublication := by
  cases guess with
  | true => exact quiet_guess_alice_ready bit true
  | false =>
      change ((nativeInitial bit).config.cut.complete bobPublication
        (initial_bob_ready bit)).Ready alicePublication
      cases bit <;> decide

theorem after_bob_fixed (bit guess : Bool) :
    NativeFixed bit (afterBob bit guess).application := by
  cases guess with
  | true =>
      have fixed := quiet_alice_fixed bit true
      exact ⟨fixed.1.copy rfl rfl rfl, fixed.2.1.copy rfl rfl rfl, fixed.2.2⟩
  | false =>
      have ticked := (native_fixed_invariant bit).environment
        (silentBobIncluded bit).application .advanceClock
        (silentBobTicked bit).application (quiet_bob_fixed bit)
        (FinDist.mem_support_pure.mpr rfl)
      apply (native_fixed_invariant bit).environment
        (silentBobTicked bit).application (.expire bobPublication) _ ticked
      have expiry := environmentStep_expire_resolve_eq nativeRuntime
        (silentBobTicked bit).application bobPublication (silent_bob_ready bit) 0 rfl
        (by change 1 ≤ 1; omega) bob .bool bobBindingRef [] rfl rfl bob_node
      change _ ∈ (environmentStep nativeRuntime _ _).support
      rw [expiry]
      exact FinDist.mem_support_pure.mpr rfl

theorem after_bob_clock (bit guess : Bool) : (afterBob bit guess).application.clock = 1 := by
  cases guess with
  | false => rfl
  | true =>
      change (quietGuessIncluded bit true).application.clock + 1 = 1
      rw [quiet_guess_clock]

theorem before_alice_fixed (bit guess : Bool) :
    NativeFixed bit (beforeAlice bit guess).application :=
  (native_fixed_invariant bit).environment (afterBob bit guess).application
    (.grant alicePublication) _ (after_bob_fixed bit guess)
    (FinDist.mem_support_pure.mpr rfl)

theorem before_alice_timely (bit guess : Bool) :
    (beforeAlice bit guess).application.WithinDeadline nativeRuntime alicePublication := by
  obtain ⟨entered, activated⟩ := (before_alice_fixed bit guess).1.activatedAt_eq_some_of_ready_actor
    alicePublication (after_bob_ready bit guess) (by rw [native_actor]; rfl)
  rw [State.WithinDeadline, activated]
  change (afterBob bit guess).application.clock - entered < 2
  rw [after_bob_clock]
  omega

theorem grant_alice (bit guess : Bool) :
    (afterBob bit guess).environmentStep nativeApp (.application (.grant alicePublication)) =
      FinDist.pure (grantedAlice bit guess) := by
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    environmentStep, FinDist.map_pure]
  rfl

theorem activate_alice (bit guess : Bool) :
    (grantedAlice bit guess).environmentStep nativeApp (.activate alice) =
      FinDist.pure (beforeAlice bit guess) := by
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    nativeLeaks, alice, watcher, bob, show (0 : Player) ≠ 2 by decide,
    show (0 : Player) ≠ 1 by decide, ↓reduceIte, FinDist.map_pure, MessageNetwork.learn_empty]
  rfl

theorem before_alice_opening (bit guess : Bool) :
    opening alice ((beforeAlice bit guess).recall alice)
      ((beforeAlice bit guess).observe nativeApp alice) alicePublication aliceHandle
        (observedAliceBit ((beforeAlice bit guess).observe nativeApp alice)) =
      nativeOpeningAction alicePublication aliceHandle bit := by
  rw [native_observed_alice_bit bit _ (before_alice_fixed bit guess)]
  apply opening_eq _ alice alicePublication aliceHandle bit rfl
    (before_alice_fixed bit guess).alice_candidate
  have known : ReactiveApplication.ResponseMenu.knownPackets
      ((beforeAlice bit guess).recall alice) ((beforeAlice bit guess).observe nativeApp alice) =
        if guess then [⟨(bob, 0), ⟨.opening bobPublication bobHandle ⟨.bool, true⟩,
          some ⟨bobHandle, ⟨.bool, true⟩⟩⟩⟩] else [] := by cases guess <;> rfl
  rw [known]
  cases guess <;> simp [EvidenceRequest.forwardingPacket, EvidenceRequest.forwardedEvidence,
    aliceHandle, bobHandle, alice, bob]

theorem quiet_bob_opening (bit : Bool) :
    opening bob ((quietBob bit).recall bob) ((quietBob bit).observe nativeApp bob)
      bobPublication bobHandle true = nativeOpeningAction bobPublication bobHandle true := by
  apply opening_eq _ bob bobPublication bobHandle true rfl (quiet_bob_fixed bit).bob_candidate
  change EvidenceRequest.forwardingPacket [] _ = none
  rfl

theorem before_alice_pending (bit guess : Bool) :
    (beforeAlice bit guess).network.pending = [] := by
  cases guess with
  | false =>
      change (quietBob bit).network.pending = []
      rw [quiet_bob_network]
      rfl
  | true =>
      change ((quietGuessRespond bit true).includePending nativeApp (bob, 0)).network.pending = []
      rw [nativeApp.includePending_network]
      simp only [quietGuessRespond, nativeGuessAction, ↓reduceIte, nativeOpeningAction,
        ReactiveApplication.Execution.respond, quiet_bob_network, MessageNetwork.submit,
        MessageNetwork.empty, List.nil_append, MessageNetwork.includePending,
        MessageNetwork.lookup, MessagePool.removeFirst]
      rfl

theorem before_alice_serials (bit guess : Bool) :
    (beforeAlice bit guess).network.SerialsBeforeNext := by
  cases guess with
  | false =>
      change (quietBob bit).network.SerialsBeforeNext
      exact quiet_bob_serials bit
  | true => exact quiet_alice_serials bit true

theorem before_alice_no_charge (bit guess : Bool) :
    rejectedAlice (beforeAlice bit guess).receipts = false := by
  cases guess with
  | false => rfl
  | true =>
      change rejectedAlice (quietGuessIncluded bit true).receipts = false
      rw [(quiet_guess_results bit true).2]
      rfl

def waitExecution (execution : nativeApp.Execution) : nativeApp.Execution :=
  { execution with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment nativeApp, .wait⟩] }

def tickExecution (execution : nativeApp.Execution) : nativeApp.Execution :=
  { execution with
    application := { execution.application with clock := execution.application.clock + 1 }
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment nativeApp, .application .advanceClock⟩] }

theorem empty_reserved_inclusion (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (event : nativeGraph.EventId) (who : Player)
    (pending : execution.network.pending = []) :
    nativeRuntime.interactionStep nativeLeaks players nativeNetwork (.includeLatest event who)
      execution = FinDist.pure (waitExecution execution) := by
  have selected : nativeRuntime.reactiveLatest nativeLeaks event who
      (execution.observeEnvironment nativeApp) = .wait := by
    simp only [reactiveLatest, ReactiveApplication.Execution.observeEnvironment,
      MessageNetwork.publicView, pending, List.reverse_nil, List.find?_nil]
  simp only [interactionStep, interactionInstruction, selected,
    FinDist.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume]
  rfl

theorem tick_execution (execution : nativeApp.Execution) :
    execution.environmentStep nativeApp (.application .advanceClock) =
      FinDist.pure (tickExecution execution) := by
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    environmentStep, FinDist.map_pure]
  rfl

def silentAliceDue (bit guess : Bool) : nativeApp.Execution :=
  tickExecution (tickExecution (waitExecution
    ((beforeAlice bit guess).respond nativeApp alice nativeSilent)))

def silentAliceExpired (bit guess : Bool) : nativeApp.Execution :=
  let before := silentAliceDue bit guess
  { before with
    application := before.application.complete alicePublication (after_bob_ready bit guess)
      false .failure
    environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment nativeApp, .application (.expire alicePublication)⟩] }

theorem silent_alice_expiry (bit guess : Bool) :
    (silentAliceDue bit guess).environmentStep nativeApp (.application (.expire alicePublication)) =
      FinDist.pure (silentAliceExpired bit guess) := by
  obtain ⟨entered, activated⟩ := (before_alice_fixed bit guess).1.activatedAt_eq_some_of_ready_actor
    alicePublication (after_bob_ready bit guess) (by rw [native_actor]; rfl)
  have enteredLe := (before_alice_fixed bit guess).1.activated_le _ _ activated
  have expiry := environmentStep_expire_resolve_eq nativeRuntime
    (silentAliceDue bit guess).application alicePublication (after_bob_ready bit guess)
    entered activated (by
      change 2 ≤ (beforeAlice bit guess).application.clock + 1 + 1 - entered
      omega) alice .bool aliceBindingRef [] rfl rfl alice_node
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    expiry, FinDist.map_pure]
  rfl

theorem silent_alice_service (players : Player → nativeApp.Policy) (bit guess : Bool) :
    nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
      ((beforeAlice bit guess).respond nativeApp alice nativeSilent) =
        FinDist.pure (silentAliceExpired bit guess) := by
  rw [resolutionTail, runInteractionPlan, empty_reserved_inclusion players
    ((beforeAlice bit guess).respond nativeApp alice nativeSilent) _ _
    (before_alice_pending bit guess), FinDist.pure_bind]
  simp only [runInteractionPlan, interactionStep, interactionInstruction,
    FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume, tick_execution]
  change (((silentAliceDue bit guess).environmentStep nativeApp
    (.application (.expire alicePublication))).bind FinDist.pure).bind FinDist.pure = _
  rw [silent_alice_expiry, FinDist.pure_bind, FinDist.pure_bind]

theorem silent_alice_result (bit guess : Bool) :
    nativeResults (silentAliceExpired bit guess).application.config =
      ⟨.failure, guessResult guess⟩ := by
  have stored := after_bob_stored bit guess
  simp only [nativeResults, silentAliceExpired, State.complete, EventGraph.Config.store,
    EventGraph.FieldRef.get?, alicePublicationRef, bobPublicationRef]
  exact congrArg (Results.mk .failure) (congrArg (fun result => result.getD .failure) stored)

theorem alice_service_summary (players : Player → nativeApp.Policy)
    (bit guess disclose : Bool) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork resolutionTail
      ((beforeAlice bit guess).respond nativeApp alice
        (choiceAction alicePublication aliceHandle bit disclose))).map
          (fun final => (nativeResults final.application.config, rejectedAlice final.receipts)) =
      FinDist.pure (Results.mk (if disclose then .success bit else .failure) (guessResult guess),
        false) := by
  cases disclose with
  | false =>
      simp only [choiceAction, Bool.false_eq_true, ↓reduceIte, silent_alice_service,
        FinDist.map_pure, silent_alice_result]
      change FinDist.pure (_, rejectedAlice (beforeAlice bit guess).receipts) = _
      rw [before_alice_no_charge]
  | true =>
      simpa only [choiceAction, ↓reduceIte, before_alice_no_charge] using
        resolution_tail_summary players (beforeAlice bit guess) bit (guessResult guess)
          (before_alice_fixed bit guess) (after_bob_stored bit guess)
          (after_bob_ready bit guess) (before_alice_timely bit guess)
          (before_alice_serials bit guess)

theorem bob_to_alice (players : Player → nativeApp.Policy) (bit guess : Bool) :
    nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      [.includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication, .player alice]
      ((quietBob bit).respond nativeApp bob (choiceAction bobPublication bobHandle true guess)) =
      (players alice ((beforeAlice bit guess).recall alice)
        ((beforeAlice bit guess).observe nativeApp alice)).map
          ((beforeAlice bit guess).respond nativeApp alice) := by
  change nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
    ([.includeLatest bobPublication bob, .tick, .expire bobPublication] ++
      [.grant alicePublication, .player alice]) _ = _
  rw [runInteractionPlan_append, bob_service, FinDist.pure_bind]
  simp only [runInteractionPlan, interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Command.actor?, grant_alice,
    activate_alice, ReactiveApplication.resume, ReactiveApplication.invoke, FinDist.bind_pure]

theorem source_results (bit guess disclose : Bool) :
    sourceResults (finalConfig bit guess disclose).state =
      ⟨if disclose then .success bit else .failure, guessResult guess⟩ := by
  cases bit <;> cases guess <;> cases disclose <;> rfl

/-- Every pair of source choices has the same results and incurs no charge.
The continuation policy is constrained only at the actual Alice input; its
behavior elsewhere is arbitrary. -/
theorem branch_summary (players : Player → nativeApp.Policy) (bit guess disclose : Bool)
    (aliceChoice : players alice ((beforeAlice bit guess).recall alice)
      ((beforeAlice bit guess).observe nativeApp alice) =
        FinDist.pure (choiceAction alicePublication aliceHandle bit disclose)) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication, .player alice] ++ resolutionTail)
      ((quietBob bit).respond nativeApp bob (choiceAction bobPublication bobHandle true guess))).map
        (fun final => (nativeResults final.application.config, rejectedAlice final.receipts)) =
      FinDist.pure (sourceResults (finalConfig bit guess disclose).state, false) := by
  rw [runInteractionPlan_append, bob_to_alice, aliceChoice, FinDist.map_pure,
    FinDist.pure_bind, alice_service_summary, source_results]

theorem branch_initial_type_results (players : Player → nativeApp.Policy)
    (bit guess disclose : Bool)
    (aliceChoice : players alice ((beforeAlice bit guess).recall alice)
      ((beforeAlice bit guess).observe nativeApp alice) =
        FinDist.pure (choiceAction alicePublication aliceHandle bit disclose)) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication, .player alice] ++ resolutionTail)
      ((quietBob bit).respond nativeApp bob (choiceAction bobPublication bobHandle true guess))).map
        (fun final => (observedAliceBit (final.observe nativeApp alice),
          nativeResults final.application.config, rejectedAlice final.receipts)) =
      FinDist.pure (bit, sourceResults (finalConfig bit guess disclose).state, false) := by
  apply FinDist.eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨final, reached, rfl⟩ := FinDist.support_map .. ▸ supported
  have summarized : (nativeResults final.application.config, rejectedAlice final.receipts) =
      (sourceResults (finalConfig bit guess disclose).state, false) := by
    apply FinDist.mem_support_pure.mp
    rw [← branch_summary players bit guess disclose aliceChoice, FinDist.support_map]
    exact ⟨final, reached, rfl⟩
  have fixed := resolution_plan_invariant players _ (native_fixed_invariant bit) _
    ((quietBob bit).respond nativeApp bob (choiceAction bobPublication bobHandle true guess)) final
    ((native_fixed_invariant bit).respond (quietBob bit) bob _ (quiet_bob_fixed bit)) reached
  change (observedAliceBit (final.observe nativeApp alice), nativeResults final.application.config,
    rejectedAlice final.receipts) = _
  rw [native_observed_alice_bit bit final fixed]
  exact congrArg (Prod.mk bit) summarized

end Vegas.Examples.MonitoredGuessing.Restricted
