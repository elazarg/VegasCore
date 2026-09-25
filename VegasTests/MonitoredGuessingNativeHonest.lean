/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNativeOutcome
import VegasTests.MonitoredGuessingNativeProfile
import VegasTests.MonitoredGuessingNativeResolutionService
import VegasTests.MonitoredGuessingNativeResolutionTail

/-! # Exact ordinary service after the quiet guessing decision -/

noncomputable section
namespace VegasTests.MonitoredGuessing
open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def guessResult (guess : Bool) : PublicationResult Bool :=
  if guess then .success true else .failure

def quietGuessRespond (bit guess : Bool) : nativeApp.Execution :=
  (quietBob bit).respond nativeApp bob (nativeGuessAction guess)

def quietGuessIncluded (bit guess : Bool) : nativeApp.Execution :=
  let before := quietGuessRespond bit guess
  { before.includePending nativeApp (bob, 0) with
    environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment nativeApp, .include (bob, 0)⟩] }

theorem quiet_bob_network (bit : Bool) : (quietBob bit).network = .empty := by
  simp only [quietBob, watcherRespond, watcherActivated, MessageNetwork.learn_empty]
  rfl

theorem quiet_bob_serials (bit : Bool) : (quietBob bit).network.SerialsBeforeNext := by
  rw [quiet_bob_network]
  exact MessageNetwork.SerialsBeforeNext.empty

theorem quiet_bob_receipts (bit : Bool) : (quietBob bit).receipts = [] := rfl

theorem quiet_guess_included (players : Player → nativeApp.Policy) (bit guess : Bool) :
    nativeRuntime.interactionStep nativeLeaks players nativeNetwork
      (.includeLatest bobPublication bob) (quietGuessRespond bit guess) =
        FinDist.pure (quietGuessIncluded bit guess) := by
  have selected : nativeRuntime.reactiveLatest nativeLeaks bobPublication bob
      ((quietGuessRespond bit guess).observeEnvironment nativeApp) = .include (bob, 0) := by
    cases guess with
    | false =>
        simpa only [quietGuessRespond, nativeGuessAction, Bool.false_eq_true, ↓reduceIte,
          quiet_bob_network, MessageNetwork.empty] using
          nativeRuntime.reactiveLatest_after_submit nativeLeaks bob bobPublication
          (quietBob bit) (quiet_bob_serials bit)
          ⟨⟨.withhold bobPublication, none⟩, .none⟩ rfl
    | true =>
        simpa only [quietGuessRespond, nativeGuessAction, ↓reduceIte,
          quiet_bob_network, MessageNetwork.empty, nativeOpeningAction] using
          nativeRuntime.reactiveLatest_after_submit nativeLeaks bob bobPublication
          (quietBob bit) (quiet_bob_serials bit)
          ⟨⟨.opening bobPublication bobHandle ⟨.bool, true⟩, none⟩,
            .owned ⟨bobHandle, ⟨.bool, true⟩⟩⟩ rfl
  simp only [interactionStep, interactionInstruction, selected, FinDist.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume, FinDist.map_pure,
    FinDist.pure_bind]
  rfl

theorem quiet_bob_fixed (bit : Bool) : NativeFixed bit (quietBob bit).application := by
  have initial := native_initial_fixed bit
  exact ⟨initial.1.copy rfl rfl rfl, initial.2.1.copy rfl rfl rfl, initial.2.2⟩

theorem quiet_guess_accepted (bit guess : Bool) :
    ∃ next, handle nativeRuntime (quietBob bit).application
      ⟨(bob, 0), if guess then .opening bobPublication bobHandle ⟨.bool, true⟩
        else .withhold bobPublication⟩ = some next ∧
      bobPublicationRef.get? next.config.store = some (guessResult guess) := by
  have ready : (quietBob bit).application.config.cut.Ready bobPublication :=
    initial_bob_ready bit
  have timely : (quietBob bit).application.WithinDeadline nativeRuntime bobPublication := by
    change 0 - 0 < 1
    decide
  cases guess with
  | false => exact resolution_withhold_accepted _ ready timely rfl 0
  | true =>
      exact resolution_opening_accepted bit _ (quiet_bob_fixed bit)
        bobPublication ready timely 0

theorem quiet_guess_application (bit guess : Bool) :
    ∃ next, handle nativeRuntime (quietBob bit).application
      ⟨(bob, 0), if guess then .opening bobPublication bobHandle ⟨.bool, true⟩
        else .withhold bobPublication⟩ = some next ∧
      bobPublicationRef.get? next.config.store = some (guessResult guess) ∧
      (quietGuessIncluded bit guess).application = next ∧
      (quietGuessIncluded bit guess).receipts = [((bob, 0), true)] := by
  obtain ⟨next, accepted, published⟩ := quiet_guess_accepted bit guess
  have law : (nativeRuntime.interactionStep nativeLeaks (fun _ => nativeAlicePolicy)
      nativeNetwork (.includeLatest bobPublication bob) (quietGuessRespond bit guess)).map
        (fun result => (result.application, result.receipts)) =
      FinDist.pure (next, [((bob, 0), true)]) := by
    cases guess with
    | false =>
        simpa only [quiet_bob_network, MessageNetwork.empty, quiet_bob_receipts,
          List.nil_append, quietGuessRespond] using resolution_withhold_inclusion
          (fun _ => nativeAlicePolicy) (quietBob bit) next (quiet_bob_serials bit)
          (by simpa only [quiet_bob_network, MessageNetwork.empty, Bool.false_eq_true,
            ↓reduceIte] using accepted)
    | true =>
        simpa only [quiet_bob_network, MessageNetwork.empty, quiet_bob_receipts,
          List.nil_append, quietGuessRespond, nativeGuessAction, ↓reduceIte] using
          resolution_opening_inclusion
          (fun _ => nativeAlicePolicy) (quietBob bit) bob bobPublication bobHandle true next
          (quiet_bob_serials bit) (by simpa only [quiet_bob_network, MessageNetwork.empty,
            ↓reduceIte] using accepted)
  have pair : ((quietGuessIncluded bit guess).application,
      (quietGuessIncluded bit guess).receipts) = (next, [((bob, 0), true)]) := by
    rw [quiet_guess_included, FinDist.map_pure] at law
    exact FinDist.mem_support_pure.mp (law ▸ FinDist.mem_support_pure.mpr rfl)
  have applicationEq : (quietGuessIncluded bit guess).application = next :=
    congrArg Prod.fst pair
  exact ⟨next, accepted, published, applicationEq, congrArg Prod.snd pair⟩

theorem quiet_guess_results (bit guess : Bool) :
    bobPublicationRef.get? (quietGuessIncluded bit guess).application.config.store =
      some (guessResult guess) ∧
    (quietGuessIncluded bit guess).receipts = [((bob, 0), true)] := by
  obtain ⟨_, _, published, applicationEq, receipts⟩ := quiet_guess_application bit guess
  exact ⟨by rw [applicationEq]; exact published, receipts⟩

theorem quiet_guess_cut (bit guess : Bool) :
    (quietGuessIncluded bit guess).application.config.cut =
      (nativeInitial bit).config.cut.complete bobPublication (initial_bob_ready bit) := by
  obtain ⟨next, accepted, _, applicationEq, _⟩ := quiet_guess_application bit guess
  obtain ⟨event, addressed, ready, action, reached⟩ :=
    handle_config_mem_step nativeRuntime (quietBob bit).application next _ accepted
  have eventEq : event = bobPublication := by
    cases guess <;> exact (Option.some.inj addressed).symm
  subst event
  rw [applicationEq, EventGraph.Config.step_cut _ _ _ _ _ reached]
  rfl

theorem quiet_guess_clock (bit guess : Bool) :
    (quietGuessIncluded bit guess).application.clock = 0 := by
  obtain ⟨next, accepted, _, applicationEq, _⟩ := quiet_guess_application bit guess
  rw [applicationEq, (handle_clock_activated nativeRuntime _ _ _ accepted).1]
  rfl

theorem quiet_guess_alice_ready (bit guess : Bool) :
    (quietGuessIncluded bit guess).application.config.cut.Ready alicePublication := by
  rw [quiet_guess_cut]
  cases bit <;> decide

def quietGuessTicked (bit guess : Bool) : nativeApp.Execution :=
  let included := quietGuessIncluded bit guess
  { included with
    application := { included.application with clock := included.application.clock + 1 }
    environmentRecall := included.environmentRecall ++
      [⟨included.observeEnvironment nativeApp, .application .advanceClock⟩] }

def quietGuessExpired (bit guess : Bool) : nativeApp.Execution :=
  let ticked := quietGuessTicked bit guess
  { ticked with environmentRecall := ticked.environmentRecall ++
      [⟨ticked.observeEnvironment nativeApp, .application (.expire bobPublication)⟩] }

def quietAliceGranted (bit guess : Bool) : nativeApp.Execution :=
  let expired := quietGuessExpired bit guess
  { expired with
    application := { expired.application with serviceGrant := some alicePublication }
    environmentRecall := expired.environmentRecall ++
      [⟨expired.observeEnvironment nativeApp, .application (.grant alicePublication)⟩] }

def quietAlice (bit guess : Bool) : nativeApp.Execution :=
  let granted := quietAliceGranted bit guess
  { granted with environmentRecall := granted.environmentRecall ++
      [⟨granted.observeEnvironment nativeApp, .activate alice⟩] }

theorem quiet_alice_ready (bit guess : Bool) :
    (quietAlice bit guess).application.config.cut.Ready alicePublication :=
  quiet_guess_alice_ready bit guess

theorem quiet_alice_timely (bit guess : Bool)
    (valid : NativeFixed bit (quietAlice bit guess).application) :
    (quietAlice bit guess).application.WithinDeadline nativeRuntime alicePublication := by
  obtain ⟨entered, activated⟩ := valid.1.activatedAt_eq_some_of_ready_actor
    alicePublication (quiet_alice_ready bit guess) (by rw [native_actor]; rfl)
  rw [State.WithinDeadline, activated]
  change (quietGuessIncluded bit guess).application.clock + 1 - entered < 2
  rw [quiet_guess_clock]
  omega

theorem quiet_guess_fixed (bit guess : Bool) :
    NativeFixed bit (quietGuessIncluded bit guess).application := by
  obtain ⟨next, accepted, _, applicationEq, _⟩ := quiet_guess_application bit guess
  rw [applicationEq]
  exact (native_fixed_invariant bit).handle (quietBob bit).application
    ⟨(bob, 0), ⟨if guess then .opening bobPublication bobHandle ⟨.bool, true⟩
      else .withhold bobPublication, none⟩⟩ next (quiet_bob_fixed bit) accepted

theorem quiet_alice_fixed (bit guess : Bool) :
    NativeFixed bit (quietAlice bit guess).application := by
  have ticked := (native_fixed_invariant bit).environment
    (quietGuessIncluded bit guess).application .advanceClock
    (quietGuessTicked bit guess).application (quiet_guess_fixed bit guess)
    (FinDist.mem_support_pure.mpr rfl)
  exact (native_fixed_invariant bit).environment (quietGuessTicked bit guess).application
    (.grant alicePublication) (quietAlice bit guess).application ticked
    (FinDist.mem_support_pure.mpr rfl)

theorem quiet_alice_serials (bit guess : Bool) :
    (quietAlice bit guess).network.SerialsBeforeNext := by
  have responded := (nativeApp.serialsBeforeNextInvariant nativeScheduler).respond
    (quietBob bit) bob (nativeGuessAction guess) (quiet_bob_serials bit)
  change ((quietGuessRespond bit guess).includePending nativeApp (bob, 0)).network.SerialsBeforeNext
  rw [nativeApp.includePending_network]
  exact responded.includePending (bob, 0)

theorem quiet_guess_tick (bit guess : Bool) :
    (quietGuessIncluded bit guess).environmentStep nativeApp (.application .advanceClock) =
      FinDist.pure (quietGuessTicked bit guess) := by
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    environmentStep, FinDist.map_pure]
  rfl

theorem quiet_guess_expiry (bit guess : Bool) :
    (quietGuessTicked bit guess).environmentStep nativeApp
      (.application (.expire bobPublication)) = FinDist.pure (quietGuessExpired bit guess) := by
  have completed : bobPublication ∈ (quietGuessTicked bit guess).application.config.cut.completed :=
    by
    change bobPublication ∈ (quietGuessIncluded bit guess).application.config.cut.completed
    rw [quiet_guess_cut, EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  have expiry := environmentStep_expire_of_not_ready nativeRuntime
    (quietGuessTicked bit guess).application bobPublication (fun ready => ready.1 completed)
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    expiry, FinDist.map_pure]
  rfl

theorem quiet_alice_grant (bit guess : Bool) :
    (quietGuessExpired bit guess).environmentStep nativeApp
      (.application (.grant alicePublication)) = FinDist.pure (quietAliceGranted bit guess) := by
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    environmentStep, FinDist.map_pure]
  rfl

theorem quiet_alice_activation (bit guess : Bool) :
    (quietAliceGranted bit guess).environmentStep nativeApp (.activate alice) =
      FinDist.pure (quietAlice bit guess) := by
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    nativeLeaks, alice, watcher, bob, show (0 : Player) ≠ 2 by decide,
    show (0 : Player) ≠ 1 by decide, ↓reduceIte, FinDist.map_pure, MessageNetwork.learn_empty]
  rfl

theorem quiet_alice_response (bit guess : Bool) :
    nativeAliceResponse ((quietAlice bit guess).observe nativeApp alice) =
      nativeOpeningAction alicePublication aliceHandle bit := by
  exact native_alice_response_eq bit (quietAlice bit guess) (quiet_alice_fixed bit guess) rfl

theorem quiet_guess_to_alice (players : Player → nativeApp.Policy)
    (prescribed : players alice = nativeAlicePolicy) (bit guess : Bool) :
    nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      [.tick, .expire bobPublication, .grant alicePublication, .player alice]
      (quietGuessIncluded bit guess) =
        FinDist.pure ((quietAlice bit guess).respond nativeApp alice
          (nativeOpeningAction alicePublication aliceHandle bit)) := by
  simp only [runInteractionPlan, interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
    quiet_guess_tick, quiet_guess_expiry, quiet_alice_grant, quiet_alice_activation,
    ReactiveApplication.resume, FinDist.pure_bind, ReactiveApplication.invoke, prescribed,
    nativeAlicePolicy, quiet_alice_response, FinDist.map_pure]

theorem quiet_guess_suffix_summary (players : Player → nativeApp.Policy)
    (prescribed : players alice = nativeAlicePolicy) (bit guess : Bool) :
    (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      ([.includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication, .player alice] ++ resolutionTail)
      (quietGuessRespond bit guess)).map
        (fun final => (nativeResults final.application.config, rejectedAlice final.receipts)) =
      FinDist.pure (Results.mk (.success bit) (guessResult guess), false) := by
  have prefixLaw : nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      [.includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication, .player alice] (quietGuessRespond bit guess) =
      FinDist.pure ((quietAlice bit guess).respond nativeApp alice
        (nativeOpeningAction alicePublication aliceHandle bit)) := by
    rw [runInteractionPlan, quiet_guess_included, FinDist.pure_bind]
    exact quiet_guess_to_alice players prescribed bit guess
  rw [runInteractionPlan_append, prefixLaw, FinDist.pure_bind]
  rw [resolution_tail_summary players (quietAlice bit guess) bit (guessResult guess)
    (quiet_alice_fixed bit guess) (quiet_guess_results bit guess).1
    (quiet_alice_ready bit guess) (quiet_alice_timely bit guess (quiet_alice_fixed bit guess))
    (quiet_alice_serials bit guess)]
  change FinDist.pure (_, rejectedAlice (quietGuessIncluded bit guess).receipts) = _
  rw [(quiet_guess_results bit guess).2]
  rfl

end VegasTests.MonitoredGuessing
