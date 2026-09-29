/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.RestrictedSupport
import Vegas.Examples.MonitoredGuessing.NativeInitial

/-! # Exhaustive restricted sender checkpoints

Uniform legal responses give every restricted history positive support. The
actual nine-round prefix then classifies every final sender input by the same
initial bit and receiver choice used by the source program.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem bob_to_granted_alice (players : Player → nativeApp.Policy) (bit guess : Bool) :
    nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      [.includeLatest bobPublication bob, .tick, .expire bobPublication, .grant alicePublication]
      ((quietBob bit).respond nativeApp bob (choiceAction bobPublication bobHandle true guess)) =
      PMF.pure (grantedAlice bit guess) := by
  change nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
    ([.includeLatest bobPublication bob, .tick, .expire bobPublication] ++
      [.grant alicePublication]) _ = _
  rw [runInteractionPlan_append, bob_service, PMF.pure_bind]
  simp only [runInteractionPlan, interactionStep, interactionInstruction, PMF.pure_bind,
    ReactiveApplication.dispatch, grant_alice]
  rw [show (ReactiveApplication.Command.application (.grant alicePublication) :
    nativeApp.Command).actor? nativeApp = none from rfl,
    ReactiveApplication.resume, PMF.pure_bind]

theorem reference_receiver_support (bit : Bool) (execution : nativeApp.Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan nativeLeaks
      restrictedMenu.uniformResponses nativeNetwork
      [.player bob, .includeLatest bobPublication bob, .tick, .expire bobPublication,
        .grant alicePublication] (quietGranted bit)).support) :
    ∃ guess, execution = grantedAlice bit guess := by
  classical
  change execution ∈ ((nativeRuntime.interactionStep nativeLeaks
    restrictedMenu.uniformResponses nativeNetwork (.player bob) (quietGranted bit)).bind _).support
    at reached
  have activated : nativeRuntime.interactionStep nativeLeaks restrictedMenu.uniformResponses
      nativeNetwork (.player bob) (quietGranted bit) =
        (restrictedMenu.uniformResponses bob ((quietBob bit).recall bob)
          ((quietBob bit).observe nativeApp bob)).map ((quietBob bit).respond nativeApp bob) := by
    simp only [interactionStep, interactionInstruction, PMF.pure_bind,
      ReactiveApplication.dispatch, quiet_bob_activation]
    rfl
  rw [activated, PMF.bind_map, PMF.support_bind] at reached
  obtain ⟨response, responseMem, finished⟩ := Set.mem_iUnion₂.mp reached
  have permitted := (restrictedMenu.uniformResponses_support bob _ _ response).mp responseMem
  rw [bob_actions, Finset.mem_insert, Finset.mem_singleton] at permitted
  rcases permitted with rfl | rfl
  · refine ⟨false, ?_⟩
    have law := bob_to_granted_alice restrictedMenu.uniformResponses bit false
    simp only [choiceAction, Bool.false_eq_true, ↓reduceIte] at law
    rw [law] at finished
    exact (PMF.mem_support_pure_iff _ _).mp finished
  · refine ⟨true, ?_⟩
    have law := bob_to_granted_alice restrictedMenu.uniformResponses bit true
    simp only [choiceAction, ↓reduceIte] at law
    rw [law] at finished
    exact (PMF.mem_support_pure_iff _ _).mp finished

theorem reference_rounds_nine_support (execution : nativeApp.Execution)
    (reached : execution ∈ (nativeApp.roundsFrom nativeInitialLaw nativeScheduler
      restrictedMenu.uniformResponses 9).support) :
    ∃ bit guess, execution = grantedAlice bit guess := by
  rw [ReactiveApplication.roundsFrom, nativeInitialLaw, PMF.bind_map,
    PMF.support_bind] at reached
  obtain ⟨bit, _, reached⟩ := Set.mem_iUnion₂.mp reached
  change execution ∈ (nativeApp.runRounds nativeScheduler restrictedMenu.uniformResponses
    9 (nativeStart bit)).support at reached
  have rounds := native_segment_rounds restrictedMenu.uniformResponses []
    (nativePlan.take 9) (nativePlan.drop 9) (by simp) (nativeStart bit) rfl
  change nativeApp.runRounds nativeScheduler restrictedMenu.uniformResponses 9 (nativeStart bit) =
    nativeRuntime.runInteractionPlan nativeLeaks restrictedMenu.uniformResponses nativeNetwork
      ([.player alice, .player watcher, .wire, .grant bobPublication] ++
        [.player bob, .includeLatest bobPublication bob, .tick, .expire bobPublication,
          .grant alicePublication]) (nativeStart bit) at rounds
  rw [rounds, runInteractionPlan_append, reference_quiet_prefix, PMF.pure_bind] at reached
  obtain ⟨guess, same⟩ := reference_receiver_support bit execution reached
  exact ⟨bit, guess, same⟩

/-- Every final-Alice legal control is one of the four source decision inputs. -/
theorem final_alice_control (control : nativeApp.Control)
    (trace : restrictedArena.Trace (some control)) (active : control.actor = some alice)
    (position : control.execution.environmentRecall.length = 10) :
    ∃ bit guess, control = ⟨4, some alice, beforeAlice bit guess⟩ := by
  have supported := restrictedMenu.roundSupported_uniform nativeInitialLaw nativeHorizon
    nativeScheduler trace
  rcases control with ⟨remaining, actor, execution⟩
  change actor = some alice at active
  subst actor
  obtain ⟨accounted, count, prior, command, advanced, priorMem, selected, acting, moved⟩ :=
    supported
  have countEq : count = 9 := by omega
  subst count
  obtain ⟨bit, guess, rfl⟩ := reference_rounds_nine_support prior priorMem
  have commandEq : command = .activate alice := by
    cases command with
    | activate who => cases Option.some.inj acting; rfl
    | «include» id | application command | wait => cases acting
  subst command
  rw [activate_alice, PMF.mem_support_pure_iff _ _] at moved
  change execution = beforeAlice bit guess at moved
  subst execution
  have remainingEq : remaining = 4 := by
    change (beforeAlice bit guess).environmentRecall.length + remaining = 14 at accounted
    change (beforeAlice bit guess).environmentRecall.length = 10 at position
    omega
  subst remaining
  exact ⟨bit, guess, rfl⟩

theorem alice_control (control : nativeApp.Control)
    (trace : restrictedArena.Trace (some control)) (active : control.actor = some alice) :
    (∃ bit, control = ⟨13, some alice, aliceActivated bit⟩) ∨
      ∃ bit guess, control = ⟨4, some alice, beforeAlice bit guess⟩ := by
  have supported := restrictedMenu.roundSupported_uniform nativeInitialLaw nativeHorizon
    nativeScheduler trace
  rcases control with ⟨remaining, actor, execution⟩
  change actor = some alice at active
  subst actor
  obtain ⟨accounted, count, prior, command, advanced, priorMem, selected, acting, moved⟩ :=
    supported
  have cursor := nativeApp.roundsFrom_recall nativeInitialLaw nativeScheduler
    restrictedMenu.uniformResponses count prior priorMem
  have possible := native_alice_activation_positions prior.environmentRecall
    (prior.observeEnvironment nativeApp) command selected acting
  rw [cursor] at possible
  rcases possible with early | late
  · rw [early] at priorMem
    left
    change prior ∈ (nativeInitialLaw.bind fun initial =>
      PMF.pure (ReactiveApplication.Execution.initial nativeApp initial)).support at priorMem
    rw [← ← PMF.bind_pure_comp, Function.comp_def, nativeInitialLaw, PMF.map_comp, PMF.support_map] at priorMem
    obtain ⟨bit, _, rfl⟩ := priorMem
    have commandEq : command = .activate alice := (PMF.mem_support_pure_iff _ _).mp selected
    subst command
    change execution ∈ ((nativeStart bit).environmentStep nativeApp (.activate alice)).support
      at moved
    rw [initial_activation, PMF.mem_support_pure_iff _ _] at moved
    subst execution
    have remainingEq : remaining = 13 := by
      change 1 + remaining = 14 at accounted
      omega
    subst remaining
    exact ⟨bit, rfl⟩
  · right
    apply final_alice_control _ trace rfl
    change execution.environmentRecall.length = 10
    change execution.environmentRecall.length = count + 1 at advanced
    omega

theorem alice_site_cases (site : restrictedModel.InformationSite alice) :
    (∃ bit, site.1 = some ([], (aliceActivated bit).observe nativeApp alice)) ∨
      ∃ bit guess, site.1 = aliceInput bit guess := by
  obtain ⟨history, _, _⟩ := site.2
  have active := InformationModel.InformationSite.active restrictedModel site history
  rcases history with ⟨⟨state, trace⟩, observed⟩
  cases state with
  | none => cases active
  | some control =>
      rcases alice_control control trace active with ⟨bit, rfl⟩ | ⟨bit, guess, rfl⟩
      · exact Or.inl ⟨bit, observed.symm.trans
          (restrictedMenu.info nativeInitialLaw nativeHorizon nativeScheduler alice trace)⟩
      · exact Or.inr ⟨bit, guess, observed.symm.trans
          (restrictedMenu.info nativeInitialLaw nativeHorizon nativeScheduler alice trace)⟩

theorem final_alice_known_state (bit guess : Bool)
    (history : restrictedModel.InformationHistory alice (aliceInput bit guess)) :
    history.1.state = some ⟨4, some alice, beforeAlice bit guess⟩ := by
  rcases history with ⟨⟨state, trace⟩, observed⟩
  change (restrictedMenu.signals nativeInitialLaw nativeHorizon nativeScheduler).infoOf
    alice trace = aliceInput bit guess at observed
  rw [restrictedMenu.info] at observed
  cases state with
  | none => cases observed
  | some control =>
      have active : control.actor = some alice := by
        by_contra inactive
        simp only [ReactiveApplication.observe, inactive, ↓reduceIte] at observed
        cases observed
      have actualInput : some (control.execution.recall alice,
          control.execution.observe nativeApp alice) = aliceInput bit guess := by
        simpa only [ReactiveApplication.observe, active, ↓reduceIte] using observed
      rcases alice_control control trace active with ⟨other, rfl⟩ | ⟨other, decision, rfl⟩
      · have grants := congrArg (fun info : nativeApp.Info =>
          info.bind fun pair => pair.2.application.publicView.serviceGrant) actualInput
        change none = some alicePublication at grants
        cases grants
      · obtain ⟨rfl, rfl⟩ := (alice_input_eq_iff other decision bit guess).mp actualInput
        rfl

end Vegas.Examples.MonitoredGuessing.Restricted
