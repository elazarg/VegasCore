/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingNative
import Interaction.ReactiveCalendar
import GameTheoryExtensions.Analysis.Protocol.LastDecision

/-! # Bob's single native decision

The actual scheduler activates Bob once. His decision beliefs consequently
precede every use of his policy; Alice's later beliefs may depend on it.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem native_instruction_actor (history : List nativeApp.EnvironmentEntry)
    (view : nativeApp.EnvironmentView) (instruction : ServiceInstruction nativeGraph)
    (command : nativeApp.Command)
    (supported : command ∈ (nativeRuntime.interactionInstruction nativeLeaks nativeNetwork
      history view instruction).support)
    (active : command.actor? nativeApp = some bob) : instruction = .player bob := by
  cases instruction with
  | player who =>
      simp only [interactionInstruction, FinDist.mem_support_pure] at supported
      subst command
      simpa only [ReactiveApplication.Command.actor?, Option.some.injEq] using
        congrArg ServiceInstruction.player (Option.some.inj active)
  | wire =>
      simp only [interactionInstruction, nativeNetwork, FinDist.map_pure,
        FinDist.mem_support_pure] at supported
      subst command
      cases last : view.network.inputs.getLast? with
      | none =>
          simp only [last, NetworkChoice.command, ReactiveApplication.atMostOnceCommand,
            ReactiveApplication.Command.actor?, reduceCtorEq] at active
      | some input =>
          by_cases report : input.broadcaster = watcher ∧ input.envelope.sender = alice
          · simp only [last, ite_eq_left report, NetworkChoice.command] at active
            change (if view.Unpublished nativeApp input.envelope.id then
              ReactiveApplication.Command.include input.envelope.id else
                ReactiveApplication.Command.wait).actor? nativeApp = some bob at active
            by_cases fresh : view.Unpublished nativeApp input.envelope.id
            · rw [ite_eq_left fresh] at active; cases active
            · rw [ite_eq_right fresh] at active; cases active
          · simp only [last, report, ↓reduceIte, NetworkChoice.command,
              ReactiveApplication.atMostOnceCommand, ReactiveApplication.Command.actor?,
              reduceCtorEq] at active
  | includeLatest event owner =>
      simp only [interactionInstruction, FinDist.mem_support_pure] at supported
      subst command
      unfold reactiveLatest at active
      split at active <;> cases active
  | grant event | sample event | tick | expire event =>
      simp only [interactionInstruction, FinDist.mem_support_pure] at supported
      subst command
      cases active

theorem native_unique_bob_activation (history : List nativeApp.EnvironmentEntry)
    (view : nativeApp.EnvironmentView) (command : nativeApp.Command)
    (supported : command ∈ (nativeScheduler history view).support)
    (active : command.actor? nativeApp = some bob) : history.length = 4 := by
  unfold nativeScheduler at supported
  cases selected : nativePlan[history.length]? with
  | none =>
      simp only [selected, FinDist.mem_support_pure] at supported
      subst command
      cases active
  | some instruction =>
      rw [selected] at supported
      have only := native_instruction_actor history view instruction command supported active
      subst instruction
      have bounded : history.length < 14 := by
        have := List.getElem?_eq_some_iff.mp selected
        simpa only [← native_horizon] using this.1
      generalize size : history.length = index at *
      have count : nativeGraph.order.eventCount = 2 := rfl
      interval_cases index
      all_goals first | rfl | norm_num [nativePlan, nativeVisit, nativeOwner, nativeRuntime,
        bobPublication, alicePublication, alice, bob, watcher, count] at selected

theorem native_bob_remaining (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some bob) :
    control.execution.environmentRecall.length = 5 ∧ control.remaining = 9 := by
  have accounted := nativeApp.remaining_at_activation nativeInitialLaw nativeHorizon
    nativeScheduler bob 4 native_unique_bob_activation control
      (nativeMenu.toRawTrace nativeInitialLaw nativeHorizon nativeScheduler trace) active
  exact ⟨accounted.1, by have := accounted.2; rw [native_horizon] at this; omega⟩

theorem native_bob_allNonterminal (site : nativeModel.InformationSite bob) :
    site.AllNonterminal :=
  nativeMenu.informationSite_allNonterminal nativeInitialLaw nativeHorizon nativeScheduler bob site

private theorem environment_recall (execution next : nativeApp.Execution)
    (command : nativeApp.Command)
    (supported : next ∈ (execution.environmentStep nativeApp command).support) :
    next.environmentRecall = execution.environmentRecall ++
      [⟨execution.observeEnvironment nativeApp, command⟩] := by
  obtain ⟨updated, _, rfl⟩ := FinDist.support_map .. ▸ supported
  rfl

private theorem idle_step_probability
    (profile : Profile nativeModel.behavioralSignature) {state : nativeArena.State}
    (trace : nativeArena.Trace state)
    (joint : { action : ∀ who, Option (nativeArena.Action who) // nativeArena.Legal state action })
    (inactive : ¬ nativeArena.active state bob) :
    nativeModel.playerStepProb profile bob trace joint = 1 := by
  let := nativeModel.subsingleton_choice_of_not_active trace inactive
  change (profile bob (nativeModel.infoOf bob trace)).prob
    (nativeModel.choicesOfLegal trace joint bob) = 1
  rw [FinDist.eq_pure_of_subsingleton (profile bob (nativeModel.infoOf bob trace))
    (nativeModel.choicesOfLegal trace joint bob)]
  exact FinDist.prob_pure_self _

private def beforeBob : nativeApp.ProtocolState → Prop
  | none => True
  | some control => control.execution.environmentRecall.length ≤ 4 ∨
      (control.execution.environmentRecall.length = 5 ∧ control.actor = some bob)

theorem player_reach_before_bob (profile : Profile nativeModel.behavioralSignature) :
    ∀ {state} (trace : nativeArena.Trace state), beforeBob state →
      nativeModel.playerReachProbability profile bob trace = 1
  | _, .start, _ => rfl
  | _, .extend (source := before) prior joint legal reached, early => by
      rw [InformationModel.playerReachProbability]
      have inactive : ¬ nativeArena.active before bob := by
        cases before with
        | none => intro impossible; cases impossible
        | some control =>
            intro active
            have same : control.actor = some bob := active
            have position := (native_bob_remaining control prior same).1
            change _ ∈ (nativeApp.transition nativeInitialLaw nativeHorizon nativeScheduler
              (some control) joint).support at reached
            simp only [ReactiveApplication.transition, same, FinDist.mem_support_pure] at reached
            subst_vars
            simp only [beforeBob, nativeApp.respond_environmentRecall, position,
              Nat.reduceLeDiff, reduceCtorEq, and_false, or_self] at early
      have priorEarly : beforeBob before := by
        cases before with
        | none => trivial
        | some control =>
            rcases control with ⟨remaining, actor, execution⟩
            change _ ∈ (nativeApp.transition nativeInitialLaw nativeHorizon nativeScheduler
              (some ⟨remaining, actor, execution⟩) joint).support at reached
            cases actor with
            | some who =>
                cases FinDist.mem_support_pure.mp reached
                have previous : execution.environmentRecall.length ≤ 4 := by
                  simpa only [beforeBob, nativeApp.respond_environmentRecall,
                    reduceCtorEq, and_false, or_false] using early
                exact Or.inl previous
            | none =>
                cases remaining with
                | zero => cases FinDist.mem_support_pure.mp reached; exact early
                | succ remaining =>
                    obtain ⟨command, _, moved⟩ :=
                      Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
                    obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ moved
                    have length := environment_recall execution next command supported
                    change execution.environmentRecall.length ≤ 4 ∨ _
                    left
                    change next.environmentRecall.length ≤ 4 ∨
                      (next.environmentRecall.length = 5 ∧ command.actor? nativeApp = some bob)
                        at early
                    rw [length, List.length_append, List.length_singleton] at early
                    omega
      rw [player_reach_before_bob profile prior priorEarly,
        idle_step_probability profile prior ⟨joint, legal⟩ inactive, one_mul]

theorem bob_decision_player_reach (profile : Profile nativeModel.behavioralSignature)
    (site : nativeModel.InformationSite bob)
    (history : nativeModel.InformationHistory bob site.1) :
    nativeModel.playerReachProbability profile bob history.1.trace = 1 := by
  have active := InformationModel.InformationSite.active nativeModel site history
  rcases history with ⟨⟨state, trace⟩, info⟩
  cases state with
  | none => cases active
  | some control =>
      have actor : control.actor = some bob := active
      exact player_reach_before_bob profile trace
        (Or.inr ⟨(native_bob_remaining control trace actor).1, actor⟩)

theorem bob_decision_reach_invariant (profile : Profile nativeModel.behavioralSignature)
    (alternative : nativeModel.BehavioralPolicy bob)
    (site : nativeModel.InformationSite bob)
    (history : nativeModel.InformationHistory bob site.1) :
    nativeModel.historyReachProbability (Profile.update (sig := nativeModel.behavioralSignature)
      profile bob alternative) history.1 =
      nativeModel.historyReachProbability profile history.1 := by
  rw [nativeModel.historyReachProbability_eq_player_mul_counterfactual _ bob history.1.trace,
    nativeModel.historyReachProbability_eq_player_mul_counterfactual _ bob history.1.trace,
    bob_decision_player_reach _ site history, bob_decision_player_reach _ site history]
  congr 1
  exact nativeModel.counterfactualReachProbability_eq_of_eq_off
    (fun player different => Profile.update_of_ne _ _ different) history.1.trace

private def afterBob : nativeApp.ProtocolState → Prop
  | none => False
  | some control => 5 ≤ control.execution.environmentRecall.length ∧
      (control.execution.environmentRecall.length = 5 → control.actor = none)

private theorem afterBob_transition (before after : nativeApp.ProtocolState)
    (joint : Player → Option nativeApp.Action) (valid : afterBob before)
    (reached : after ∈
      (nativeApp.transition nativeInitialLaw nativeHorizon nativeScheduler before joint).support) :
    afterBob after := by
  cases before with
  | none => exact valid.elim
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases FinDist.mem_support_pure.mp reached
          exact ⟨by simpa only [nativeApp.respond_environmentRecall] using valid.1,
            fun _ => rfl⟩
      | none =>
          cases remaining with
          | zero => cases FinDist.mem_support_pure.mp reached; exact valid
          | succ remaining =>
              obtain ⟨command, _, moved⟩ :=
                Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ moved
              have length := environment_recall execution next command supported
              change 5 ≤ next.environmentRecall.length ∧ _
              have lower := valid.1
              change 5 ≤ execution.environmentRecall.length at lower
              rw [length, List.length_append, List.length_singleton]
              exact ⟨by omega, by intro impossible; omega⟩

private theorem afterBob_reaches {first last : nativeArena.History} {fuel : Nat}
    (path : nativeArena.ReachesWithin fuel first last) (valid : afterBob first.state) :
    afterBob last.state := by
  induction path with
  | refl => exact valid
  | step joint legal realized suffix ih =>
      exact ih (afterBob_transition _ _ joint valid realized)

theorem native_bob_last_decision : InformationModel.LastDecision (E := nativeArena) bob := by
  intro history active joint legal target realized fuel later path
  cases state : history.state with
  | none => rw [state] at active; cases active
  | some control =>
      have trace : nativeArena.Trace (some control) := state ▸ history.trace
      have actor : control.actor = some bob := by
        rw [state] at active
        exact active
      have position := (native_bob_remaining control trace actor).1
      have moved := realized
      change target ∈ (nativeApp.transition nativeInitialLaw nativeHorizon nativeScheduler
        history.state joint).support at moved
      rw [state] at moved
      simp only [ReactiveApplication.transition, actor, FinDist.mem_support_pure] at moved
      have initial : afterBob (history.extend legal realized).state := by
        change afterBob target
        rw [moved]
        exact ⟨by rw [nativeApp.respond_environmentRecall, position], fun _ => rfl⟩
      have final := afterBob_reaches path initial
      intro acts
      cases ending : later.state with
      | none => simp [afterBob, ending] at final
      | some next =>
          have nextTrace : nativeArena.Trace (some next) := ending ▸ later.trace
          have nextActor : next.actor = some bob := by
            rw [ending] at acts
            exact acts
          have nextPosition := (native_bob_remaining next nextTrace nextActor).1
          rw [ending] at final
          have inactive := final.2 nextPosition
          rw [nextActor] at inactive
          cases inactive

end VegasTests.MonitoredGuessing
