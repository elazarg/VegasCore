/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationService
import GameTheoryExtensions.Analysis.Protocol.LastDecision

/-! # Decision beliefs precede Bob's single response

For the actual finite native calendar, every player's decision precedes Bob's
only response. Therefore all decision-history reach probabilities, and hence
all Bayes beliefs, are independent of Bob's policy. Alice's responses and all
native rejected, malformed, and replay packets remain unrestricted by this
argument.
-/

noncomputable section

namespace VegasTests.CommunicationSequentialNative

open Vegas Vegas.EventGraphRuntime Interaction GameTheory
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open SequentialValidation

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
    (inactive : ¬ nativeArena.active state true) :
    nativeModel.playerStepProb profile true trace joint = 1 := by
  let := nativeModel.subsingleton_choice_of_not_active trace inactive
  change (profile true (nativeModel.infoOf true trace)).prob
    (nativeModel.choicesOfLegal trace joint true) = 1
  rw [FinDist.eq_pure_of_subsingleton (profile true (nativeModel.infoOf true trace))
    (nativeModel.choicesOfLegal trace joint true)]
  exact FinDist.prob_pure_self _

private def beforeBob : nativeApp.ProtocolState → Prop
  | none => True
  | some control => control.execution.environmentRecall.length ≤ 10 ∨
      (control.execution.environmentRecall.length = 11 ∧ control.actor = some true)

theorem player_reach_before_bob (profile : Profile nativeModel.behavioralSignature) :
    ∀ {state} (trace : nativeArena.Trace state), beforeBob state →
      nativeModel.playerReachProbability profile true trace = 1
  | _, .start, _ => rfl
  | _, .extend (source := before) prior joint legal reached, early => by
      rw [InformationModel.playerReachProbability]
      have inactive : ¬ nativeArena.active before true := by
        cases before with
        | none => intro impossible; cases impossible
        | some control =>
            intro active
            have same : control.actor = some true := active
            have position := (native_bob_remaining control prior same).1
            change _ ∈ (nativeApp.transition nativeInitialLaw 56 nativeScheduler
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
            change _ ∈ (nativeApp.transition nativeInitialLaw 56 nativeScheduler
              (some ⟨remaining, actor, execution⟩) joint).support at reached
            cases actor with
            | some who =>
                cases FinDist.mem_support_pure.mp reached
                have previous : execution.environmentRecall.length ≤ 10 := by
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
                    change execution.environmentRecall.length ≤ 10 ∨ _
                    left
                    change next.environmentRecall.length ≤ 10 ∨
                      (next.environmentRecall.length = 11 ∧ command.actor? nativeApp = some true)
                        at early
                    rw [length, List.length_append, List.length_singleton] at early
                    omega
      rw [player_reach_before_bob profile prior priorEarly,
        idle_step_probability profile prior ⟨joint, legal⟩ inactive, one_mul]

theorem native_alice_activation_position (history : List nativeApp.EnvironmentEntry)
    (view : nativeApp.EnvironmentView) (command : nativeApp.Command)
    (supported : command ∈ (nativeScheduler history view).support)
    (active : command.actor? nativeApp = some false) : history.length ≤ 7 := by
  have instruction := nativeApp.uniformInstruction_actor dependencyCondition history view
    (nativeCalendar history.length) command false supported active
  unfold nativeCalendar at instruction
  split at instruction <;> simp_all
  split at instruction <;> cases instruction

private theorem alice_position_history : ∀ {state} (_trace : nativeArena.Trace state),
    ∀ control, state = some control → control.actor = some false →
      control.execution.environmentRecall.length ≤ 8
  | _, .start, control, same, _ => by cases same
  | _, .extend (source := before) prior joint _ reached, control, same, active => by
      subst_vars
      cases before with
      | none =>
          obtain ⟨state, _, equal⟩ := FinDist.support_map .. ▸ reached
          cases equal
          cases active
      | some previous =>
          rcases previous with ⟨remaining, actor, execution⟩
          change _ ∈ (nativeApp.transition nativeInitialLaw 56 nativeScheduler
            (some ⟨remaining, actor, execution⟩) joint).support at reached
          cases actor with
          | some who =>
              cases FinDist.mem_support_pure.mp reached
              cases active
          | none =>
              cases remaining with
              | zero =>
                  cases FinDist.mem_support_pure.mp reached
                  cases active
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
                  obtain ⟨next, supported, equal⟩ := FinDist.support_map .. ▸ moved
                  cases equal
                  have length := environment_recall execution next command supported
                  have position := native_alice_activation_position execution.environmentRecall
                    (execution.observeEnvironment nativeApp) command selected active
                  change next.environmentRecall.length ≤ 8
                  rw [length, List.length_append, List.length_singleton]
                  omega

theorem decision_player_reach (profile : Profile nativeModel.behavioralSignature)
    (who : Bool) (site : nativeModel.InformationSite who)
    (history : nativeModel.InformationHistory who site.1) :
    nativeModel.playerReachProbability profile true history.1.trace = 1 := by
  have active := InformationModel.InformationSite.active nativeModel site history
  rcases history with ⟨⟨state, trace⟩, info⟩
  cases state with
  | none => cases active
  | some control =>
      have actor : control.actor = some who := active
      apply player_reach_before_bob profile trace
      cases who with
      | false => exact Or.inl (by have := alice_position_history trace control rfl actor; omega)
      | true => exact Or.inr ⟨(native_bob_remaining control trace actor).1, actor⟩

theorem decision_reach_invariant (profile : Profile nativeModel.behavioralSignature)
    (alternative : nativeModel.BehavioralPolicy true) (who : Bool)
    (site : nativeModel.InformationSite who)
    (history : nativeModel.InformationHistory who site.1) :
    nativeModel.historyReachProbability (Profile.update (sig := nativeModel.behavioralSignature)
      profile true alternative) history.1 =
      nativeModel.historyReachProbability profile history.1 := by
  rw [nativeModel.historyReachProbability_eq_player_mul_counterfactual _ true history.1.trace,
    nativeModel.historyReachProbability_eq_player_mul_counterfactual _ true history.1.trace,
    decision_player_reach _ who site history, decision_player_reach _ who site history]
  congr 1
  exact nativeModel.counterfactualReachProbability_eq_of_eq_off
    (fun player different => Profile.update_of_ne _ _ different) history.1.trace

private def afterBob : nativeApp.ProtocolState → Prop
  | none => False
  | some control => 11 ≤ control.execution.environmentRecall.length ∧
      (control.execution.environmentRecall.length = 11 → control.actor = none)

private theorem afterBob_transition (before after : nativeApp.ProtocolState)
    (joint : Bool → Option nativeApp.Action) (valid : afterBob before)
    (reached : after ∈
      (nativeApp.transition nativeInitialLaw 56 nativeScheduler before joint).support) :
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
              change 11 ≤ next.environmentRecall.length ∧ _
              have lower := valid.1
              change 11 ≤ execution.environmentRecall.length at lower
              rw [length, List.length_append, List.length_singleton]
              exact ⟨by omega, by intro impossible; omega⟩

private theorem afterBob_reaches {first last : nativeArena.History} {fuel : Nat}
    (path : nativeArena.ReachesWithin fuel first last) (valid : afterBob first.state) :
    afterBob last.state := by
  induction path with
  | refl => exact valid
  | step joint legal realized suffix ih =>
      exact ih (afterBob_transition _ _ joint valid realized)

theorem bob_last_decision : InformationModel.LastDecision (E := nativeArena) true := by
  intro history active joint legal target realized fuel later path
  cases state : history.state with
  | none => rw [state] at active; cases active
  | some control =>
      have trace : nativeArena.Trace (some control) := state ▸ history.trace
      have actor : control.actor = some true := by
        rw [state] at active
        exact active
      have position := (native_bob_remaining control trace actor).1
      have moved := realized
      change target ∈ (nativeApp.transition nativeInitialLaw 56 nativeScheduler
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
          have nextActor : next.actor = some true := by
            rw [ending] at acts
            exact acts
          have nextPosition := (native_bob_remaining next nextTrace nextActor).1
          rw [ending] at final
          have inactive := final.2 nextPosition
          rw [nextActor] at inactive
          cases inactive

end VegasTests.CommunicationSequentialNative
