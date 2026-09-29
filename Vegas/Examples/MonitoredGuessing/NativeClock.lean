/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.NativeDepth
import Vegas.Examples.MonitoredGuessing.NativeInitial
import GameTheory.Analysis.Protocol.CounterfactualDecomposition

/-! # Common decision depths in the actual native fixture

The fixed activation roster, existing service grants and existing decision
recall determine one trace depth for each information site. This certificate
covers arbitrary raw responses and passive observations. It adds no clock or
other information to a player's view.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private def scheduledActivations (count : Nat) : Nat :=
  if count = 0 then 0 else if count = 1 then 1 else if count ≤ 4 then 2
    else if count ≤ 9 then 3 else 4

private theorem scheduled_activation_count (history : List nativeApp.EnvironmentEntry)
    (view : nativeApp.EnvironmentView) (command : nativeApp.Command)
    (supported : command ∈ (nativeScheduler history view).support) :
    scheduledActivations (history.length + 1) = scheduledActivations history.length +
      (command.actor? nativeApp).toList.length := by
  unfold nativeScheduler at supported
  cases selected : nativePlan[history.length]? with
  | none =>
      rw [selected, PMF.mem_support_pure_iff _ _] at supported
      subst command
      have bound : 14 ≤ history.length := by
        simpa only [← native_horizon] using List.getElem?_eq_none_iff.mp selected
      have nonzero : history.length ≠ 0 := by omega
      have notOne : history.length ≠ 1 := by omega
      have notFour : ¬history.length ≤ 4 := by omega
      have notNine : ¬history.length ≤ 9 := by omega
      simp [scheduledActivations, nonzero, notOne, notFour, notNine,
        show ¬history.length + 1 ≤ 4 by omega,
        show ¬history.length + 1 ≤ 9 by omega, ReactiveApplication.Command.actor?]
  | some instruction =>
      rw [selected] at supported
      have actor := native_instruction_actor_eq history view instruction command supported
      have bound : history.length < 14 := by
        simpa only [← native_horizon] using (List.getElem?_eq_some_iff.mp selected).1
      have table : ∀ index : Fin 14,
          scheduledActivations (index.val + 1) = scheduledActivations index.val +
            ((nativePlan[index.val]?).bind instructionPlayer).toList.length := by decide
      have counted := table ⟨history.length, bound⟩
      simpa only [selected, Option.bind_some, actor] using counted

private def CountedDepth (state : nativeApp.ProtocolState) (depth : Nat) : Prop :=
  match state with
  | none => depth = 0
  | some control => depth + control.actor.toList.length =
      1 + control.execution.environmentRecall.length +
        scheduledActivations control.execution.environmentRecall.length

private theorem trace_counted_depth :
    ∀ {state} (trace : nativeArena.Trace state), CountedDepth state trace.length
  | _, .start => rfl
  | _, @Trace.extend _ _ source target before joint legal realized => by
      have inherited := trace_counted_depth before
      have reached : target ∈ (nativeApp.transition nativeInitialLaw nativeHorizon
        nativeScheduler source joint).support := realized
      cases source with
      | none =>
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ reached
          have counted : before.length = 0 := inherited
          simpa only [CountedDepth, Trace.length, ReactiveApplication.Execution.initial,
            List.length_nil, Option.toList_none, Nat.add_zero, scheduledActivations,
            ↓reduceIte] using congrArg (· + 1) counted
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              simpa only [CountedDepth, Trace.length, nativeApp.respond_environmentRecall,
                Option.toList_some, Option.toList_none, List.length_singleton,
                List.length_nil, Nat.add_zero] using inherited
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  have schedulerRecall : next.environmentRecall = execution.environmentRecall ++
                      [⟨execution.observeEnvironment nativeApp, command⟩] := by
                    obtain ⟨updated, _, equal⟩ := PMF.support_map .. ▸ supported
                    cases equal
                    rfl
                  have activations := scheduled_activation_count execution.environmentRecall
                    (execution.observeEnvironment nativeApp) command selected
                  simp only [CountedDepth, Option.toList_none, List.length_nil, Nat.add_zero]
                    at inherited
                  simp only [CountedDepth, Trace.length, schedulerRecall, List.length_append,
                    List.length_singleton, activations]
                  omega

theorem native_initial_alice_information_depth (bit : Bool)
    (history : nativeModel.InformationHistory alice (initialAliceSite bit).1) :
    history.1.trace.length = 2 := by
  have stateEq := initial_alice_information_control bit history
  rcases history with ⟨⟨state, trace⟩, information⟩
  change state = some (initialAliceControl bit) at stateEq
  subst state
  have counted := trace_counted_depth trace
  change trace.length + 1 = 1 + 1 + scheduledActivations 1 at counted
  norm_num [scheduledActivations] at counted
  omega

theorem native_final_alice_information_depth (site : nativeModel.InformationSite alice)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (viewed : site.1 = some (past, view))
    (granted : view.application.publicView.serviceGrant = some alicePublication)
    (history : nativeModel.InformationHistory alice site.1) :
    history.1.trace.length = 14 := by
  obtain ⟨control, stateEq, active, _, observed⟩ := native_information_control alice past view
    ⟨history.1, history.2.trans viewed⟩
  rcases history with ⟨⟨state, trace⟩, information⟩
  change state = some control at stateEq
  subst state
  rcases native_alice_calendar control trace active with early | late
  · obtain ⟨bit, same⟩ := native_alice_initial_representation control trace active early.1
    subst control
    have actualGrant := congrArg (fun observed : nativeApp.PlayerView =>
      observed.application.publicView.serviceGrant) observed
    change none = view.application.publicView.serviceGrant at actualGrant
    rw [granted] at actualGrant
    cases actualGrant
  · have counted := trace_counted_depth trace
    change trace.length + control.actor.toList.length = _ at counted
    rw [active, late.1] at counted
    norm_num [scheduledActivations] at counted
    omega

theorem native_watcher_activation_position (history : List nativeApp.EnvironmentEntry)
    (view : nativeApp.EnvironmentView) (command : nativeApp.Command)
    (supported : command ∈ (nativeScheduler history view).support)
    (active : command.actor? nativeApp = some watcher) : history.length = 1 := by
  unfold nativeScheduler at supported
  cases selected : nativePlan[history.length]? with
  | none =>
      rw [selected, PMF.mem_support_pure_iff _ _] at supported
      subst command
      cases active
  | some instruction =>
      rw [selected] at supported
      have actor := (native_instruction_actor_eq history view instruction command supported).symm
        |>.trans active
      have bounded : history.length < nativePlan.length :=
        (List.getElem?_eq_some_iff.mp selected).1
      have table : ∀ index : Fin nativePlan.length,
          (nativePlan[index.val]?).bind instructionPlayer = some watcher → index.val = 1 := by
        decide
      apply table ⟨history.length, bounded⟩
      rw [selected]
      exact actor

theorem native_watcher_information_depth (site : nativeModel.InformationSite watcher)
    (history : nativeModel.InformationHistory watcher site.1) : history.1.trace.length = 4 := by
  have active := InformationModel.InformationSite.active nativeModel site history
  rcases history with ⟨⟨state, trace⟩, observed⟩
  cases state with
  | none => cases active
  | some control =>
      have acting : control.actor = some watcher := active
      have position := nativeApp.remaining_at_activation nativeInitialLaw nativeHorizon
        nativeScheduler watcher 1 native_watcher_activation_position control
        (nativeMenu.toRawTrace nativeInitialLaw nativeHorizon nativeScheduler trace) active
      have counted := trace_counted_depth trace
      change trace.length + control.actor.toList.length = _ at counted
      rw [acting, position.1] at counted
      norm_num [scheduledActivations] at counted
      omega

/-- A theorem-side evaluator depth, obtained from information already in the model. -/
def nativeDecisionDepth (who : Player) (site : nativeModel.InformationSite who) : Nat :=
  if who = bob then 8 else if who = watcher then 4 else
    match site.1 with
    | none => 2
    | some (_, view) => if view.application.publicView.serviceGrant = none then 2 else 14

theorem native_common_decision_depth (who : Player) (site : nativeModel.InformationSite who) :
    InformationModel.InformationSite.CommonDepth nativeModel site (nativeDecisionDepth who site) :=
    by
  fin_cases who
  · change InformationModel.InformationSite.CommonDepth nativeModel
      (site : nativeModel.InformationSite alice) (nativeDecisionDepth alice site)
    rcases native_alice_site_cases site with ⟨bit, rfl⟩ | ⟨past, view, viewed, granted⟩
    · exact native_initial_alice_information_depth bit
    · intro history
      have depth := native_final_alice_information_depth site past view viewed granted history
      simpa only [nativeDecisionDepth, alice, bob, watcher, show (0 : Player) ≠ 1 by decide,
        show (0 : Player) ≠ 2 by decide, ↓reduceIte, viewed, granted, reduceCtorEq] using depth
  · exact native_bob_information_depth site
  · exact native_watcher_information_depth site

end Vegas.Examples.MonitoredGuessing
