/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationHistory

/-! # The public grant determines the native decision cursor

These facts apply to every legal history, including histories outside an
assessment's support. The two ambient prelude responses have no grant; each
later activation follows the unique grant of its source event.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

private def responseOwner : ServiceInstruction nativeGraph → Option Player
  | .player who => some who
  | _ => none

private theorem instruction_actor (instruction : ServiceInstruction nativeGraph)
    (history : List nativeApp.EnvironmentEntry) (view : nativeApp.EnvironmentView)
    (command : nativeApp.Command)
    (supported : command ∈ (nativeRuntime.interactionInstruction nativeLeaks nativeNetwork
      history view instruction).support) :
    command.actor? nativeApp = responseOwner instruction := by
  cases instruction with
  | player who | grant event | sample event | tick | expire event =>
      cases FinDist.mem_support_pure.mp supported
      rfl
  | wire =>
      simp only [interactionInstruction, nativeNetwork, FinDist.map_pure,
        FinDist.mem_support_pure] at supported
      subst command
      rfl
  | includeLatest event owner =>
      cases FinDist.mem_support_pure.mp supported
      unfold reactiveLatest
      split <;> rfl

private theorem player_positions (count : Nat) (who : Player)
    (bounded : count < nativePlan.length)
    (selected : (nativePlan[count]?).bind responseOwner = some who) :
    count = 0 ∨ count = 1 ∨ ∃ event : nativeGraph.EventId,
      count = (nativeBeforeResponse event).length ∧ who = nativeOwner event := by
  have all : ∀ cursor : Fin nativePlan.length, ∀ actor : Player,
      (nativePlan[cursor.val]?).bind responseOwner = some actor →
        cursor.val = 0 ∨ cursor.val = 1 ∨ ∃ event : nativeGraph.EventId,
          cursor.val = (nativeBeforeResponse event).length ∧ actor = nativeOwner event := by
    decide
  exact all ⟨count, bounded⟩ who selected

theorem native_response_grant (execution : nativeApp.Execution) (who : Player)
    (response : nativeApp.Action) :
    (execution.respond nativeApp who response).application.serviceGrant =
      execution.application.serviceGrant := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay id => rfl
      | submit material =>
          change (submitStep (material.call.register execution.application who) who
            material.call.packet).serviceGrant = _
          rw [submitStep_serviceGrant]
          exact congrArg PublicView.serviceGrant
            (material.call.register_facts who execution.application).2.2

theorem native_activation_grant (execution next : nativeApp.Execution) (who : Player)
    (reached : next ∈ (execution.environmentStep nativeApp (.activate who)).support) :
    next.application.serviceGrant = execution.application.serviceGrant := by
  obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
  obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
  rfl

private theorem prelude_grant (count : Nat) (early : count = 0 ∨ count = 1)
    (execution : nativeApp.Execution)
    (reached : execution ∈ (nativeApp.roundsFrom (FinDist.pure nativeInitial)
      nativeScheduler nativeMenu.uniformResponses count).support) :
    execution.application.serviceGrant = none := by
  rcases early with rfl | rfl
  · simp only [ReactiveApplication.roundsFrom, FinDist.pure_bind,
      ReactiveApplication.runRounds, FinDist.mem_support_pure] at reached
    subst execution
    rfl
  · change execution ∈ (nativeApp.roundsFrom (FinDist.pure nativeInitial)
      nativeScheduler nativeMenu.uniformResponses
      ([.player alice] : List (ServiceInstruction nativeGraph)).length).support at reached
    rw [native_roundsFrom_prefix nativeMenu.uniformResponses [.player alice]
      nativePlan.tail (by rfl)] at reached
    simp only [runInteractionPlan, interactionStep, interactionInstruction,
      FinDist.pure_bind, FinDist.bind_pure] at reached
    obtain ⟨observed, observedMem, invoked⟩ :=
      Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
    obtain ⟨response, _, rfl⟩ := FinDist.support_map .. ▸ invoked
    rw [native_response_grant]
    exact native_activation_grant nativeRoot observed alice observedMem

theorem native_response_prefix_grant (players : Player → nativeApp.Policy)
    (event : nativeGraph.EventId) (execution : nativeApp.Execution)
    (reached : execution ∈ (nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      (nativeBeforeResponse event) nativeRoot).support) :
    execution.application.serviceGrant = some event := by
  rw [nativeBeforeResponse, runInteractionPlan_append] at reached
  obtain ⟨prior, _, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have law : nativeRuntime.runInteractionPlan nativeLeaks players nativeNetwork
      [.grant event] prior = prior.environmentStep nativeApp (.application (.grant event)) := by
    simp only [runInteractionPlan, interactionStep, interactionInstruction,
      FinDist.pure_bind, FinDist.bind_pure, ReactiveApplication.dispatch]
    change (prior.environmentStep nativeApp (.application (.grant event))).bind
      (fun next => FinDist.pure next) = _
    exact FinDist.bind_pure _
  rw [law] at moved
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    environmentStep, FinDist.map_pure, FinDist.mem_support_pure] at moved
  subst execution
  rfl

/-- Public service grants distinguish all six later decision sites, even when
the same player owns several events. -/
theorem native_decision_cursor (event : nativeGraph.EventId) (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (who : Player)
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some event) :
    who = nativeOwner event ∧ control.execution.environmentRecall.length =
      (nativeBeforeResponse event).length + 1 := by
  obtain ⟨accounted, supported⟩ := nativeMenu.roundSupported_uniform
    (FinDist.pure nativeInitial) nativeHorizon nativeScheduler trace
  rw [active] at supported
  obtain ⟨count, prior, command, position, priorMem, commandMem, actor, observed⟩ := supported
  have cursor := nativeApp.roundsFrom_recall (FinDist.pure nativeInitial) nativeScheduler
    nativeMenu.uniformResponses count prior priorMem
  have bounded : count < nativePlan.length := by
    change _ + _ = nativePlan.length at accounted
    omega
  have selected : (nativePlan[count]?).bind responseOwner = some who := by
    simp only [nativeScheduler, cursor] at commandMem
    cases found : nativePlan[count]? with
    | none =>
        simp only [found, FinDist.mem_support_pure] at commandMem
        subst command
        cases actor
    | some instruction =>
        rw [found] at commandMem
        simp only [Option.bind_some]
        exact (instruction_actor instruction _ _ command commandMem).symm.trans actor
  have grantSame := native_activation_grant prior control.execution who (by
    cases command <;> simp only [ReactiveApplication.Command.actor?] at actor <;>
      try cases actor
    exact observed)
  rcases player_positions count who bounded selected with early | early | ⟨current, same, owner⟩
  · rw [grantSame, prelude_grant count (Or.inl early) prior priorMem] at granted
    cases granted
  · rw [grantSame, prelude_grant count (Or.inr early) prior priorMem] at granted
    cases granted
  · have evaluated := priorMem
    rw [same, native_roundsFrom_prefix nativeMenu.uniformResponses (nativeBeforeResponse current)
      (.player (nativeOwner current) :: nativeAfterResponse current)
      (native_response_split current)] at evaluated
    have grant := native_response_prefix_grant nativeMenu.uniformResponses current prior evaluated
    have identified : current = event :=
      Option.some.inj (grant.symm.trans (grantSame.symm.trans granted))
    subst current
    exact ⟨owner, by omega⟩

end VegasTests.SelectiveAssociation
