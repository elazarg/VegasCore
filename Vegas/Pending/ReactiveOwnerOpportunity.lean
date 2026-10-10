/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveAsyncContract
import Interaction.ReactiveHistory
import Vegas.Pending.ReactiveCanonicalDecision

/-! # A ready owner must receive an opportunity before actual expiry -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Under the existing timely opportunity contract, an actual expiry command
stutters until the event's owner has been activated in its readiness episode.
This proves an operational precondition; it does not assert compiler correctness. -/
theorem expiry_stutters_before_owner_opportunity (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (delay bound : graph.EventId → Nat)
    (opportunity : runtime.Opportunity leaks initial horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control))
    (event : graph.EventId) (owner : Player) (actor : graph.actor? event = some owner)
    (ready : control.execution.application.config.cut.Ready event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered)
    (absent : ¬ runtime.OwnerActivatedSince leaks control.execution.environmentRecall
      event owner entered) :
    environmentStep runtime control.execution.application (.expire event) =
      PMF.pure control.execution.application := by
  apply environmentStep_expire_of_not_due runtime _ event ready entered activated
  intro due
  apply absent
  apply opportunity control trace event owner entered actor
    ((control.execution.application.publicView_eventReady event).mpr ready) activated
  have margin := timely event (by simp only [actor, Option.isSome_some])
  omega

/-- At an idle actual raw prefix, every recorded owner activation has a
corresponding actual response prefix and retained pre-response public view. -/
theorem activated_owner_response_prefix (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (idle : control.actor = none)
    (activation : (runtime.reactiveApplication leaks).EnvironmentEntry)
    (recorded : activation ∈ control.execution.environmentRecall)
    (owner : Player) (activated : activation.command = .activate owner) :
    ∃ before : (runtime.reactiveApplication leaks).Control,
      Nonempty (((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
        (some before)) ∧ before.actor = some owner ∧
      ∃ response ∈ control.execution.recall owner,
        response.beforeView = before.execution.observe (runtime.reactiveApplication leaks) owner ∧
        response.beforeView.application.publicView = activation.beforeView.application := by
  let app := runtime.reactiveApplication leaks
  let paired (current : app.Control) (entry : app.EnvironmentEntry) (who : Player) : Prop :=
    ∃ before : app.Control,
      Nonempty ((app.protocol initial horizon scheduler).Trace (some before)) ∧
        before.actor = some who ∧ ∃ response ∈ current.execution.recall who,
          response.beforeView = before.execution.observe app who ∧
          response.beforeView.application.publicView = entry.beforeView.application
  have provenance : ∀ {state} (_history : (app.protocol initial horizon scheduler).Trace state),
      state.elim True (fun current => ∀ entry ∈ current.execution.environmentRecall,
        ∀ who, entry.command = .activate who → paired current entry who ∨
          (current.actor = some who ∧ current.execution.application.publicView =
            entry.beforeView.application)) := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint legal reached ih =>
        change target ∈ (app.transition initial horizon scheduler source joint).support at reached
        cases source with
        | none =>
            obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
            intro entry member
            exact (List.not_mem_nil member).elim
        | some current =>
            rcases current with ⟨remaining, actor, execution⟩
            cases actor with
            | some acting =>
                cases (PMF.mem_support_pure_iff _ _).mp reached
                intro entry member who chosen
                have priorMember : entry ∈ execution.environmentRecall := by
                  simpa only [app.respond_environmentRecall] using member
                rcases ih entry priorMember who chosen with pairedBefore | waiting
                · left
                  obtain ⟨before, prefixTrace, actor, response, responded, viewed,
                    publicEqual⟩ :=
                    pairedBefore
                  exact ⟨before, prefixTrace, actor, response,
                    app.respond_recall_mono execution acting who _ responded, viewed, publicEqual⟩
                · have same : acting = who := Option.some.inj waiting.1
                  subst acting
                  left
                  have fresh : ∃ response ∈
                      (execution.respond app who ((joint who).getD ⟨none⟩)).recall who,
                      response.beforeView = execution.observe app who := by
                    cases action : (joint who).getD ⟨none⟩ with
                    | mk transmission =>
                        cases transmission <;>
                          simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
                        all_goals exact ⟨_, List.mem_append_right _
                          (List.mem_singleton.mpr rfl), rfl⟩
                  obtain ⟨response, member, viewed⟩ := fresh
                  refine ⟨⟨remaining, some who, execution⟩, ⟨prior⟩, rfl,
                    response, member, viewed, ?_⟩
                  rw [viewed]
                  exact waiting.2
            | none =>
                cases remaining with
                | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
                | succ remaining =>
                    obtain ⟨command, _, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                    have recall := app.environmentStep_recall execution next command supported
                    have entries : next.environmentRecall = execution.environmentRecall ++
                        [⟨execution.observeEnvironment app, command⟩] := by
                      unfold ReactiveApplication.Execution.environmentStep at supported
                      obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ supported
                      rfl
                    intro entry member who chosen
                    rw [entries, List.mem_append, List.mem_singleton] at member
                    rcases member with earlier | rfl
                    · rcases ih entry earlier who chosen with pairedBefore | waiting
                      · left
                        obtain ⟨before, prefixTrace, actor, response, responded, viewed,
                    publicEqual⟩ :=
                    pairedBefore
                        exact ⟨before, prefixTrace, actor, response, recall ▸ responded,
                          viewed, publicEqual⟩
                      · cases waiting.1
                    · right
                      have commandEq : command = .activate who := chosen
                      subst command
                      refine ⟨rfl, ?_⟩
                      unfold ReactiveApplication.Execution.environmentStep at supported
                      obtain ⟨updated, updatedMember, rfl⟩ := PMF.support_map .. ▸ supported
                      obtain ⟨observed, _, rfl⟩ := PMF.support_map .. ▸ updatedMember
                      rfl
  rcases provenance trace activation recorded owner activated with done | waiting
  · exact done
  · rw [idle] at waiting
    cases waiting.1

/-- Before a due owned expiry, the existing timely opportunity condition
supplies an actual prior owner response at precisely the event's source turn. -/
theorem due_owner_response_prefix (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (delay bound : graph.EventId → Nat)
    (opportunity : runtime.Opportunity leaks initial horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound) (ordered : graph.BarrierOrdered)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (idle : control.actor = none)
    (event : graph.EventId) (owner : Player) (actor : graph.actor? event = some owner)
    (ready : control.execution.application.config.cut.Ready event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ control.execution.application.clock - entered) :
    ∃ before : (runtime.reactiveApplication leaks).Control,
      Nonempty (((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
        (some before)) ∧ before.actor = some owner ∧
      ∃ response ∈ control.execution.recall owner,
        response.beforeView = before.execution.observe (runtime.reactiveApplication leaks) owner ∧
        before.execution.application.publicView.ownTurn? owner = some event ∧
        before.execution.application.activatedAt event = some entered := by
  have margin := timely event (by simp only [actor, Option.isSome_some])
  obtain ⟨activation, recorded, command, activatedBefore, readyBefore⟩ :=
    opportunity control trace event owner entered actor
      ((control.execution.application.publicView_eventReady event).mpr ready) activated
      (by omega)
  obtain ⟨before, prefixTrace, own, response, remembered, viewed, publicEqual⟩ :=
    runtime.activated_owner_response_prefix leaks initial horizon scheduler control trace idle
      activation recorded owner command
  have publicState : before.execution.application.publicView =
      activation.beforeView.application := by
    simpa only [viewed, ReactiveApplication.Execution.observe, reactiveApplication,
      State.playerView] using publicEqual
  refine ⟨before, prefixTrace, own, response, remembered, viewed, ?_, ?_⟩
  · apply PublicView.ownTurn?_of_ownTurn
    apply State.ownTurn_of_ready _ ordered owner event
    · rw [publicState]
      exact readyBefore
    · exact actor
  · have same := congrArg (fun view => view.activatedAt event) publicState
    exact same.trans activatedBefore


/-- Every recorded readiness-episode activation has a recorded activation
within the existing opportunity delay. -/
theorem recorded_activation_within_delay (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (delay : graph.EventId → Nat)
    (opportunity : runtime.Opportunity leaks initial horizon scheduler delay)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (event : graph.EventId) (owner : Player) (entered : Nat)
    (actor : graph.actor? event = some owner)
    (existsActivation : runtime.OwnerActivatedSince leaks control.execution.environmentRecall
      event owner entered) :
    ∃ entry ∈ control.execution.environmentRecall, entry.command = .activate owner ∧
      entry.beforeView.application.activatedAt event = some entered ∧
      entry.beforeView.application.EventReady event ∧
      entry.beforeView.application.clock ≤ entered + delay event := by
  let app := runtime.reactiveApplication leaks
  have provenance : ∀ {state} (_history : (app.protocol initial horizon scheduler).Trace state),
      state.elim True (fun current => ∀ event owner entered,
        graph.actor? event = some owner →
        runtime.OwnerActivatedSince leaks current.execution.environmentRecall event owner entered →
        ∃ entry ∈ current.execution.environmentRecall, entry.command = .activate owner ∧
          entry.beforeView.application.activatedAt event = some entered ∧
          entry.beforeView.application.EventReady event ∧
          entry.beforeView.application.clock ≤ entered + delay event) := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint legal reached ih =>
        change target ∈ (app.transition initial horizon scheduler source joint).support at reached
        cases source with
        | none =>
            obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
            intro event owner entered actor existsActivation
            obtain ⟨entry, member, _⟩ := existsActivation
            exact (List.not_mem_nil member).elim
        | some current =>
            rcases current with ⟨remaining, acting, execution⟩
            cases acting with
            | some who =>
                cases (PMF.mem_support_pure_iff _ _).mp reached
                simpa only [Option.elim_some, app.respond_environmentRecall] using ih
            | none =>
                cases remaining with
                | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
                | succ remaining =>
                    obtain ⟨command, _, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                    have entries : next.environmentRecall = execution.environmentRecall ++
                        [⟨execution.observeEnvironment app, command⟩] := by
                      unfold ReactiveApplication.Execution.environmentStep at supported
                      obtain ⟨updated, _, rfl⟩ := PMF.support_map .. ▸ supported
                      rfl
                    intro event owner entered actor existsActivation
                    obtain ⟨entry, member, chosen, activated, ready⟩ := existsActivation
                    rw [entries, List.mem_append, List.mem_singleton] at member
                    have liftEarlier : runtime.OwnerActivatedSince leaks
                        execution.environmentRecall event owner entered →
                        ∃ entry ∈ next.environmentRecall, entry.command = .activate owner ∧
                          entry.beforeView.application.activatedAt event = some entered ∧
                          entry.beforeView.application.EventReady event ∧
                          entry.beforeView.application.clock ≤ entered + delay event := by
                      intro earlier
                      obtain ⟨earlier, member, facts⟩ := ih event owner entered actor earlier
                      exact ⟨earlier, entries ▸ List.mem_append_left _ member, facts⟩
                    rcases member with earlier | rfl
                    · exact liftEarlier ⟨entry, earlier, chosen, activated, ready⟩
                    · by_cases timely : execution.application.clock ≤ entered + delay event
                      · exact ⟨_, entries ▸ List.mem_append_right _
                          (List.mem_singleton.mpr rfl), chosen, activated, ready, timely⟩
                      · apply liftEarlier
                        exact opportunity ⟨remaining + 1, none, execution⟩ prior event owner entered
                          actor ready activated (by
                            change entered + delay event < execution.application.clock
                            omega)
  exact provenance trace event owner entered actor existsActivation


/-- A recorded owner opportunity yields an actual owner response at the
specified source turn no later than the readiness episode's delay. -/
theorem owner_response_within_delay (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (delay : graph.EventId → Nat)
    (opportunity : runtime.Opportunity leaks initial horizon scheduler delay)
    (ordered : graph.BarrierOrdered)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) (idle : control.actor = none)
    (event : graph.EventId) (owner : Player) (entered : Nat)
    (actor : graph.actor? event = some owner)
    (existsActivation : runtime.OwnerActivatedSince leaks control.execution.environmentRecall
      event owner entered) :
    ∃ before : (runtime.reactiveApplication leaks).Control,
      Nonempty (((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
        (some before)) ∧ before.actor = some owner ∧
      ∃ response ∈ control.execution.recall owner,
        response.beforeView = before.execution.observe (runtime.reactiveApplication leaks) owner ∧
        before.execution.application.publicView.ownTurn? owner = some event ∧
        before.execution.application.activatedAt event = some entered ∧
        before.execution.application.clock ≤ entered + delay event := by
  obtain ⟨activation, recorded, command, activatedBefore, readyBefore, timely⟩ :=
    runtime.recorded_activation_within_delay leaks initial horizon scheduler delay opportunity
      control trace event owner entered actor existsActivation
  obtain ⟨before, prefixTrace, own, response, remembered, viewed, publicEqual⟩ :=
    runtime.activated_owner_response_prefix leaks initial horizon scheduler control trace idle
      activation recorded owner command
  have publicState : before.execution.application.publicView =
      activation.beforeView.application := by
    simpa only [viewed, ReactiveApplication.Execution.observe, reactiveApplication,
      State.playerView] using publicEqual
  refine ⟨before, prefixTrace, own, response, remembered, viewed, ?_, ?_, ?_⟩
  · apply PublicView.ownTurn?_of_ownTurn
    apply State.ownTurn_of_ready _ ordered owner event
    · rw [publicState]
      exact readyBefore
    · exact actor
  · exact (congrArg (fun view => view.activatedAt event) publicState).trans activatedBefore
  · have same := congrArg (fun view => view.clock) publicState
    change before.execution.application.publicView.clock ≤ entered + delay event
    rw [same]
    exact timely


omit [DecidableEq Player] in
/-- The existing asynchronous margin turns a timely actual response into
exactly the inclusion-window hypothesis used by packet settlement. -/
theorem PublicView.inclusionFitsDeadline_of_response_delay
    (runtime : EventGraphRuntime graph) (delay bound : graph.EventId → Nat)
    (timely : runtime.AsyncTimely delay bound) (view : PublicView graph)
    (event : graph.EventId) (entered : Nat)
    (owned : (graph.actor? event).isSome)
    (activated : view.activatedAt event = some entered)
    (responded : view.clock ≤ entered + delay event) :
    view.InclusionFitsDeadline runtime bound event := by
  unfold PublicView.InclusionFitsDeadline
  rw [activated]
  have margin := timely event owned
  omega

end Vegas.EventGraphRuntime
