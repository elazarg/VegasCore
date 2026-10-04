/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingPublicTraffic
import Vegas.Pending.ReactiveHiddenEnvironment

/-! # Joint opaque-binding traffic under actual public scheduler rounds

The owner is silent during the phase and every foreign policy is arbitrary.
The scheduler and passive observation use the same public and pending data.
Clock, expiry, inclusion and activation preserve the complete joint public and
foreign readout while a binding is the sole ready event.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private theorem observeEnvironment_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingPublicTraffic leaks owner left =
      runtime.bindingPublicTraffic leaks owner right) :
    left.observeEnvironment (runtime.reactiveApplication leaks) =
      right.observeEnvironment (runtime.reactiveApplication leaks) := by
  have parts := same
  simp only [bindingPublicTraffic, Prod.mk.injEq] at parts
  obtain ⟨networks, receipts, _, publics, _⟩ := parts
  change ReactiveApplication.EnvironmentView.mk left.network.publicView
    left.application.publicView left.receipts =
      ReactiveApplication.EnvironmentView.mk right.network.publicView
        right.application.publicView right.receipts
  rw [networks, publics, receipts]

private theorem foreign_input_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner actor : Player) (foreign : actor ≠ owner)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingPublicTraffic leaks owner left =
      runtime.bindingPublicTraffic leaks owner right) :
    left.recall actor = right.recall actor ∧
      left.observe (runtime.reactiveApplication leaks) actor =
        right.observe (runtime.reactiveApplication leaks) actor := by
  have parts := same
  simp only [bindingPublicTraffic, Prod.mk.injEq] at parts
  obtain ⟨networks, receipts, _, _, locals⟩ := parts
  have localEq := congrFun locals actor
  simp only [foreign, ite_false, Option.some.injEq, Prod.mk.injEq] at localEq
  refine ⟨localEq.1, ?_⟩
  have view := congrArg (fun view : PlayerView graph =>
    (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
      ReactivePlayerView graph)) localEq.2
  change ReactiveApplication.PlayerView.mk _ _ _ = _
  rw [networks, receipts]
  exact congrArg (fun view => (⟨right.network.observe actor, view, right.receipts⟩ :
    (runtime.reactiveApplication leaks).PlayerView)) view

private theorem silent_respond_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingPublicTraffic leaks owner left =
      runtime.bindingPublicTraffic leaks owner right) :
    runtime.bindingPublicTraffic leaks owner
        (left.respond (runtime.reactiveApplication leaks) owner ⟨none⟩) =
      runtime.bindingPublicTraffic leaks owner
        (right.respond (runtime.reactiveApplication leaks) owner ⟨none⟩) := by
  have parts := same
  simp only [bindingPublicTraffic, Prod.mk.injEq] at parts
  obtain ⟨networks, receipts, environments, publics, locals⟩ := parts
  refine Prod.ext networks (Prod.ext receipts (Prod.ext environments (Prod.ext publics ?_)))
  funext who
  dsimp only [bindingPublicTraffic]
  by_cases foreign : who ≠ owner
  · simp only [foreign, ite_false, ReactiveApplication.Execution.respond]
    simpa only [foreign, ite_false] using congrFun locals who
  · simp only [not_ne_iff.mp foreign, ite_true]

omit [DecidableEq Player] in
private theorem sample_identity (runtime : EventGraphRuntime graph)
    (state : State graph) (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (sole : state.publicView.SoleReady event) (target : graph.EventId) :
    environmentStep runtime state (.executeSample target) = PMF.pure state := by
  by_cases ready : state.config.cut.Ready target
  · have current := sole.2 target ((state.publicView_eventReady target).mpr ready)
    subst target
    apply environmentStep_executeSample_of_nonsample runtime state event ready
    intro other law otherOutput otherCode sampled
    rw [node] at sampled
    cases sampled
  · exact environmentStep_executeSample_of_not_ready runtime state target ready

omit [DecidableEq Player] in
private theorem expire_public (runtime : EventGraphRuntime graph)
    (left right : State graph) (same : left.publicView = right.publicView)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (sole : left.publicView.SoleReady event) (target : graph.EventId) :
    (environmentStep runtime left (.expire target)).map State.publicView =
      (environmentStep runtime right (.expire target)).map State.publicView := by
  have clock := congrArg PublicView.clock same
  have activated := congrArg PublicView.activatedAt same
  dsimp only [State.publicView] at clock activated
  by_cases ready : left.config.cut.Ready target
  · have rightReady : right.config.cut.Ready target := by
      rw [← State.publicView_eventReady, ← same, State.publicView_eventReady]
      exact ready
    have current := sole.2 target ((left.publicView_eventReady target).mpr ready)
    subst target
    cases started : left.activatedAt event with
    | none =>
        have rightStarted : right.activatedAt event = none := by rw [← activated]; exact started
        rw [environmentStep_expire_of_not_activated runtime left event ready started,
          environmentStep_expire_of_not_activated runtime right event rightReady rightStarted]
        simpa only [PMF.pure_map] using congrArg (fun view => PMF.pure view) same
    | some entered =>
        have rightStarted : right.activatedAt event = some entered := by
          rw [← activated]
          exact started
        by_cases due : runtime.deadline event ≤ left.clock - entered
        · have rightDue : runtime.deadline event ≤ right.clock - entered := clock ▸ due
          rw [environmentStep_expire_bind_eq runtime left event ready entered started due
              owner payload outputEq codeEq node,
            environmentStep_expire_bind_eq runtime right event rightReady entered rightStarted
              rightDue owner payload outputEq codeEq node, PMF.pure_map, PMF.pure_map]
          apply congrArg PMF.pure
          have completed := State.complete_publicView_congr left right same event ready rightReady
            (cast (congrArg EventField.Action outputEq.symm)
              (PublicationResult.failure : PublicationResult (L.Val payload)))
            (cast (congrArg EventField.Value outputEq.symm)
              (PublicationResult.failure : PublicationResult (L.Val payload)))
          exact congrArg (fun view : PublicView graph =>
            { view with missedEvents := insert event view.missedEvents }) completed
        · have rightNotDue : ¬runtime.deadline event ≤ right.clock - entered := by
            rw [← clock]
            exact due
          rw [environmentStep_expire_of_not_due runtime left event ready entered started due,
            environmentStep_expire_of_not_due runtime right event rightReady entered
              rightStarted rightNotDue]
          simpa only [PMF.pure_map] using congrArg (fun view => PMF.pure view) same
  · have rightNotReady : ¬right.config.cut.Ready target := by
      rw [← State.publicView_eventReady, ← same, State.publicView_eventReady]
      exact ready
    rw [environmentStep_expire_of_not_ready runtime left target ready,
      environmentStep_expire_of_not_ready runtime right target rightNotReady]
    simpa only [PMF.pure_map] using congrArg (fun view => PMF.pure view) same

private theorem maintenance_pure (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (command : EnvironmentCommand graph)
    (maintenance : ∀ target, command ≠ .executeSample target) :
    ∃ next, execution.environmentStep (runtime.reactiveApplication leaks)
      (.application command) = PMF.pure next := by
  cases command with
  | executeSample target => exact (maintenance target rfl).elim
  | advanceClock | expire target =>
      simp only [ReactiveApplication.Execution.environmentStep, reactiveApplication,
        environmentStep, PMF.pure_map]
      exact ⟨_, rfl⟩

private theorem maintenance_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingPublicTraffic leaks owner left =
      runtime.bindingPublicTraffic leaks owner right)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (sole : left.application.publicView.SoleReady event)
    (command : EnvironmentCommand graph)
    (maintenance : ∀ target, command ≠ .executeSample target) :
    (left.environmentStep (runtime.reactiveApplication leaks) (.application command)).map
        (runtime.bindingPublicTraffic leaks owner) =
      (right.environmentStep (runtime.reactiveApplication leaks) (.application command)).map
        (runtime.bindingPublicTraffic leaks owner) := by
  have parts := same
  simp only [bindingPublicTraffic, Prod.mk.injEq] at parts
  obtain ⟨networks, receipts, environments, publics, locals⟩ := parts
  have views (who : Player) (foreign : who ≠ owner) :
      left.application.playerView who = right.application.playerView who := by
    have localEq := congrFun locals who
    simp only [foreign, ite_false, Option.some.injEq, Prod.mk.injEq] at localEq
    exact localEq.2
  have recalled (who : Player) (foreign : who ≠ owner) :
      left.recall who = right.recall who := by
    have localEq := congrFun locals who
    simp only [foreign, ite_false, Option.some.injEq, Prod.mk.injEq] at localEq
    exact localEq.1
  have joined := runtime.reactive_maintenance_hidden_congr leaks left right owner networks receipts
    publics environments views recalled command maintenance
  dsimp only at joined
  have observed :
      (left.environmentStep (runtime.reactiveApplication leaks) (.application command)).map
          (fun next => next.application.publicView) =
        (right.environmentStep (runtime.reactiveApplication leaks) (.application command)).map
          (fun next => next.application.publicView) := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
    change (environmentStep runtime left.application command).map State.publicView =
      (environmentStep runtime right.application command).map State.publicView
    cases command with
    | executeSample target => exact (maintenance target rfl).elim
    | advanceClock =>
        simpa only [environmentStep, PMF.pure_map, State.publicView] using congrArg
          (fun view : PublicView graph => PMF.pure { view with clock := view.clock + 1 }) publics
    | expire target =>
        exact expire_public runtime left.application right.application publics
          event owner payload outputEq codeEq node sole target
  obtain ⟨first, firstLaw⟩ := maintenance_pure runtime leaks left command maintenance
  obtain ⟨second, secondLaw⟩ := maintenance_pure runtime leaks right command maintenance
  rw [firstLaw, secondLaw, PMF.pure_map, PMF.pure_map] at joined observed ⊢
  have core := Set.singleton_injective (by
    simpa only [PMF.support_pure] using congrArg PMF.support joined)
  have publicEq := Set.singleton_injective (by
    simpa only [PMF.support_pure] using congrArg PMF.support observed)
  simp only [Prod.mk.injEq] at core
  obtain ⟨nextNetworks, nextReceipts, nextEnvironment, nextLocals⟩ := core
  apply congrArg PMF.pure
  exact Prod.ext nextNetworks (Prod.ext nextReceipts (Prod.ext nextEnvironment
    (Prod.ext publicEq nextLocals)))

private theorem sampledActivation_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner actor : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingPublicTraffic leaks owner left =
      runtime.bindingPublicTraffic leaks owner right)
    (selected : Finset (MessageId Player)) :
    runtime.bindingPublicTraffic leaks owner
        (left.sampledActivation (runtime.reactiveApplication leaks) actor selected) =
      runtime.bindingPublicTraffic leaks owner
        (right.sampledActivation (runtime.reactiveApplication leaks) actor selected) := by
  have parts := same
  simp only [bindingPublicTraffic, Prod.mk.injEq] at parts
  obtain ⟨networks, receipts, environments, publics, locals⟩ := parts
  have environment := observeEnvironment_eq runtime leaks owner left right same
  dsimp only [bindingPublicTraffic, ReactiveApplication.Execution.sampledActivation]
  rw [networks, receipts, environments, publics, environment]
  exact congrArg (fun extras =>
    ((right.network.learn actor selected), right.receipts,
      right.environmentRecall ++ [⟨right.observeEnvironment
        (runtime.reactiveApplication leaks), .activate actor⟩],
      right.application.publicView, extras)) locals

private theorem invoke_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (owner actor : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingPublicTraffic leaks owner left =
      runtime.bindingPublicTraffic leaks owner right) :
    ((runtime.reactiveApplication leaks).invoke
        (Function.update players owner (runtime.reactiveApplication leaks).silentPolicy)
        actor left).map (runtime.bindingPublicTraffic leaks owner) =
      ((runtime.reactiveApplication leaks).invoke
        (Function.update players owner (runtime.reactiveApplication leaks).silentPolicy)
        actor right).map (runtime.bindingPublicTraffic leaks owner) := by
  by_cases foreign : actor ≠ owner
  · obtain ⟨pastEq, inputEq⟩ := foreign_input_eq runtime leaks owner actor foreign left right same
    simp only [ReactiveApplication.invoke, Function.update_of_ne foreign,
      PMF.map_comp, pastEq, inputEq]
    apply map_congr_on_support _
    intro response _
    exact runtime.bindingPublicTraffic_respond_foreign leaks owner actor foreign left right
      same response
  · have own : actor = owner := not_ne_iff.mp foreign
    subst actor
    simpa only [ReactiveApplication.invoke, Function.update_self,
      ReactiveApplication.silentPolicy_apply, PMF.pure_map, PMF.map_comp,
      Function.comp_apply] using congrArg PMF.pure (silent_respond_eq runtime leaks owner
        left right same)

/-- An arbitrary public scheduler and arbitrary foreign response policies
have the same complete joint traffic law during a sole-ready opaque binding.
Only the current binding owner's policy is replaced by physical silence. -/
theorem bindingPublicTraffic_round (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (owner : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingPublicTraffic leaks owner left =
      runtime.bindingPublicTraffic leaks owner right)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (sole : left.application.publicView.SoleReady event) :
    ((runtime.reactiveApplication leaks).round scheduler
        (Function.update players owner (runtime.reactiveApplication leaks).silentPolicy)
        left).map (runtime.bindingPublicTraffic leaks owner) =
      ((runtime.reactiveApplication leaks).round scheduler
        (Function.update players owner (runtime.reactiveApplication leaks).silentPolicy)
        right).map (runtime.bindingPublicTraffic leaks owner) := by
  let app := runtime.reactiveApplication leaks
  have parts := same
  simp only [bindingPublicTraffic, Prod.mk.injEq] at parts
  obtain ⟨networks, receipts, environments, publics, _locals⟩ := parts
  have environment := observeEnvironment_eq runtime leaks owner left right same
  have rightSole : right.application.publicView.SoleReady event := publics ▸ sole
  have waiting : app.resume (Function.update players owner app.silentPolicy) none = PMF.pure := rfl
  dsimp only [app] at waiting
  simp only [ReactiveApplication.round, PMF.map_bind, environments]
  rw [environment]
  apply bind_congr_on_support _
  intro command _
  cases command with
  | activate actor =>
      simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.Execution.activation_samples,
        PMF.map_bind, PMF.bind_map]
      rw [networks]
      apply bind_congr_on_support _
      intro selected _
      exact invoke_eq runtime leaks players owner actor _ _
        (sampledActivation_eq runtime leaks owner actor left right same selected)
  | «include» id =>
      have included := runtime.bindingPublicTraffic_include leaks owner left right same
        event payload outputEq codeEq node sole id
      simpa only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.Execution.environmentStep,
        PMF.pure_map, PMF.pure_bind, PMF.map_comp, bindingPublicTraffic,
        Function.comp_apply, app, environments, environment] using congrArg
        (fun read => PMF.pure (read.1, read.2.1,
          right.environmentRecall ++ [⟨right.observeEnvironment
            (runtime.reactiveApplication leaks), .include id⟩], read.2.2.2)) included
  | wait =>
      simpa only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.Execution.environmentStep,
        PMF.pure_map, PMF.pure_bind, bindingPublicTraffic, Function.comp_apply,
        app, environments, environment] using congrArg
        (fun read => PMF.pure (read.1, read.2.1,
          right.environmentRecall ++ [⟨right.observeEnvironment
            (runtime.reactiveApplication leaks), .wait⟩], read.2.2.2)) same
  | application command =>
      cases command with
      | advanceClock =>
          simpa only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
            waiting, PMF.bind_pure] using maintenance_eq runtime leaks
            owner left right same event payload outputEq codeEq node sole .advanceClock (by
              intro target impossible
              cases impossible)
      | expire target =>
          simpa only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
            waiting, PMF.bind_pure] using maintenance_eq runtime leaks
            owner left right same event payload outputEq codeEq node sole (.expire target) (by
              intro target impossible
              cases impossible)
      | executeSample target =>
          have first := sample_identity runtime left.application event owner payload
            outputEq codeEq node sole target
          have second := sample_identity runtime right.application event owner payload
            outputEq codeEq node rightSole target
          change app.environment left.application (.executeSample target) = _ at first
          change app.environment right.application (.executeSample target) = _ at second
          simpa only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
            waiting, ReactiveApplication.Execution.environmentStep,
            PMF.bind_pure, first, second, PMF.pure_map, PMF.map_comp,
            bindingPublicTraffic, Function.comp_apply, app, environments, environment] using
            congrArg (fun read => PMF.pure (read.1, read.2.1,
              right.environmentRecall ++ [⟨right.observeEnvironment
                (runtime.reactiveApplication leaks), .application (.executeSample target)⟩],
              read.2.2.2)) same

end Vegas.EventGraphRuntime
