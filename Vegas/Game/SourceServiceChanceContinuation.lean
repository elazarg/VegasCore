/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceAsyncStep
import Vegas.Pending.ExclusionPolicyLaw

/-! # Native continuation while waiting for public chance

A ready chance event is the unique ready event of the sequential graph. Native commands
and arbitrary responses preserve its canonical remaining-run law: sampling executes the
same chance kernel followed by automatic completion, and other commands preserve the
configuration. Bounded waiting therefore preserves the full continuation even when its
budget ends before sampling, without a completion or initialization premise.
-/
noncomputable section

namespace Vegas

open SourceProgram EventGraph Interaction GameTheory.Math.Probability
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

private theorem ownerless_step_bind_runPlan
    (profile : (graph setup).BehavioralProfile) (config : (graph setup).Config)
    (event : (graph setup).EventId) (ready : config.cut.Ready event)
    (ownerless : (graph setup).actor? event = none) (action : (graph setup).Action event) :
    (config.step event ready action).bind (fun next => (graph setup).runPlan
      ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
      next.remaining next) =
      (graph setup).runPlan
        ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
        config.remaining config := by
  have nonzero : config.remaining ≠ 0 := by
    intro zero
    have terminal := config.terminal_iff_remaining_zero.mpr zero
    apply ready.1
    rw [EventOrder.Cut.Terminal] at terminal
    rw [terminal]
    exact Finset.mem_univ _
  obtain ⟨fuel, fuelEq⟩ := Nat.exists_eq_succ_of_ne_zero nonzero
  symm
  rw [fuelEq, (graph setup).runPlan_canonical_ownerless profile fuel config event ready
    (fun _ pending => setup.eventGraph.sequentialize_ready_le_unfinished config.cut ready pending)
    ownerless]
  rw [((graph setup).nodes event).action_eq_of_actor_none ownerless
    (EventCode.actionOfActorNone ((graph setup).nodes event) ownerless) action]
  apply bind_congr_on_support _
  intro next member
  have progress := config.remaining_step event ready action next member
  have remaining : next.remaining = fuel := by omega
  rw [remaining]

private theorem resume_config
    (players : Player → (application setup runtime leaks).Policy)
    (actor : Option Player) (execution next : (application setup runtime leaks).Execution)
    (reached : next ∈ ((application setup runtime leaks).resume players actor execution).support) :
    next.application.config = execution.application.config := by
  cases actor with
  | none =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | some who =>
      change next ∈ ((application setup runtime leaks).invoke players who execution).support
        at reached
      rw [ReactiveApplication.invoke, PMF.support_map] at reached
      obtain ⟨response, _, rfl⟩ := reached
      exact (runtime.reactive_respond_application leaks execution who response).1

private theorem chance_environment_bind_runPlan
    (profile : (graph setup).BehavioralProfile)
    (state : EventGraphRuntime.State (graph setup))
    (command : EnvironmentCommand (graph setup)) (event : (graph setup).EventId)
    (ready : state.config.cut.Ready event) (ownerless : (graph setup).actor? event = none) :
    (((runtime.reactiveApplication leaks).environment state command).bind fun next =>
      (graph setup).runPlan
        ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
        next.config.remaining next.config) =
      (graph setup).runPlan
        ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
        state.config.remaining state.config := by
  refine (EventGraphRuntime.State.drain_bind_runPlan_canonical setup.eventGraph profile
    (environmentStep runtime state command)).trans ?_
  have sole (other : (graph setup).EventId) (otherReady : state.config.cut.Ready other) :
      other = event := setup.eventGraph.sequentialize_ready_unique state.config.cut otherReady ready
  cases node : nodeView (graph setup) event with
  | bind owner payload outputEq codeEq =>
      have actor := nodeView_bind_actor outputEq codeEq
      rw [ownerless] at actor
      cases actor
  | resolve owner payload binding checks outputEq codeEq =>
      have actor := nodeView_resolve_actor outputEq codeEq
      rw [ownerless] at actor
      cases actor
  | sample payload law outputEq codeEq =>
      cases command with
      | advanceClock => simp only [environmentStep, PMF.pure_bind]
      | executeSample other =>
          by_cases otherReady : state.config.cut.Ready other
          · have same := sole other otherReady
            subst other
            rw [environmentStep_executeSample_eq runtime state event ready payload law outputEq
              codeEq node, PMF.bind_map]
            exact ownerless_step_bind_runPlan profile state.config event ready ownerless _
          · rw [environmentStep_executeSample_of_not_ready runtime state other otherReady,
              PMF.pure_bind]
      | expire other =>
          have pure : environmentStep runtime state (.expire other) = PMF.pure state := by
            by_cases otherReady : state.config.cut.Ready other
            · have same := sole other otherReady
              subst other
              cases activated : state.activatedAt event with
              | none =>
                  exact environmentStep_expire_of_not_activated runtime state event ready activated
              | some entered =>
                  by_cases due : runtime.deadline event ≤ state.clock - entered
                  · exact environmentStep_expire_sample_eq runtime state event ready entered
                      activated due payload law outputEq codeEq node
                  · exact environmentStep_expire_of_not_due runtime state event ready entered
                      activated due
            · exact environmentStep_expire_of_not_ready runtime state other otherReady
          rw [pure, PMF.pure_bind]

/-- Every native command preserves the remaining canonical law while the ready
event is a public chance event. Sampling includes its atomic automatic tail. -/
private theorem chance_dispatch_bind_runPlan
    (profile : (graph setup).BehavioralProfile)
    (players : Player → (application setup runtime leaks).Policy)
    (execution : (application setup runtime leaks).Execution)
    (command : (application setup runtime leaks).Command) (event : (graph setup).EventId)
    (ready : execution.application.config.cut.Ready event)
    (ownerless : (graph setup).actor? event = none) :
    (((application setup runtime leaks).dispatch players command execution).bind fun next =>
      (graph setup).runPlan
        ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
        next.application.config.remaining next.application.config) =
      (graph setup).runPlan
        ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
        execution.application.config.remaining execution.application.config := by
  let app := application setup runtime leaks
  let continuation := fun next : app.Execution => (graph setup).runPlan
    ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
    next.application.config.remaining next.application.config
  change (app.dispatch players command execution).bind continuation = continuation execution
  unfold ReactiveApplication.dispatch
  rw [PMF.bind_bind]
  have resumed (middle : app.Execution) :
      (app.resume players (command.actor? app) middle).bind continuation = continuation middle := by
    calc
      _ = (app.resume players (command.actor? app) middle).bind
          (fun _ => continuation middle) := by
        apply bind_congr_on_support _
        intro next reached
        dsimp only [continuation]
        rw [resume_config runtime leaks players _ middle next reached]
      _ = _ := PMF.bind_const _ _
  simp_rw [resumed]
  have stays : (∀ next ∈ (execution.environmentStep app command).support,
      next.application.config = execution.application.config) →
      (execution.environmentStep app command).bind continuation = continuation execution := by
    intro fixed
    calc
      _ = (execution.environmentStep app command).bind (fun _ => continuation execution) := by
        apply bind_congr_on_support _
        intro next reached
        dsimp only [continuation]
        rw [fixed next reached]
      _ = _ := PMF.bind_const _ _
  cases command with
  | activate who =>
      apply stays
      intro next reached
      rw [activation_application (setup := setup) leaks execution next who reached]
  | wait =>
      apply stays
      intro next reached
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | «include» id =>
      apply stays
      intro next reached
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => rfl
      | some message =>
          change ((app.handle execution.application message).getD execution.application).config = _
          cases accepted : app.handle execution.application message with
          | none => rfl
          | some next =>
              obtain ⟨native, handled, _⟩ := reactiveHandle_call accepted
              obtain ⟨named, namedEq, namedReady, _, _⟩ := handle_config_mem_step runtime
                execution.application native ⟨message.id, message.payload.call⟩ handled
              have same := setup.eventGraph.sequentialize_ready_unique
                execution.application.config.cut namedReady ready
              subst named
              have actor := handle_sender_actor runtime execution.application native
                ⟨message.id, message.payload.call⟩ handled event namedEq
              rw [ownerless] at actor
              cases actor
  | application command =>
      change (execution.environmentStep app (.application command)).bind continuation = _
      simp only [ReactiveApplication.Execution.environmentStep, PMF.bind_map]
      exact chance_environment_bind_runPlan runtime leaks profile execution.application command
        event ready ownerless

/-- Bounded waiting for a ready chance event preserves its complete canonical
continuation, including runs whose budget ends before sampling. -/
theorem chance_runUntil_bind_runPlan
    (profile : (graph setup).BehavioralProfile)
    (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy)
    (event : (graph setup).EventId) (ownerless : (graph setup).actor? event = none) :
    ∀ (count : Nat) (execution : (application setup runtime leaks).Execution),
      execution.application.config.cut.Ready event →
      (((application setup runtime leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).bind
        fun final => (graph setup).runPlan
          ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          final.application.config.remaining final.application.config) =
        (graph setup).runPlan
          ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          execution.application.config.remaining execution.application.config := by
  classical
  let app := application setup runtime leaks
  let continuation := fun next : app.Execution => (graph setup).runPlan
    ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
    next.application.config.remaining next.application.config
  intro count
  induction count with
  | zero => intro execution _; simp only [ReactiveApplication.runUntil, PMF.pure_bind]
  | succ count ih =>
      intro execution ready
      rw [ReactiveApplication.runUntil, ite_eq_right ready.1, PMF.bind_bind]
      calc
        _ = (app.round scheduler players execution).bind continuation := by
          apply bind_congr_on_support _
          intro next reached
          by_cases completed : event ∈ next.application.config.cut.completed
          · rw [app.runUntil_of_stop scheduler players _ count next completed, PMF.pure_bind]
          · have path : Relation.ReflTransGen EventGraph.Config.Step
                execution.application.config next.application.config := by
              obtain ⟨command, _, dispatched⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨middle, moved, resumed⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
              have same := resume_config runtime leaks players _ middle next resumed
              rw [same]
              exact (runtime.reactiveApplication_graphSteps leaks).environmentStep
                execution middle command moved
            have same := EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
              (fun _ otherReady => setup.eventGraph.sequentialize_ready_unique _ otherReady ready)
              completed path
            exact ih next (same.symm ▸ ready)
        _ = continuation execution := by
          unfold ReactiveApplication.round
          rw [PMF.bind_bind]
          calc
            _ = (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind
                (fun _ => continuation execution) :=
              bind_congr_on_support _ (fun command _ =>
                chance_dispatch_bind_runPlan runtime leaks profile players execution command
                  event ready ownerless)
            _ = _ := PMF.bind_const _ _

end Vegas
