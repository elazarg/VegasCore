/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecidedCompletion

/-! # A public chance event ready alone

At a chance event ready alone no response changes the configuration, which
stays put until the scheduler samples, and the sample has the source law: a
run that stops only once the event has completed has the event's sampling law
on configurations (`Vegas.chance_runUntil`). This holds in every dependency
mode; on a barrier-ordered graph every chance event is ready alone.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- A response keeps the configuration, so resuming keeps its law. -/
private theorem resume_config_law (players : Player →
    (serviceApplication setup mode deadline leaks).Policy)
    (actor : Option Player) (execution : (serviceApplication setup mode deadline leaks).Execution) :
    ((serviceApplication setup mode deadline leaks).resume players actor execution).map
        (fun next => next.application.config) = PMF.pure execution.application.config := by
  rw [map_congr_on_support _ (g := fun _ => execution.application.config) (fun next reached => by
    cases actor with
    | none =>
        cases (PMF.mem_support_pure_iff _ _).mp reached
        rfl
    | some who =>
        change next ∈
            ((serviceApplication setup mode deadline leaks).invoke
              players who execution).support at reached
        rw [ReactiveApplication.invoke, PMF.support_map] at reached
        obtain ⟨response, _, rfl⟩ := reached
        exact ((serviceRuntime setup mode deadline).reactive_respond_application
          leaks execution who response).1)]
  exact PMF.map_const _ _

/-- At an unfinished chance event, each scheduler command either keeps the
configuration or samples the event with its graph law. -/
private theorem sample_command_law (players : Player →
    (serviceApplication setup mode deadline leaks).Policy)
    (execution : (serviceApplication setup mode deadline leaks).Execution) (command :
        (serviceApplication setup mode deadline leaks).Command)
    (event : (serviceGraph setup mode).EventId)
        (ready : execution.application.config.cut.Ready event)
    (actorless : (serviceGraph setup mode).actor? event = none)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (action : (serviceGraph setup mode).Action event) :
    ((serviceApplication setup mode deadline leaks).dispatch players command execution).map
        (fun next => next.application.config) = PMF.pure execution.application.config ∨
      ((serviceApplication setup mode deadline leaks).dispatch players command execution).map
        (fun next => next.application.config) =
          execution.application.config.step event ready action := by
  let app := serviceApplication setup mode deadline leaks
  have soleOf (other : (serviceGraph setup mode).EventId)
      (otherReady : execution.application.config.cut.Ready other) : other = event :=
    alone _ other ready otherReady
  have dispatched : (app.dispatch players command execution).map
      (fun next => next.application.config) =
        (execution.environmentStep app command).map (fun next => next.application.config) := by
    unfold ReactiveApplication.dispatch
    rw [PMF.map_bind]
    calc _ = (execution.environmentStep app command).bind
          (fun middle => PMF.pure middle.application.config) :=
          bind_congr_on_support _ fun middle _ => resume_config_law players _ middle
      _ = _ := PMF.bind_pure_comp _ _
  rw [dispatched]
  have stays : (∀ other ∈ (execution.environmentStep app command).support,
      other.application.config = execution.application.config) →
      (execution.environmentStep app command).map (fun next => next.application.config) =
        PMF.pure execution.application.config := by
    intro all
    rw [map_congr_on_support _ (g := fun _ => execution.application.config) all]
    exact PMF.map_const _ _
  cases command with
  | activate who =>
      exact Or.inl (stays fun other moved => by
        rw [activation_application setup leaks execution other who moved])
  | wait =>
      exact Or.inl (stays fun other moved => by
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
        cases (PMF.mem_support_pure_iff _ _).mp moved
        rfl)
  | «include» id =>
      refine Or.inl (stays fun other moved => ?_)
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
      cases found : execution.network.lookup id with
      | none => rfl
      | some message =>
          change (((serviceApplication setup mode deadline leaks).handle execution.application
            message).getD execution.application).config = _
          cases reactiveAccepted :
              (serviceApplication setup mode deadline leaks).handle execution.application
              message with
          | none => rfl
          | some state =>
              have accepted := reactiveHandle_call reactiveAccepted
              exfalso
              obtain ⟨named, namedEq, namedReady, _, _⟩ :=
                handle_config_mem_step (serviceRuntime setup mode deadline) _ _ _ accepted
              have namedIs := soleOf named namedReady
              subst namedIs
              have sender := handle_sender_actor
                  (serviceRuntime setup mode deadline) _ _ _ accepted named namedEq
              rw [actorless] at sender
              cases sender
  | application command =>
      have stepLaw : (execution.environmentStep app (.application command)).map
          (fun next => next.application.config) =
            (environmentStep (serviceRuntime setup mode deadline) execution.application command).map
              (fun state => state.config) := by
        unfold ReactiveApplication.Execution.environmentStep
        rw [PMF.map_comp, PMF.map_comp]
        rfl
      rw [stepLaw]
      have pureStays : environmentStep
          (serviceRuntime setup mode deadline) execution.application command =
          PMF.pure execution.application →
          (environmentStep (serviceRuntime setup mode deadline) execution.application command).map
            (fun state => state.config) = PMF.pure execution.application.config := by
        intro pure
        rw [pure, PMF.pure_map]
      cases command with
      | advanceClock =>
          left
          simp only [environmentStep, PMF.pure_map]
      | executeSample other =>
          by_cases otherReady : execution.application.config.cut.Ready other
          · have otherIs := soleOf other otherReady
            subst otherIs
            cases node : nodeView (serviceGraph setup mode) other with
            | sample payload law outputEq codeEq =>
                right
                rw [environmentStep_executeSample_eq _ _ other otherReady payload law outputEq
                  codeEq node, PMF.map_comp]
                obtain ⟨marker, rfl⟩ : ∃ marker : PUnit,
                    action = cast (congrArg EventGraph.EventField.Action outputEq.symm) marker :=
                  ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
                cases marker
                exact PMF.map_id _
            | bind actor payload outputEq codeEq =>
                have some := nodeView_bind_actor outputEq codeEq
                rw [actorless] at some
                cases some
            | resolve actor payload binding checks outputEq codeEq =>
                have some := nodeView_resolve_actor outputEq codeEq
                rw [actorless] at some
                cases some
          · exact Or.inl (pureStays
              (environmentStep_executeSample_of_not_ready _ _ _ otherReady))
      | expire other =>
          left
          apply pureStays
          by_cases otherReady : execution.application.config.cut.Ready other
          · have otherIs := soleOf other otherReady
            subst otherIs
            cases activated : execution.application.activatedAt other with
            | none => exact environmentStep_expire_of_not_activated _ _ other otherReady activated
            | some entered =>
                by_cases due : (serviceRuntime setup mode deadline).deadline other ≤
                    execution.application.clock - entered
                · cases node : nodeView (serviceGraph setup mode) other with
                  | sample payload law outputEq codeEq =>
                      exact environmentStep_expire_sample_eq _ _ other otherReady entered
                        activated due payload law outputEq codeEq node
                  | bind actor payload outputEq codeEq =>
                      have some := nodeView_bind_actor outputEq codeEq
                      rw [actorless] at some
                      cases some
                  | resolve actor payload binding checks outputEq codeEq =>
                      have some := nodeView_resolve_actor outputEq codeEq
                      rw [actorless] at some
                      cases some
                · exact environmentStep_expire_of_not_due _ _ other otherReady entered activated
                    due
          · exact environmentStep_expire_of_not_ready _ _ _ otherReady

/-- The configuration law of a round at an unfinished chance event, bound
with a continuation that is the sampling law at the unchanged configuration
and a point mass after completion, is the sampling law. -/
private theorem chance_round_bind (scheduler :
    (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy)
    (execution : (serviceApplication setup mode deadline leaks).Execution) (event :
        (serviceGraph setup mode).EventId)
    (ready : execution.application.config.cut.Ready event)
    (actorless : (serviceGraph setup mode).actor? event = none)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (action : (serviceGraph setup mode).Action event)
    (continuation : (serviceGraph setup mode).Config → PMF (serviceGraph setup mode).Config)
    (unchanged : continuation execution.application.config =
      execution.application.config.step event ready action)
    (completed : ∀ next ∈ (execution.application.config.step event ready action).support,
      continuation next = PMF.pure next) :
    (((serviceApplication setup mode deadline leaks).round scheduler players execution).map
        (fun next => next.application.config)).bind continuation =
      execution.application.config.step event ready action := by
  let app := serviceApplication setup mode deadline leaks
  unfold ReactiveApplication.round
  rw [PMF.map_bind, PMF.bind_bind]
  calc _ = (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind
        (fun _ => execution.application.config.step event ready action) := by
        apply bind_congr_on_support _
        intro command _
        rcases sample_command_law players execution command event ready actorless alone action with
          stays | samples
        · rw [stays, PMF.pure_bind, unchanged]
        · rw [samples]
          calc _ = (execution.application.config.step event ready action).bind PMF.pure :=
                bind_congr_on_support _ fun next member => completed next member
            _ = _ := PMF.bind_pure _
    _ = _ := PMF.bind_const _ _

/-- **The chance phase.** From an unfinished chance event ready alone at
configuration `config`, a run that stops only once the event has completed has
the event's sampling law on configurations. -/
theorem chance_runUntil (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (event :
        (serviceGraph setup mode).EventId)
    (actorless : (serviceGraph setup mode).actor? event = none) (config :
        (serviceGraph setup mode).Config)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (ready : config.cut.Ready event) (action : (serviceGraph setup mode).Action event) :
    ∀ (count : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution),
      execution.application.config = config →
      (∀ stopped ∈ ((serviceApplication setup mode deadline leaks).runUntil scheduler players
          (fun final => event ∈ final.application.config.cut.completed) count execution).support,
        event ∈ stopped.application.config.cut.completed) →
      ((serviceApplication setup mode deadline leaks).runUntil scheduler players
          (fun final => event ∈ final.application.config.cut.completed) count execution).map
        (fun stopped => stopped.application.config) = config.step event ready action := by
  classical
  let app := serviceApplication setup mode deadline leaks
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
  have openAt (execution : app.Execution) (same : execution.application.config = config) :
      ¬ stop execution := by
    change event ∉ _
    rw [same]
    exact ready.1
  intro count
  induction count with
  | zero =>
      intro execution same completes
      exact (openAt execution same (completes execution (by simp [ReactiveApplication.runUntil])
        )).elim
  | succ count ih =>
      intro execution same completes
      subst same
      have running : event ∉ execution.application.config.cut.completed := ready.1
      simp only [ReactiveApplication.runUntil, running, ↓reduceIte] at completes ⊢
      rw [PMF.map_bind]
      let continuation : (serviceGraph setup mode).Config → PMF
          (serviceGraph setup mode).Config := fun next =>
        if next = execution.application.config then
          execution.application.config.step event ready action
        else PMF.pure next
      calc _ = (app.round scheduler players execution).bind
            (fun next => continuation next.application.config) := by
            apply bind_congr_on_support _
            intro next moved
            have rest : ∀ stopped ∈ (app.runUntil scheduler players stop count next).support,
                stop stopped := fun stopped member => completes stopped
              (by rw [PMF.mem_support_bind_iff]; exact ⟨next, moved, member⟩)
            by_cases unchanged : next.application.config = execution.application.config
            · simp only [continuation, unchanged, ↓reduceIte]
              exact ih next unchanged rest
            · simp only [continuation, unchanged, ↓reduceIte]
              rcases round_configStep setup leaks scheduler players execution next moved with
                same | ⟨other, otherReady, otherAction, member⟩
              · exact (unchanged same).elim
              · have otherIs : other = event := alone _ other ready otherReady
                subst otherIs
                have finished : stop next := by
                  change other ∈ next.application.config.cut.completed
                  rw [execution.application.config.step_cut other otherReady otherAction _ member,
                    EventOrder.Cut.mem_complete]
                  exact Or.inl rfl
                rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ next finished, PMF.pure_map]
        _ = ((app.round scheduler players execution).map
              (fun next => next.application.config)).bind continuation :=
            by rw [PMF.bind_map]; rfl
        _ = _ := chance_round_bind scheduler players execution event ready actorless alone action
            continuation (by simp [continuation]) (fun next member => by
              have completedNext : event ∈ next.cut.completed := by
                rw [execution.application.config.step_cut event ready action next member,
                  EventOrder.Cut.mem_complete]
                exact Or.inl rfl
              have different : next ≠ execution.application.config := fun same =>
                ready.1 (same ▸ completedNext)
              simp [continuation, different])


end Vegas
