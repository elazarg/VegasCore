/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecidedCompletion

/-! # The first-turn premises hold under the asynchronous contract

The premises `Vegas.FirstTurnCompletes` of the approximate step law hold for
every scheduler satisfying the asynchronous contract with
`delay + bound < deadline`, for every source profile whose disclosures are
effective (`Vegas.sourceServiceTurnPolicy_firstTurnCompletes`).

* `completes`: complete play completes the current event before the run stops.
* `terminal`: at the terminal rank the decoded source state is terminal.
* `exact`: at a chance event no response changes the configuration, which stays
  put until the scheduler samples, and the sample has the source law
  (`Vegas.sample_runUntil`). At an owned event the first-turn decision is a
  mixture over source actions (`Vegas.firstTurn_runUntil_mixture`), and each
  fixed action completes the event with exactly that action
  (`Vegas.decided_completion`); the source continuation decomposes the same way
  (`Vegas.SourceResidual.head_law`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- A response keeps the configuration, so resuming keeps its law. -/
private theorem resume_config_law (players : Player → (application setup leaks).Policy)
    (actor : Option Player) (execution : (application setup leaks).Execution) :
    ((application setup leaks).resume players actor execution).map
        (fun next => next.application.config) = PMF.pure execution.application.config := by
  rw [map_congr_on_support _ (g := fun _ => execution.application.config) (fun next reached => by
    cases actor with
    | none =>
        cases (PMF.mem_support_pure_iff _ _).mp reached
        rfl
    | some who =>
        change next ∈ ((application setup leaks).invoke players who execution).support at reached
        rw [ReactiveApplication.invoke, PMF.support_map] at reached
        obtain ⟨response, _, rfl⟩ := reached
        exact ((runtime setup).reactive_respond_application leaks execution who response).1)]
  exact PMF.map_const _ _

/-- At an unfinished chance event, each scheduler command either keeps the
configuration or samples the event with its graph law. -/
private theorem sample_command_law (players : Player → (application setup leaks).Policy)
    (execution : (application setup leaks).Execution) (command : (application setup leaks).Command)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (actorless : (graph setup).actor? event = none) (action : (graph setup).Action event) :
    ((application setup leaks).dispatch players command execution).map
        (fun next => next.application.config) = PMF.pure execution.application.config ∨
      ((application setup leaks).dispatch players command execution).map
        (fun next => next.application.config) =
          execution.application.config.step event ready action := by
  let app := application setup leaks
  have soleOf (other : (graph setup).EventId)
      (otherReady : execution.application.config.cut.Ready other) : other = event :=
    (soleReady_of_ready setup execution.application ready).2 other
      ((execution.application.publicView_eventReady other).mpr otherReady)
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
          change (((application setup leaks).handle execution.application
            message).getD execution.application).config = _
          cases reactiveAccepted : (application setup leaks).handle execution.application
              message with
          | none => rfl
          | some state =>
              have accepted := reactiveHandle_call reactiveAccepted
              exfalso
              obtain ⟨named, namedEq, namedReady, _, _⟩ :=
                handle_config_mem_step (runtime setup) _ _ _ accepted
              have namedIs := soleOf named namedReady
              subst namedIs
              have sender := handle_sender_actor (runtime setup) _ _ _ accepted named namedEq
              rw [actorless] at sender
              cases sender
  | application command =>
      have stepLaw : (execution.environmentStep app (.application command)).map
          (fun next => next.application.config) =
            (environmentStep (runtime setup) execution.application command).map
              (fun state => state.config) := by
        unfold ReactiveApplication.Execution.environmentStep
        rw [PMF.map_comp, PMF.map_comp]
        rfl
      rw [stepLaw]
      have pureStays : environmentStep (runtime setup) execution.application command =
          PMF.pure execution.application →
          (environmentStep (runtime setup) execution.application command).map
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
            cases node : nodeView (graph setup) other with
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
                by_cases due : (runtime setup).deadline other ≤
                    execution.application.clock - entered
                · cases node : nodeView (graph setup) other with
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
private theorem sample_round_bind (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (ready : execution.application.config.cut.Ready event)
    (actorless : (graph setup).actor? event = none) (action : (graph setup).Action event)
    (continuation : (graph setup).Config → PMF (graph setup).Config)
    (unchanged : continuation execution.application.config =
      execution.application.config.step event ready action)
    (completed : ∀ next ∈ (execution.application.config.step event ready action).support,
      continuation next = PMF.pure next) :
    (((application setup leaks).round scheduler players execution).map
        (fun next => next.application.config)).bind continuation =
      execution.application.config.step event ready action := by
  let app := application setup leaks
  unfold ReactiveApplication.round
  rw [PMF.map_bind, PMF.bind_bind]
  calc _ = (scheduler execution.environmentRecall (execution.observeEnvironment app)).bind
        (fun _ => execution.application.config.step event ready action) := by
        apply bind_congr_on_support _
        intro command _
        rcases sample_command_law players execution command event ready actorless action with
          stays | samples
        · rw [stays, PMF.pure_bind, unchanged]
        · rw [samples]
          calc _ = (execution.application.config.step event ready action).bind PMF.pure :=
                bind_congr_on_support _ fun next member => completed next member
            _ = _ := PMF.bind_pure _
    _ = _ := PMF.bind_const _ _

/-- **The chance phase.** From an unfinished chance event at configuration
`config`, a run that stops only once the event has completed has the event's
sampling law on configurations. -/
theorem sample_runUntil (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (event : (graph setup).EventId)
    (actorless : (graph setup).actor? event = none) (config : (graph setup).Config)
    (rank : Nat) (ordered : config.cut.IsPrefix rank)
    (ready : config.cut.Ready event) (action : (graph setup).Action event) :
    ∀ (count : Nat) (execution : (application setup leaks).Execution),
      execution.application.config = config →
      (∀ stopped ∈ ((application setup leaks).runUntil scheduler players
          (fun final => event ∈ final.application.config.cut.completed) count execution).support,
        event ∈ stopped.application.config.cut.completed) →
      ((application setup leaks).runUntil scheduler players
          (fun final => event ∈ final.application.config.cut.completed) count execution).map
        (fun stopped => stopped.application.config) = config.step event ready action := by
  classical
  let app := application setup leaks
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
      let continuation : (graph setup).Config → PMF (graph setup).Config := fun next =>
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
              rcases (round_configStep setup leaks scheduler players execution next moved).prefix
                  rank ordered with same | advanced
              · exact (unchanged same).elim
              · have finished : stop next := (advanced.2 event).mpr (by
                  rw [(ready_iff_rank setup _ rank ordered event).mp ready]
                  exact Nat.lt_succ_self _)
                rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ next finished, PMF.pure_map]
        _ = ((app.round scheduler players execution).map
              (fun next => next.application.config)).bind continuation :=
            by rw [PMF.bind_map]; rfl
        _ = _ := sample_round_bind scheduler players execution event ready actorless action
            continuation (by simp [continuation]) (fun next member => by
              have completedNext : event ∈ next.cut.completed := by
                rw [execution.application.config.step_cut event ready action next member,
                  EventOrder.Cut.mem_complete]
                exact Or.inl rfl
              have different : next ≠ execution.application.config := fun same =>
                ready.1 (same ▸ completedNext)
              simp [continuation, different])

/-- **The first-turn premises hold under the asynchronous contract.** For every
scheduler satisfying the contract with `delay + bound < deadline`, every turn
timing, and every source profile whose disclosures are effective, the
turn-counted policy with the contract's inclusion bound completes each event
before the run stops, deciding at the first turn is exact, and the terminal
continuation is the readout. -/
theorem sourceServiceTurnPolicy_firstTurnCompletes [Finite Player]
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context)) :
    FirstTurnCompletes setup leaks scheduler horizon bound turns timing profile := by
  let app := application setup leaks
  refine ⟨fun event execution boundary bounded stopped reached =>
    completionRun_completes contract.completes event execution boundary bounded stopped reached,
    ?_, fun execution boundary => boundary.terminal_continuation (profile := profile)⟩
  intro event start boundary bounded
  have ready : start.application.config.cut.Ready event :=
    (ready_iff_rank setup _ event.val boundary.ordered event).mpr rfl
  obtain ⟨residual⟩ := boundary.sourceResidual (profile := profile)
  obtain ⟨law, continuation, policy, effectiveLaw⟩ :=
    SourceResidual.head_law leaks residual event rfl ready
  rw [continuation]
  obtain ⟨startTrace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
    (sourceServiceTurnPolicy setup leaks bound turns timing profile) _ bounded start
    boundary.supported
  cases owned : (graph setup).actor? event with
  | none =>
      have profileEq : firstTurnProfile setup leaks bound turns profile event =
          fun _ => app.silentPolicy := by
        unfold firstTurnProfile
        simp only [owned]
        rfl
      rw [profileEq]
      have samples (action : (graph setup).Action event) :
          (app.runUntilHorizon scheduler (fun _ => app.silentPolicy)
            (fun final => event ∈ final.application.config.cut.completed) horizon start).map
              (fun stopped => stopped.application.config) =
            start.application.config.step event ready action :=
        sample_runUntil scheduler _ event owned start.application.config event.val
          boundary.ordered ready action _ start rfl
          (fun stopped reached => runUntilHorizon_completes contract.completes bounded startTrace
            stopped reached)
      calc _ = ((app.runUntilHorizon scheduler (fun _ => app.silentPolicy)
            (fun final => event ∈ final.application.config.cut.completed) horizon start).map
              (fun stopped => stopped.application.config)).bind
            (sourceContinuation setup profile (event.val + 1)) := by
            rw [PMF.bind_map]
            rfl
        _ = law.bind (fun _ => ((app.runUntilHorizon scheduler (fun _ => app.silentPolicy)
            (fun final => event ∈ final.application.config.cut.completed) horizon start).map
              (fun stopped => stopped.application.config)).bind
            (sourceContinuation setup profile (event.val + 1))) := (PMF.bind_const _ _).symm
        _ = _ := bind_congr_on_support law fun action _ => by rw [samples action]
  | some owner =>
      unfold ReactiveApplication.runUntilHorizon
      rw [firstTurn_runUntil_mixture event start boundary owner owned bound turns profile law
        (policy owner owned) _, PMF.bind_bind]
      apply bind_congr_on_support law
      intro action chosen
      obtain ⟨completedConfig, member⟩ :=
        (start.application.config.step event ready action).support_nonempty
      have pure := start.application.config.step_eq_pure_of_actor event ready action owner owned
        completedConfig member
      rw [pure, PMF.pure_bind]
      calc _ = (app.runUntil scheduler
            (Function.update (fun _ => app.silentPolicy) owner
              (decidedTurnPolicy setup leaks bound owner event action))
            (fun final => event ∈ final.application.config.cut.completed)
            (horizon - start.environmentRecall.length) start).bind
              (fun _ => sourceContinuation setup profile (event.val + 1) completedConfig) := by
            apply bind_congr_on_support _
            intro stopped reached
            have completed := decided_completion contract timely event start boundary bounded
              ready owned action (effectiveLaw effective action chosen) stopped reached
            rw [pure, PMF.mem_support_pure_iff] at completed
            rw [completed]
        _ = _ := PMF.bind_const _ _

end Vegas
