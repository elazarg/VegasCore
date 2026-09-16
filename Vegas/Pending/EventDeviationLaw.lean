/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventDeviationEnvironment
import Vegas.Pending.EventDeviationInvocation
import Vegas.Pending.EventReplayEnvironment
import Vegas.Pending.EventServiceCompletion
import Vegas.Pending.EventServicePredraw
import Vegas.Pending.EventServiceReachability

/-! # Deviation law for the actual adaptive event service -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Every focal action completed by one supported transition from a reachable
control is selected by the policy extracted from actual reached actions. -/
theorem reachedFocalPolicy_controlStep
    (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (functional : ∀ (event : graph.EventId) (observation : graph.PlayerObservation focal)
      (left right : graph.Action event),
      ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation right → left = right)
    (before after : ServiceControl runtime)
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order before)
    (transition : after ∈
      (runtime.serviceControlStep roster reactionRounds players wire order before).support)
    (event : graph.EventId) (actor : graph.actor? event = some focal)
    (ready : before.execution.native.application.config.cut.Ready event)
    (action : graph.Action event)
    (completion : after.execution.native.application.config ∈
      (before.execution.native.application.config.step event ready action).support) :
    graph.normalizePolicy focal
        (reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal)
        event actor (graph.playerObserve focal before.execution.native.application.config) =
      FinDist.pure action := by
  apply runtime.reachedFocalPolicy_eq_of_functional inputs roster reactionRounds players wire
    order focal functional event actor
  exact .realized before after reachable transition actor ready completion rfl

/-- Instruction-level form of `reachedFocalPolicy_controlStep`. -/
theorem reachedFocalPolicy_serviceStep
    (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (functional : ∀ (event : graph.EventId) (observation : graph.PlayerObservation focal)
      (left right : graph.Action event),
      ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation right → left = right)
    (epochs : Nat) (instruction : ServiceInstruction graph)
    (rest : List (ServiceInstruction graph))
    (execution next : runtime.application.PolicyExecution)
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      ⟨epochs, instruction :: rest, execution⟩)
    (step : next ∈ (runtime.serviceStep players wire instruction execution).support)
    (event : graph.EventId) (actor : graph.actor? event = some focal)
    (ready : execution.native.application.config.cut.Ready event)
    (action : graph.Action event)
    (completion : next.native.application.config ∈
      (execution.native.application.config.step event ready action).support) :
    graph.normalizePolicy focal
        (reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal)
        event actor (graph.playerObserve focal execution.native.application.config) =
      FinDist.pure action := by
  let before : ServiceControl runtime := ⟨epochs, instruction :: rest, execution⟩
  let after : ServiceControl runtime := ⟨epochs, rest, next⟩
  apply runtime.reachedFocalPolicy_controlStep inputs roster reactionRounds players wire order
    focal functional before after reachable
  · simp only [before, after, serviceControlStep, FinDist.support_map, Set.mem_image]
    exact ⟨next, step, rfl⟩
  · exact completion

private theorem environmentPolicyStep_include_accept_support
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (id : MessageId Player) (message : Message Player (Payload graph))
    (lookup : execution.native.pool.lookup id = some message)
    (next : State graph)
    (accepted : runtime.handle execution.native.application message = some next) :
    ∃ after ∈
        (runtime.application.environmentPolicyStep execution (.include id)).support,
      after.native.application = next := by
  let after : runtime.application.PolicyExecution :=
    { execution with
      native := ⟨next, (execution.native.pool.includePending id).state,
        execution.native.receipts ++ [(id, true)]⟩
      environmentHistory := execution.environmentHistory ++
        [⟨MessageApplication.State.environmentView runtime.application execution.native,
          .include id⟩]
      nativeTrace := execution.nativeTrace ++ [.include id] }
  refine ⟨after, ?_, rfl⟩
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.pure_bind, FinDist.mem_support_pure]
  rw [runtime.application.includePending_accept execution.native id message next lookup accepted]

private theorem environmentPolicyStep_application_support
    (runtime : EventGraphRuntime graph)
    (execution : runtime.application.PolicyExecution)
    (command : EnvironmentCommand graph) (next : State graph)
    (supported : next ∈
      (environmentStep runtime execution.native.application command).support) :
    ∃ after ∈ (runtime.application.environmentPolicyStep execution
        (.application command)).support,
      after.native.application = next := by
  let native : runtime.application.State :=
    { execution.native with application := next }
  let after : runtime.application.PolicyExecution :=
    { execution with
      native := native
      environmentHistory := execution.environmentHistory ++
        [⟨MessageApplication.State.environmentView runtime.application execution.native,
          .application command⟩]
      nativeTrace := execution.nativeTrace ++ [.environment command] }
  refine ⟨after, ?_, rfl⟩
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.support_bind, Set.mem_iUnion, FinDist.mem_support_pure]
  refine ⟨(native, execution.nativeTrace ++ [.environment command]), ?_, rfl⟩
  rw [FinDist.support_map]
  refine ⟨native, ?_, rfl⟩
  change native ∈ (fun application : State graph =>
      ({ execution.native with application := application } : runtime.application.State)) ''
        (environmentStep runtime execution.native.application command).support
  exact ⟨next, supported, rfl⟩

/-- Assemble all unchanged-owner protocol facts at one actual reachable
control.  The age argument is the sole timing fact and is kept pointwise. -/
theorem ServiceReachable.deviationEnvironmentState
    (runtime : EventGraphRuntime graph) (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player) (control : ServiceControl runtime)
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order control)
    (opponentCompiled : ∀ owner, owner ≠ focal →
      players owner = runtime.compilePlayerPolicy owner (profile owner))
    (activationAge : ∀ owner, owner ≠ focal → ∀ event,
      graph.actor? event = some owner → ∀ entered,
        control.execution.native.application.activatedAt event = some entered →
        event ∉ control.execution.native.application.config.cut.completed →
        control.execution.native.application.clock - entered ≤ 1) :
    DeviationEnvironmentState runtime control.execution focal where
  authorship := ServiceReachable.authorship runtime inputs roster reactionRounds players wire
    order reachable
  coherent owner other := ServiceReachable.policyCoherentAll runtime inputs roster reactionRounds
    players wire order owner (profile owner) (opponentCompiled owner other) reachable
  bindingCoherent owner other := ServiceReachable.bindingPolicyCoherentAll runtime inputs roster
    reactionRounds players wire order owner (profile owner) (opponentCompiled owner other)
      reachable
  resources owner other := ServiceReachable.canonicalResources runtime inputs roster
    reactionRounds players wire order owner (profile owner) (opponentCompiled owner other)
      reachable
  bindingSubmissions owner other := ServiceReachable.bindingSubmissions runtime inputs roster
    reactionRounds players wire order owner (profile owner) (opponentCompiled owner other)
      reachable
  resolutionOrigins owner other := ServiceReachable.resolutionOrigins runtime inputs roster
    reactionRounds players wire order ordered owner (profile owner) (opponentCompiled owner other)
      reachable
  bindingInvariant := ServiceReachable.bindingInvariant runtime inputs roster reactionRounds
    players wire order reachable
  activationAge := activationAge

/-- A concrete environment policy command at one installed service
instruction conserves the continuation for the reached-action focal policy. -/
theorem environmentPolicyStep_reached_deviationContinuation
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (functional : ∀ (event : graph.EventId) (observation : graph.PlayerObservation focal)
      (left right : graph.Action event),
      ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation right → left = right)
    (epochs : Nat) (instruction : ServiceInstruction graph)
    (rest : List (ServiceInstruction graph))
    (execution : runtime.application.PolicyExecution)
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      ⟨epochs, instruction :: rest, execution⟩)
    (assumptions : DeviationEnvironmentState runtime execution focal)
    (command : runtime.application.EnvironmentPolicyCommand)
    (stepEmbed : ∀ after,
      after ∈ (runtime.application.environmentPolicyStep execution command).support →
      after ∈ (runtime.serviceStep players wire instruction execution).support) :
    let extracted :=
      reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal
    let deviationProfile : graph.BehavioralProfile :=
      Profile.update (sig := graph.gameSignature) profile focal extracted
    (runtime.application.environmentPolicyStep execution command).bind
        (fun next => next.native.application.deviationContinuation deviationProfile focal) =
      execution.native.application.deviationContinuation deviationProfile focal := by
  dsimp only
  apply runtime.environmentPolicyStep_deviationContinuation feasible ordered _ focal execution
    assumptions command
  · intro id commandEq message next lookup pending accepted event addressed ready action member
      actor
    subst command
    obtain ⟨after, supported, application⟩ :=
      environmentPolicyStep_include_accept_support runtime execution id message
        lookup next accepted
    have serviceSupported : after ∈
        (runtime.serviceStep players wire instruction execution).support := by
      exact stepEmbed after supported
    have completion : after.native.application.config ∈
        (execution.native.application.config.step event ready action).support := by
      rw [application]
      exact member
    have selected := runtime.reachedFocalPolicy_serviceStep inputs roster reactionRounds players
      wire order focal functional epochs instruction rest execution after reachable
      serviceSupported event actor ready action completion
    simpa only [Profile.update_same] using selected
  · intro event commandEq next supported ready action member actor
    subst command
    obtain ⟨after, afterSupported, application⟩ :=
      environmentPolicyStep_application_support runtime execution (.expire event) next supported
    have serviceSupported : after ∈
        (runtime.serviceStep players wire instruction execution).support := by
      exact stepEmbed after afterSupported
    have completion : after.native.application.config ∈
        (execution.native.application.config.step event ready action).support := by
      rw [application]
      exact member
    have selected := runtime.reachedFocalPolicy_serviceStep inputs roster reactionRounds players
      wire order focal functional epochs instruction rest execution after reachable
      serviceSupported event actor ready action completion
    simpa only [Profile.update_same] using selected

/-- One actual adaptive control transition conserves the deviation
continuation extracted from all actual focal completions. -/
theorem serviceControlStep_reached_deviationContinuation
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (functional : ∀ (event : graph.EventId) (observation : graph.PlayerObservation focal)
      (left right : graph.Action event),
      ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation right → left = right)
    (opponentCompiled : ∀ owner, owner ≠ focal →
      players owner = runtime.compilePlayerPolicy owner (profile owner))
    (before : ServiceControl runtime)
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order before)
    (assumptions : DeviationEnvironmentState runtime before.execution focal) :
    let extracted :=
      reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal
    let deviationProfile : graph.BehavioralProfile :=
      Profile.update (sig := graph.gameSignature) profile focal extracted
    (runtime.serviceControlStep roster reactionRounds players wire order before).bind
        (fun after => after.execution.native.application.deviationContinuation
          deviationProfile focal) =
      before.execution.native.application.deviationContinuation deviationProfile focal := by
  dsimp only
  rcases before with ⟨epochs, plan, execution⟩
  cases plan with
  | nil =>
      cases epochs with
      | zero => simp [serviceControlStep]
      | succ epochs =>
          simp only [serviceControlStep, FinDist.bind_map]
          exact FinDist.bind_const _ _
  | cons instruction rest =>
      rw [show runtime.serviceControlStep roster reactionRounds players wire order
          ⟨epochs, instruction :: rest, execution⟩ =
          (runtime.serviceStep players wire instruction execution).map
            (fun next => ⟨epochs, rest, next⟩) from rfl,
        FinDist.bind_map]
      cases instruction with
      | player who =>
          by_cases same : who = focal
          · subst who
            exact runtime.focalPlayer_invoke_deviationContinuation _ focal players
              (runtime.application.wireEnvironment wire) execution
          · apply runtime.compiledOpponent_invoke_deviationContinuation ordered _ focal who same
              players (runtime.application.wireEnvironment wire) execution
              (assumptions.coherent who same)
            rw [Profile.update_of_ne _ _ same]
            exact opponentCompiled who same
      | wire =>
          simp only [serviceStep, MessageApplication.invoke, FinDist.bind_bind]
          calc
            _ = (runtime.application.wireEnvironment wire execution.environmentHistory
                  (MessageApplication.State.environmentView runtime.application
                    execution.native)).bind
                (fun _ => execution.native.application.deviationContinuation
                  (Profile.update (sig := graph.gameSignature) profile focal
                    (runtime.reachedFocalPolicy inputs roster reactionRounds players wire order
                      focal)) focal) := by
              apply FinDist.bind_congr
              intro command commandMem
              apply runtime.environmentPolicyStep_reached_deviationContinuation feasible ordered
                inputs profile roster reactionRounds players wire order focal functional epochs
                .wire rest execution reachable assumptions
              intro after afterMem
              simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
                Set.mem_iUnion]
              exact ⟨command, commandMem, afterMem⟩
            _ = _ := FinDist.bind_const _ _
      | grant event =>
          apply runtime.environmentPolicyStep_reached_deviationContinuation feasible ordered
            inputs profile roster reactionRounds players wire order focal functional epochs
            (.grant event) rest execution reachable assumptions
          intro after afterMem
          exact afterMem
      | includeLatest event owner =>
          apply runtime.environmentPolicyStep_reached_deviationContinuation feasible ordered
            inputs profile roster reactionRounds players wire order focal functional epochs
            (.includeLatest event owner) rest execution reachable assumptions
          intro after afterMem
          exact afterMem
      | sample event =>
          apply runtime.environmentPolicyStep_reached_deviationContinuation feasible ordered
            inputs profile roster reactionRounds players wire order focal functional epochs
            (.sample event) rest execution reachable assumptions
          intro after afterMem
          exact afterMem
      | tick =>
          apply runtime.environmentPolicyStep_reached_deviationContinuation feasible ordered
            inputs profile roster reactionRounds players wire order focal functional epochs .tick
            rest execution reachable assumptions
          intro after afterMem
          exact afterMem
      | expire event =>
          apply runtime.environmentPolicyStep_reached_deviationContinuation feasible ordered
            inputs profile roster reactionRounds players wire order focal functional epochs
            (.expire event) rest execution reachable assumptions
          intro after afterMem
          exact afterMem

/-- Finite iteration of the actual adaptive controller conserves the same
deviation continuation.  The invariant premise contains only pointwise native
protocol facts at reachable source controls, not a semantic law. -/
theorem runServiceControlSteps_reached_deviationContinuation
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (functional : ∀ (event : graph.EventId) (observation : graph.PlayerObservation focal)
      (left right : graph.Action event),
      ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation right → left = right)
    (opponentCompiled : ∀ owner, owner ≠ focal →
      players owner = runtime.compilePlayerPolicy owner (profile owner))
    (environmentState : ∀ control,
      ServiceReachable runtime inputs roster reactionRounds players wire order control →
      DeviationEnvironmentState runtime control.execution focal) :
    ∀ fuel (before : ServiceControl runtime),
      ServiceReachable runtime inputs roster reactionRounds players wire order before →
      let extracted :=
        reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal
      let deviationProfile : graph.BehavioralProfile :=
        Profile.update (sig := graph.gameSignature) profile focal extracted
      (runtime.runServiceControlSteps roster reactionRounds players wire order fuel before).bind
          (fun after => after.execution.native.application.deviationContinuation
            deviationProfile focal) =
        before.execution.native.application.deviationContinuation deviationProfile focal := by
  intro fuel
  induction fuel with
  | zero =>
      intro before reachable
      simp [runServiceControlSteps]
  | succ fuel ih =>
      intro before reachable
      dsimp only
      rcases before with ⟨epochs, plan, execution⟩
      cases epochs with
      | zero =>
          cases plan with
          | nil => simp [runServiceControlSteps]
          | cons instruction rest =>
              simp only [runServiceControlSteps, FinDist.bind_bind]
              calc
                _ = (runtime.serviceControlStep roster reactionRounds players wire order
                      ⟨0, instruction :: rest, execution⟩).bind
                    (fun middle => middle.execution.native.application.deviationContinuation
                      (Profile.update (sig := graph.gameSignature) profile focal
                        (runtime.reachedFocalPolicy inputs roster reactionRounds players wire order
                          focal)) focal) := by
                    apply FinDist.bind_congr
                    intro middle member
                    exact ih middle (.step reachable member)
                _ = _ := runtime.serviceControlStep_reached_deviationContinuation feasible
                  ordered inputs profile roster reactionRounds players wire order focal functional
                  opponentCompiled _ reachable (environmentState _ reachable)
      | succ epochs =>
          cases plan with
          | nil =>
              simp only [runServiceControlSteps, FinDist.bind_bind]
              calc
                _ = (runtime.serviceControlStep roster reactionRounds players wire order
                      ⟨epochs + 1, [], execution⟩).bind
                    (fun middle => middle.execution.native.application.deviationContinuation
                      (Profile.update (sig := graph.gameSignature) profile focal
                        (runtime.reachedFocalPolicy inputs roster reactionRounds players wire order
                          focal)) focal) := by
                    apply FinDist.bind_congr
                    intro middle member
                    exact ih middle (.step reachable member)
                _ = _ := runtime.serviceControlStep_reached_deviationContinuation feasible
                  ordered inputs profile roster reactionRounds players wire order focal functional
                  opponentCompiled _ reachable (environmentState _ reachable)
          | cons instruction rest =>
              simp only [runServiceControlSteps, FinDist.bind_bind]
              calc
                _ = (runtime.serviceControlStep roster reactionRounds players wire order
                      ⟨epochs + 1, instruction :: rest, execution⟩).bind
                    (fun middle => middle.execution.native.application.deviationContinuation
                      (Profile.update (sig := graph.gameSignature) profile focal
                        (runtime.reachedFocalPolicy inputs roster reactionRounds players wire order
                          focal)) focal) := by
                    apply FinDist.bind_congr
                    intro middle member
                    exact ih middle (.step reachable member)
                _ = _ := runtime.serviceControlStep_reached_deviationContinuation feasible
                  ordered inputs profile roster reactionRounds players wire order focal functional
                  opponentCompiled _ reachable (environmentState _ reachable)

/-- The exact finite control horizon reaches a terminal graph configuration
from every initialized input, independently of native strategies. -/
theorem runServiceControlSteps_initial_terminal
    (runtime : EventGraphRuntime graph) (input : graph.Inputs)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (after : ServiceControl runtime)
    (supported : after ∈
      (runtime.runServiceControlSteps roster reactionRounds players wire order
        (runtime.serviceControlFuel roster reactionRounds runtime.serviceEpochs [])
        ⟨runtime.serviceEpochs, [],
          MessageApplication.PolicyExecution.initial runtime.application
            (MessageApplication.State.initial runtime.application
              (State.initial input))⟩).support) :
    after.execution.native.application.config.cut.Terminal := by
  have executionMem : after.execution ∈
      ((runtime.runServiceControlSteps roster reactionRounds players wire order
        (runtime.serviceControlFuel roster reactionRounds runtime.serviceEpochs [])
        ⟨runtime.serviceEpochs, [],
          MessageApplication.PolicyExecution.initial runtime.application
            (MessageApplication.State.initial runtime.application
              (State.initial input))⟩).map ServiceControl.execution).support := by
    rw [FinDist.support_map]
    exact ⟨after, supported, rfl⟩
  rw [runtime.runServiceControlSteps_map_execution roster reactionRounds players wire order,
    runtime.evalServiceControl_nil roster reactionRounds players wire order] at executionMem
  exact runtime.runService_terminal input roster reactionRounds players wire order _ _
    (State.initial_invariant input) executionMem

/-- At the finite service horizon, control conservation becomes the complete
terminal semantic law for the reached-action focal policy. -/
theorem runServiceControlSteps_reached_semantic_law
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (input : graph.Inputs) (inputMem : input ∈ inputs.support)
    (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (functional : ∀ (event : graph.EventId) (observation : graph.PlayerObservation focal)
      (left right : graph.Action event),
      ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation right → left = right)
    (opponentCompiled : ∀ owner, owner ≠ focal →
      players owner = runtime.compilePlayerPolicy owner (profile owner))
    (environmentState : ∀ control,
      ServiceReachable runtime inputs roster reactionRounds players wire order control →
      DeviationEnvironmentState runtime control.execution focal) :
    let extracted :=
      reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal
    let deviationProfile : graph.BehavioralProfile :=
      Profile.update (sig := graph.gameSignature) profile focal extracted
    let initial : ServiceControl runtime :=
      ⟨runtime.serviceEpochs, [],
        MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application (State.initial input))⟩
    (runtime.runServiceControlSteps roster reactionRounds players wire order
        (runtime.serviceControlFuel roster reactionRounds runtime.serviceEpochs []) initial).map
          (fun after => graph.semanticKey after.execution.native.application.config) =
      (graph.runPolicies graph.canonicalScheduler
        (graph.normalizeProfile deviationProfile) input).map graph.semanticKey := by
  dsimp only
  let initial : ServiceControl runtime :=
    ⟨runtime.serviceEpochs, [],
      MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial input))⟩
  have reachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      initial := .initial input inputMem
  have conserved := runtime.runServiceControlSteps_reached_deviationContinuation feasible ordered
    inputs profile roster reactionRounds players wire order focal functional opponentCompiled
    environmentState (runtime.serviceControlFuel roster reactionRounds runtime.serviceEpochs [])
    initial reachable
  calc
    _ = (runtime.runServiceControlSteps roster reactionRounds players wire order
          (runtime.serviceControlFuel roster reactionRounds runtime.serviceEpochs []) initial).bind
        (fun after => after.execution.native.application.deviationContinuation
          (Profile.update (sig := graph.gameSignature) profile focal
            (runtime.reachedFocalPolicy inputs roster reactionRounds players wire order focal))
          focal) := by
      rw [FinDist.map_eq_bind]
      apply FinDist.bind_congr
      intro after member
      exact (after.execution.native.application.deviationContinuation_terminal _ focal
        (runtime.runServiceControlSteps_initial_terminal input roster reactionRounds players wire
          order after member)).symm
    _ = initial.execution.native.application.deviationContinuation
          (Profile.update (sig := graph.gameSignature) profile focal
            (runtime.reachedFocalPolicy inputs roster reactionRounds players wire order focal))
          focal := conserved
    _ = graph.canonicalContinuation
          (Profile.update (sig := graph.gameSignature) profile focal
            (runtime.reachedFocalPolicy inputs roster reactionRounds players wire order focal))
          (Config.initial input) := State.deviationContinuation_initial input _ focal
    _ = _ := graph.canonicalContinuation_initial _ input

/-- Store projection of the terminal semantic deviation law. -/
theorem runServiceControlSteps_reached_store_law
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (input : graph.Inputs) (inputMem : input ∈ inputs.support)
    (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (functional : ∀ (event : graph.EventId) (observation : graph.PlayerObservation focal)
      (left right : graph.Action event),
      ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation right → left = right)
    (opponentCompiled : ∀ owner, owner ≠ focal →
      players owner = runtime.compilePlayerPolicy owner (profile owner))
    (environmentState : ∀ control,
      ServiceReachable runtime inputs roster reactionRounds players wire order control →
      DeviationEnvironmentState runtime control.execution focal) :
    let extracted :=
      reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal
    let deviationProfile : graph.BehavioralProfile :=
      Profile.update (sig := graph.gameSignature) profile focal extracted
    let initial : ServiceControl runtime :=
      ⟨runtime.serviceEpochs, [],
        MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application (State.initial input))⟩
    (runtime.runServiceControlSteps roster reactionRounds players wire order
        (runtime.serviceControlFuel roster reactionRounds runtime.serviceEpochs []) initial).map
          (fun after => after.execution.native.application.config.store) =
      (graph.runPolicies graph.canonicalScheduler
        (graph.normalizeProfile deviationProfile) input).map (fun config => config.store) := by
  dsimp only
  have semanticLaw := runtime.runServiceControlSteps_reached_semantic_law feasible ordered inputs
    input inputMem profile roster reactionRounds players wire order focal functional
    opponentCompiled environmentState
  have projected := congrArg (fun measure : FinDist graph.SemanticKey =>
    measure.map fun key => key.2.1) semanticLaw
  simpa only [FinDist.map_comp, Function.comp_def, semanticKey, storeRecall] using projected

/-- The actual big-step service execution has the same terminal store law as
the small-step control used to establish reachability. -/
theorem runService_reached_store_law
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (input : graph.Inputs) (inputMem : input ∈ inputs.support)
    (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (focal : Player)
    (functional : ∀ (event : graph.EventId) (observation : graph.PlayerObservation focal)
      (left right : graph.Action event),
      ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation right → left = right)
    (opponentCompiled : ∀ owner, owner ≠ focal →
      players owner = runtime.compilePlayerPolicy owner (profile owner))
    (environmentState : ∀ control,
      ServiceReachable runtime inputs roster reactionRounds players wire order control →
      DeviationEnvironmentState runtime control.execution focal) :
    let extracted :=
      reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal
    let deviationProfile : graph.BehavioralProfile :=
      Profile.update (sig := graph.gameSignature) profile focal extracted
    (runtime.runService roster reactionRounds players wire order runtime.serviceEpochs
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial input)))).map
          (fun next => next.native.application.config.store) =
      (graph.runPolicies graph.canonicalScheduler
        (graph.normalizeProfile deviationProfile) input).map (fun config => config.store) := by
  dsimp only
  let initialExecution := MessageApplication.PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application (State.initial input))
  let initialControl : ServiceControl runtime :=
    ⟨runtime.serviceEpochs, [], initialExecution⟩
  have controlLaw := runtime.runServiceControlSteps_reached_store_law feasible ordered inputs input
    inputMem profile roster reactionRounds players wire order focal functional opponentCompiled
    environmentState
  have executionLaw := runtime.runServiceControlSteps_map_execution roster reactionRounds players
    wire order runtime.serviceEpochs [] initialExecution
  rw [runtime.evalServiceControl_nil roster reactionRounds players wire order] at executionLaw
  have projected := congrArg (fun measure : FinDist runtime.application.PolicyExecution =>
    measure.map fun next => next.native.application.config.store) executionLaw
  simp only [FinDist.map_comp, Function.comp_def] at projected
  exact projected.symm.trans controlLaw

/-- The native law follows from two structural reachability facts:
functionality of reached focal actions and the unchanged-owner activation-age
certificate. -/
theorem servicedEventGame_reached_store_law
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (focal : Player) (replacement : runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    let players := Profile.update
      (sig := MessageApplication.policySignature Player runtime.application)
      (runtime.compileProfile profile) focal replacement
    let extracted :=
      reachedFocalPolicy runtime inputs roster reactionRounds players wire order focal
    (∀ (event : graph.EventId) (observation : graph.PlayerObservation focal)
      (left right : graph.Action event),
      ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players wire order focal event
          observation right → left = right) →
    (∀ (control : ServiceControl runtime),
      ServiceReachable runtime inputs roster reactionRounds players wire order control →
      ∀ owner, owner ≠ focal → ∀ event, graph.actor? event = some owner → ∀ entered,
        control.execution.native.application.activatedAt event = some entered →
        event ∉ control.execution.native.application.config.cut.completed →
        control.execution.native.application.clock - entered ≤ 1) →
    ((runtime.servicedEventGame inputs roster reactionRounds wire order).play players).map
        (fun next => next.native.application.config.store) =
      inputs.bind fun input =>
        (graph.runPolicies graph.canonicalScheduler
          (graph.normalizeProfile
            (Profile.update (sig := graph.gameSignature) profile focal extracted)) input).map
              (fun config => config.store) := by
  dsimp only
  intro functional activationAge
  let players := Profile.update
    (sig := MessageApplication.policySignature Player runtime.application)
    (runtime.compileProfile profile) focal replacement
  have opponentCompiled : ∀ owner, owner ≠ focal →
      players owner = runtime.compilePlayerPolicy owner (profile owner) := by
    intro owner other
    exact Profile.update_of_ne _ _ other
  have environmentState : ∀ control,
      ServiceReachable runtime inputs roster reactionRounds players wire order control →
      DeviationEnvironmentState runtime control.execution focal := by
    intro control reachable
    exact reachable.deviationEnvironmentState runtime ordered inputs profile roster reactionRounds
      players wire order focal control opponentCompiled (activationAge control reachable)
  change (inputs.bind _).map _ = _
  rw [FinDist.map_bind]
  apply FinDist.bind_congr
  intro input inputMem
  exact runtime.runService_reached_store_law feasible ordered inputs input inputMem profile roster
    reactionRounds players wire order focal functional opponentCompiled environmentState

/-- Joint predrawing of the focal player, wire, and adaptive order turns the
native deviation into a finite mixture of graph-policy deviations. -/
theorem exists_reachedPolicy_mixture_store_law
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (focal : Player) (replacement : runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (functional : ∀ (response : PureServiceResponses runtime) (event : graph.EventId)
      (observation : graph.PlayerObservation focal) (left right : graph.Action event),
      let players := Profile.update
        (sig := MessageApplication.policySignature Player runtime.application)
        (runtime.compileProfile profile) focal response.playerPure
      ReachedFocalAction runtime inputs roster reactionRounds players response.wirePure
          response.orderPure focal event observation left →
        ReachedFocalAction runtime inputs roster reactionRounds players response.wirePure
          response.orderPure focal event observation right → left = right)
    (activationAge : ∀ (response : PureServiceResponses runtime),
      let players := Profile.update
        (sig := MessageApplication.policySignature Player runtime.application)
        (runtime.compileProfile profile) focal response.playerPure
      ∀ (control : ServiceControl runtime),
        ServiceReachable runtime inputs roster reactionRounds players response.wirePure
          response.orderPure control →
        ∀ owner, owner ≠ focal → ∀ event, graph.actor? event = some owner → ∀ entered,
          control.execution.native.application.activatedAt event = some entered →
          event ∉ control.execution.native.application.config.cut.completed →
          control.execution.native.application.clock - entered ≤ 1) :
    ∃ mixture : FinDist (graph.BehavioralPolicy focal),
      ((runtime.servicedEventGame inputs roster reactionRounds wire order).play
        (Profile.update (sig := MessageApplication.policySignature Player runtime.application)
          (runtime.compileProfile profile) focal replacement)).map
            (fun next => next.native.application.config.store) =
        mixture.bind fun alternative =>
          inputs.bind fun input =>
            (graph.runPolicies graph.canonicalScheduler
              (graph.normalizeProfile
                (Profile.update (sig := graph.gameSignature) profile focal alternative))
              input).map (fun config => config.store) := by
  obtain ⟨responses, responseLaw⟩ := runtime.exists_pureServiceResponses_mixture inputs roster
    reactionRounds (runtime.compileProfile profile) wire order focal replacement
  let nativePlayers : PureServiceResponses runtime →
      Player → runtime.application.PlayerPolicy := fun response =>
    Profile.update (sig := MessageApplication.policySignature Player runtime.application)
      (runtime.compileProfile profile) focal response.playerPure
  let alternative : PureServiceResponses runtime → graph.BehavioralPolicy focal :=
    fun response => runtime.reachedFocalPolicy inputs roster reactionRounds
      (nativePlayers response) response.wirePure response.orderPure focal
  let mixture : FinDist (graph.BehavioralPolicy focal) := responses.map alternative
  refine ⟨mixture, ?_⟩
  have projected := congrArg
    (fun measure : FinDist runtime.application.PolicyExecution =>
      measure.map fun next => next.native.application.config.store) responseLaw
  rw [FinDist.map_bind] at projected
  calc
    _ = responses.bind (fun response =>
          ((runtime.servicedEventGame inputs roster reactionRounds response.wirePure
            response.orderPure).play (nativePlayers response)).map
              (fun next => next.native.application.config.store)) := projected
    _ = responses.bind (fun response =>
          inputs.bind fun input =>
            (graph.runPolicies graph.canonicalScheduler
              (graph.normalizeProfile
                (Profile.update (sig := graph.gameSignature) profile focal
                  (alternative response))) input).map (fun config => config.store)) := by
        apply FinDist.bind_congr
        intro response _
        exact runtime.servicedEventGame_reached_store_law feasible ordered inputs profile roster
          reactionRounds focal response.playerPure response.wirePure response.orderPure
          (functional response) (activationAge response)
    _ = mixture.bind (fun alternative =>
          inputs.bind fun input =>
            (graph.runPolicies graph.canonicalScheduler
              (graph.normalizeProfile
                (Profile.update (sig := graph.gameSignature) profile focal alternative))
              input).map (fun config => config.store)) := by
        simp only [mixture, FinDist.bind_map]

end Vegas.EventGraphRuntime
