/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventPrescribedEnvironment
import Vegas.Pending.EventPrescribedInvocation
import Vegas.Pending.EventServiceCompletion
import Vegas.Pending.EventServiceReachability

/-! # Terminal laws of partly prescribed play on the actual adaptive service

The prescribed continuation is conserved by every reachable service control
step. At the completion horizon it is the terminal semantic law, which is the
canonical graph law of the profile. A player outside `prescribed` enters only
through `FreeActionsSelected`: its graph policy must select each of its
effective completions. Honest play has no such player; a unilateral deviation
has one.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory GameTheory.Math.Probability Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

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
    PMF.pure_bind, PMF.mem_support_pure_iff _ _]
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
    PMF.support_bind, Set.mem_iUnion, PMF.mem_support_pure_iff _ _]
  refine ⟨(native, execution.nativeTrace ++ [.environment command]), ?_, rfl⟩
  rw [PMF.support_map]
  refine ⟨native, ?_, rfl⟩
  change native ∈ (fun application : State graph =>
      ({ execution.native with application := application } : runtime.application.State)) ''
        (environmentStep runtime execution.native.application command).support
  exact ⟨next, supported, rfl⟩

/-- Assemble all prescribed-owner protocol facts at one actual reachable
control.  The age argument is the sole timing fact and is kept pointwise. -/
theorem ServiceReachable.prescribedEnvironmentState
    (runtime : EventGraphRuntime graph) (ordered : graph.BarrierOrdered)
    (inputs : PMF graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (prescribed : Player → Prop) (control : ServiceControl runtime)
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order control)
    (compiled : ∀ owner, prescribed owner →
      players owner = runtime.compilePlayerPolicy owner (profile owner))
    (activationAge : ∀ owner, prescribed owner → ∀ event,
      graph.actor? event = some owner → ∀ entered,
        control.execution.native.application.activatedAt event = some entered →
        event ∉ control.execution.native.application.config.cut.completed →
        control.execution.native.application.clock - entered ≤ 1) :
    PrescribedEnvironmentState runtime control.execution prescribed where
  authorship := ServiceReachable.authorship runtime inputs roster reactionRounds players wire
    order reachable
  coherent owner prescribedOwner := ServiceReachable.policyCoherentAll runtime inputs roster
    reactionRounds players wire order owner (profile owner) (compiled owner prescribedOwner)
      reachable
  bindingCoherent owner prescribedOwner := ServiceReachable.bindingPolicyCoherentAll runtime
    inputs roster reactionRounds players wire order owner (profile owner)
      (compiled owner prescribedOwner) reachable
  resources owner prescribedOwner := ServiceReachable.canonicalResources runtime inputs roster
    reactionRounds players wire order owner (profile owner) (compiled owner prescribedOwner)
      reachable
  bindingSubmissions owner prescribedOwner := ServiceReachable.bindingSubmissions runtime inputs
    roster reactionRounds players wire order owner (profile owner)
      (compiled owner prescribedOwner) reachable
  resolutionOrigins owner prescribedOwner := ServiceReachable.resolutionOrigins runtime inputs
    roster reactionRounds players wire order ordered owner (profile owner)
      (compiled owner prescribedOwner) reachable
  bindingInvariant := ServiceReachable.bindingInvariant runtime inputs roster reactionRounds
    players wire order reachable
  activationAge := activationAge

/-- Along reachable service steps, every completed action of a player who is
not prescribed is the one `profile` selects deterministically at that
completion. A unilateral deviation discharges this with the policy extracted
from reached actions; honest play has no free players. -/
def FreeActionsSelected (runtime : EventGraphRuntime graph)
    (inputs : PMF graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (profile : graph.BehavioralProfile) (prescribed : Player → Prop) : Prop :=
  ∀ (epochs : Nat) (instruction : ServiceInstruction graph)
    (rest : List (ServiceInstruction graph))
    (execution next : runtime.application.PolicyExecution),
    ServiceReachable runtime inputs roster reactionRounds players wire order
      ⟨epochs, instruction :: rest, execution⟩ →
    next ∈ (runtime.serviceStep players wire instruction execution).support →
    ∀ (event : graph.EventId) (owner : Player) (actor : graph.actor? event = some owner),
      ¬ prescribed owner →
    ∀ (ready : execution.native.application.config.cut.Ready event)
      (action : graph.Action event),
      next.native.application.config ∈
        (execution.native.application.config.step event ready action).support →
      graph.normalizePolicy owner (profile owner) event actor
        (graph.playerObserve owner execution.native.application.config) = PMF.pure action

/-- A concrete environment policy command at one installed service
instruction conserves the prescribed continuation. -/
theorem environmentPolicyStep_reached_prescribedContinuation
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : PMF graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (prescribed : Player → Prop) [DecidablePred prescribed]
    (selected : FreeActionsSelected runtime inputs roster reactionRounds players wire order
      profile prescribed)
    (epochs : Nat) (instruction : ServiceInstruction graph)
    (rest : List (ServiceInstruction graph))
    (execution : runtime.application.PolicyExecution)
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      ⟨epochs, instruction :: rest, execution⟩)
    (assumptions : PrescribedEnvironmentState runtime execution prescribed)
    (command : runtime.application.EnvironmentPolicyCommand)
    (stepEmbed : ∀ after,
      after ∈ (runtime.application.environmentPolicyStep execution command).support →
      after ∈ (runtime.serviceStep players wire instruction execution).support) :
    (runtime.application.environmentPolicyStep execution command).bind
        (fun next => next.native.application.prescribedContinuation profile prescribed) =
      execution.native.application.prescribedContinuation profile prescribed := by
  apply runtime.environmentPolicyStep_prescribedContinuation feasible ordered profile prescribed
    execution assumptions command
  · intro id commandEq message next lookup pending accepted event addressed ready action member
      owner actor free
    subst command
    obtain ⟨after, supported, application⟩ :=
      environmentPolicyStep_include_accept_support runtime execution id message
        lookup next accepted
    have completion : after.native.application.config ∈
        (execution.native.application.config.step event ready action).support := by
      rw [application]
      exact member
    exact selected epochs instruction rest execution after reachable (stepEmbed after supported)
      event owner actor free ready action completion
  · intro event commandEq next supported ready action member owner actor free
    subst command
    obtain ⟨after, afterSupported, application⟩ :=
      environmentPolicyStep_application_support runtime execution (.expire event) next supported
    have completion : after.native.application.config ∈
        (execution.native.application.config.step event ready action).support := by
      rw [application]
      exact member
    exact selected epochs instruction rest execution after reachable
      (stepEmbed after afterSupported) event owner actor free ready action completion

/-- One actual adaptive control transition conserves the prescribed
continuation. -/
theorem serviceControlStep_reached_prescribedContinuation
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : PMF graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (prescribed : Player → Prop) [DecidablePred prescribed]
    (selected : FreeActionsSelected runtime inputs roster reactionRounds players wire order
      profile prescribed)
    (compiled : ∀ owner, prescribed owner →
      players owner = runtime.compilePlayerPolicy owner (profile owner))
    (before : ServiceControl runtime)
    (reachable : ServiceReachable runtime inputs roster reactionRounds players wire order before)
    (assumptions : PrescribedEnvironmentState runtime before.execution prescribed) :
    (runtime.serviceControlStep roster reactionRounds players wire order before).bind
        (fun after => after.execution.native.application.prescribedContinuation
          profile prescribed) =
      before.execution.native.application.prescribedContinuation profile prescribed := by
  rcases before with ⟨epochs, plan, execution⟩
  cases plan with
  | nil =>
      cases epochs with
      | zero => simp [serviceControlStep]
      | succ epochs =>
          simp only [serviceControlStep, PMF.bind_map, Function.comp_def]
          exact PMF.bind_const _ _
  | cons instruction rest =>
      rw [show runtime.serviceControlStep roster reactionRounds players wire order
          ⟨epochs, instruction :: rest, execution⟩ =
          (runtime.serviceStep players wire instruction execution).map
            (fun next => ⟨epochs, rest, next⟩) from rfl,
        PMF.bind_map]
      have environment : ∀ command : runtime.application.EnvironmentPolicyCommand,
          (∀ after,
            after ∈ (runtime.application.environmentPolicyStep execution command).support →
            after ∈ (runtime.serviceStep players wire instruction execution).support) →
          (runtime.application.environmentPolicyStep execution command).bind
              (fun next => next.native.application.prescribedContinuation profile prescribed) =
            execution.native.application.prescribedContinuation profile prescribed :=
        runtime.environmentPolicyStep_reached_prescribedContinuation feasible ordered inputs
          profile roster reactionRounds players wire order prescribed selected epochs instruction
          rest execution reachable assumptions
      cases instruction with
      | player who =>
          by_cases prescribedWho : prescribed who
          · exact runtime.compiledPrescribed_invoke_prescribedContinuation ordered profile
              prescribed who prescribedWho players (runtime.application.wireEnvironment wire)
              execution (assumptions.coherent who prescribedWho) (compiled who prescribedWho)
          · exact runtime.freePlayer_invoke_prescribedContinuation profile prescribed who
              prescribedWho players (runtime.application.wireEnvironment wire) execution
      | wire =>
          simp only [serviceStep, MessageApplication.invoke, PMF.bind_bind]
          calc
            _ = (runtime.application.wireEnvironment wire execution.environmentHistory
                  (MessageApplication.State.environmentView runtime.application
                    execution.native)).bind
                (fun _ => execution.native.application.prescribedContinuation profile
                  prescribed) := by
              apply bind_congr_on_support _
              intro command commandMem
              apply environment command
              intro after afterMem
              simp only [serviceStep, MessageApplication.invoke, PMF.support_bind,
                Set.mem_iUnion]
              exact ⟨command, commandMem, afterMem⟩
            _ = _ := PMF.bind_const _ _
      | grant event => exact environment _ fun _ afterMem => afterMem
      | includeLatest event owner => exact environment _ fun _ afterMem => afterMem
      | sample event => exact environment _ fun _ afterMem => afterMem
      | tick => exact environment _ fun _ afterMem => afterMem
      | expire event => exact environment _ fun _ afterMem => afterMem

/-- Finite iteration of the actual adaptive controller conserves the same
prescribed continuation.  The invariant premise contains only pointwise native
protocol facts at reachable source controls, not a semantic law. -/
theorem runServiceControlSteps_reached_prescribedContinuation
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : PMF graph.Inputs) (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (prescribed : Player → Prop) [DecidablePred prescribed]
    (selected : FreeActionsSelected runtime inputs roster reactionRounds players wire order
      profile prescribed)
    (compiled : ∀ owner, prescribed owner →
      players owner = runtime.compilePlayerPolicy owner (profile owner))
    (environmentState : ∀ control,
      ServiceReachable runtime inputs roster reactionRounds players wire order control →
      PrescribedEnvironmentState runtime control.execution prescribed) :
    ∀ fuel (before : ServiceControl runtime),
      ServiceReachable runtime inputs roster reactionRounds players wire order before →
      (runtime.runServiceControlSteps roster reactionRounds players wire order fuel before).bind
          (fun after => after.execution.native.application.prescribedContinuation
            profile prescribed) =
        before.execution.native.application.prescribedContinuation profile prescribed := by
  intro fuel
  induction fuel with
  | zero =>
      intro before reachable
      simp [runServiceControlSteps]
  | succ fuel ih =>
      intro before reachable
      have step := runtime.serviceControlStep_reached_prescribedContinuation feasible ordered
        inputs profile roster reactionRounds players wire order prescribed selected compiled
        before reachable (environmentState before reachable)
      have tail : (runtime.serviceControlStep roster reactionRounds players wire order
            before).bind (fun middle =>
              (runtime.runServiceControlSteps roster reactionRounds players wire order fuel
                middle).bind (fun after =>
                  after.execution.native.application.prescribedContinuation profile prescribed)) =
          before.execution.native.application.prescribedContinuation profile prescribed := by
        rw [← step]
        apply bind_congr_on_support _
        intro middle member
        exact ih middle (.step reachable member)
      rcases before with ⟨epochs, plan, execution⟩
      cases epochs with
      | zero =>
          cases plan with
          | nil => simp [runServiceControlSteps]
          | cons instruction rest =>
              simp only [runServiceControlSteps, PMF.bind_bind]
              exact tail
      | succ epochs =>
          simp only [runServiceControlSteps, PMF.bind_bind]
          exact tail

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
    rw [PMF.support_map]
    exact ⟨after, supported, rfl⟩
  rw [runtime.runServiceControlSteps_map_execution roster reactionRounds players wire order,
    runtime.evalServiceControl_nil roster reactionRounds players wire order] at executionMem
  exact runtime.runService_terminal input roster reactionRounds players wire order _ _
    (State.initial_invariant input) executionMem

/-- At the finite service horizon, control conservation becomes the complete
terminal semantic law of `profile`. -/
theorem runServiceControlSteps_semantic_law
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : PMF graph.Inputs) (input : graph.Inputs) (inputMem : input ∈ inputs.support)
    (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (prescribed : Player → Prop)
    (selected : FreeActionsSelected runtime inputs roster reactionRounds players wire order
      profile prescribed)
    (compiled : ∀ owner, prescribed owner →
      players owner = runtime.compilePlayerPolicy owner (profile owner))
    (environmentState : ∀ control,
      ServiceReachable runtime inputs roster reactionRounds players wire order control →
      PrescribedEnvironmentState runtime control.execution prescribed) :
    let initial : ServiceControl runtime :=
      ⟨runtime.serviceEpochs, [],
        MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application (State.initial input))⟩
    (runtime.runServiceControlSteps roster reactionRounds players wire order
        (runtime.serviceControlFuel roster reactionRounds runtime.serviceEpochs []) initial).map
          (fun after => graph.semanticKey after.execution.native.application.config) =
      (graph.runPolicies graph.canonicalScheduler (graph.normalizeProfile profile) input).map
        graph.semanticKey := by
  classical
  dsimp only
  let initial : ServiceControl runtime :=
    ⟨runtime.serviceEpochs, [],
      MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial input))⟩
  have reachable : ServiceReachable runtime inputs roster reactionRounds players wire order
      initial := .initial input inputMem
  have conserved := runtime.runServiceControlSteps_reached_prescribedContinuation feasible
    ordered inputs profile roster reactionRounds players wire order prescribed selected compiled
    environmentState (runtime.serviceControlFuel roster reactionRounds runtime.serviceEpochs [])
    initial reachable
  calc
    _ = (runtime.runServiceControlSteps roster reactionRounds players wire order
          (runtime.serviceControlFuel roster reactionRounds runtime.serviceEpochs []) initial).bind
        (fun after => after.execution.native.application.prescribedContinuation profile
          prescribed) := by
      rw [← PMF.bind_pure_comp, Function.comp_def]
      apply bind_congr_on_support _
      intro after member
      exact (after.execution.native.application.prescribedContinuation_terminal prescribed
        profile (runtime.runServiceControlSteps_initial_terminal input roster reactionRounds
          players wire order after member)).symm
    _ = initial.execution.native.application.prescribedContinuation profile prescribed :=
      conserved
    _ = graph.canonicalContinuation profile (Config.initial input) :=
      State.prescribedContinuation_initial prescribed input profile
    _ = _ := graph.canonicalContinuation_initial _ input

/-- The actual big-step service execution has the terminal store law of
`profile`, via the small-step control used to establish reachability. -/
theorem runService_store_law
    (runtime : EventGraphRuntime graph) (feasible : runtime.ServiceFeasible)
    (ordered : graph.BarrierOrdered)
    (inputs : PMF graph.Inputs) (input : graph.Inputs) (inputMem : input ∈ inputs.support)
    (profile : graph.BehavioralProfile)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (prescribed : Player → Prop)
    (selected : FreeActionsSelected runtime inputs roster reactionRounds players wire order
      profile prescribed)
    (compiled : ∀ owner, prescribed owner →
      players owner = runtime.compilePlayerPolicy owner (profile owner))
    (environmentState : ∀ control,
      ServiceReachable runtime inputs roster reactionRounds players wire order control →
      PrescribedEnvironmentState runtime control.execution prescribed) :
    (runtime.runService roster reactionRounds players wire order runtime.serviceEpochs
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial input)))).map
          (fun next => next.native.application.config.store) =
      (graph.runPolicies graph.canonicalScheduler (graph.normalizeProfile profile) input).map
        (fun config => config.store) := by
  classical
  let initialExecution := MessageApplication.PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application (State.initial input))
  have semanticLaw := runtime.runServiceControlSteps_semantic_law feasible ordered inputs input
    inputMem profile roster reactionRounds players wire order prescribed selected compiled
    environmentState
  have controlLaw := congrArg (fun measure : PMF graph.SemanticKey =>
    measure.map fun key => key.2.1) semanticLaw
  simp only [PMF.map_comp, Function.comp_def, semanticKey, storeRecall] at controlLaw
  have executionLaw := runtime.runServiceControlSteps_map_execution roster reactionRounds players
    wire order runtime.serviceEpochs [] initialExecution
  rw [runtime.evalServiceControl_nil roster reactionRounds players wire order] at executionLaw
  have projected := congrArg (fun measure : PMF runtime.application.PolicyExecution =>
    measure.map fun next => next.native.application.config.store) executionLaw
  simp only [PMF.map_comp, Function.comp_def] at projected
  exact projected.symm.trans controlLaw

end Vegas.EventGraphRuntime
