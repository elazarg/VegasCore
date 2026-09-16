/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventService

/-! # Small-step control for bounded event service

The existing service definition is recursive by epoch and executes a selected
epoch plan in one call to `runServicePlan`.  This module exposes the same
execution as a control state with an explicit current plan.  It is the
operational layer needed by probability-protocol presentations of the focal
player, wire, and order decisions.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- The bounded service cursor. `epochs` counts epochs not yet selected;
`plan` is the unexecuted suffix of the currently selected epoch. -/
structure ServiceControl (runtime : EventGraphRuntime graph) where
  epochs : Nat
  plan : List (ServiceInstruction graph)
  execution : runtime.application.PolicyExecution

/-- A control boundary is waiting for an epoch-order decision. -/
def ServiceControl.AtOrderBoundary
    (runtime : EventGraphRuntime graph)
    (control : ServiceControl (graph := graph) runtime) : Prop :=
  control.plan = [] ∧ control.epochs ≠ 0

/-- A control state is finished precisely after all selected plans and all
epoch selections have been consumed. -/
def ServiceControl.Terminal
    (runtime : EventGraphRuntime graph)
    (control : ServiceControl (graph := graph) runtime) : Prop :=
  control.epochs = 0 ∧ control.plan = []

def ServiceInstruction.isEnvironment : ServiceInstruction graph → Bool
  | .player _ => false
  | _ => true

def ServiceInstruction.isFocalPlayer (focal : Player) : ServiceInstruction graph → Bool
  | .player who => decide (who = focal)
  | _ => false

def ServiceControl.progress (runtime : EventGraphRuntime graph)
    (control : ServiceControl runtime) : Nat :=
  control.execution.environmentHistory.length +
    control.plan.countP ServiceInstruction.isEnvironment

omit [DecidableEq Player] in
theorem epochPlan_environment_count_pos (chosen : ServiceOrder graph)
    (roster : List Player) (reactionRounds : Nat) :
    0 < (epochPlan chosen roster reactionRounds).countP
      ServiceInstruction.isEnvironment := by
  simp [epochPlan, ServiceInstruction.isEnvironment, List.countP_append]

/-- Install one selected order and consume its epoch counter. -/
def ServiceControl.selectOrder
    (runtime : EventGraphRuntime graph)
    (control : ServiceControl (graph := graph) runtime)
    (roster : List Player) (reactionRounds : Nat) (chosen : ServiceOrder graph) :
    ServiceControl runtime :=
  { epochs := control.epochs - 1
    plan := epochPlan chosen roster reactionRounds
    execution := control.execution }

theorem ServiceControl.progress_selectOrder_lt (runtime : EventGraphRuntime graph)
    (control : ServiceControl runtime) (empty : control.plan = [])
    (positive : control.epochs ≠ 0)
    (roster : List Player) (reactionRounds : Nat) (chosen : ServiceOrder graph) :
    control.progress runtime <
      (control.selectOrder runtime roster reactionRounds chosen).progress runtime := by
  rcases control with ⟨epochs, plan, execution⟩
  simp only at empty
  subst plan
  simp only [ServiceControl.progress, ServiceControl.selectOrder]
  simp only [List.countP_nil, Nat.add_zero]
  have countPositive := epochPlan_environment_count_pos chosen roster reactionRounds
  omega

/-- A service instruction records exactly one focal-player entry precisely when
that instruction invokes the focal player.  The statement is independent of
the policies and of the command selected by them. -/
theorem serviceStep_focalHistory_length (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (focal : Player)
    (instruction : ServiceInstruction graph)
    (execution next : runtime.application.PolicyExecution)
    (supported : next ∈ (runtime.serviceStep players wire instruction execution).support) :
    (next.principalHistory focal).length =
      (execution.principalHistory focal).length +
        if instruction.isFocalPlayer focal then 1 else 0 := by
  cases instruction with
  | player who =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at supported
      obtain ⟨command, _, step⟩ := supported
      by_cases same : who = focal
      · subst who
        rw [runtime.application.playerStep_history_self focal execution command next step]
        simp [ServiceInstruction.isFocalPlayer]
      · rw [runtime.application.playerStep_other_history who focal (Ne.symm same)
          execution command next step]
        simp [ServiceInstruction.isFocalPlayer, same]
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, MessageApplication.wireEnvironment,
        FinDist.bind_map, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨command, _, step⟩ := supported
      rw [congrFun (runtime.application.environmentStep_principalHistory execution
        (WireCommand.toEnvironmentCommand runtime.application command) next step) focal]
      rfl
  | grant event | sample event | tick | expire event =>
      rw [congrFun (runtime.application.environmentStep_principalHistory execution _ next
        supported) focal]
      rfl
  | includeLatest event owner =>
      rw [congrFun (runtime.application.environmentStep_principalHistory execution _ next
        supported) focal]
      rfl

/-- Player instructions leave the environment history fixed; every other
service instruction records exactly one environment entry. -/
theorem serviceStep_environmentHistory_length (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (instruction : ServiceInstruction graph)
    (execution next : runtime.application.PolicyExecution)
    (supported : next ∈ (runtime.serviceStep players wire instruction execution).support) :
    next.environmentHistory.length = execution.environmentHistory.length +
      if instruction.isEnvironment then 1 else 0 := by
  cases instruction with
  | player who =>
      simp only [serviceStep, MessageApplication.invoke, FinDist.support_bind,
        Set.mem_iUnion] at supported
      obtain ⟨command, _, step⟩ := supported
      rw [runtime.application.playerStep_environmentHistory who execution command next step]
      rfl
  | wire =>
      simp only [serviceStep, MessageApplication.invoke, MessageApplication.wireEnvironment,
        FinDist.bind_map, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨command, _, step⟩ := supported
      simpa [ServiceInstruction.isEnvironment] using
        runtime.application.environmentStep_history_length execution
          (WireCommand.toEnvironmentCommand runtime.application command) next step
  | grant event | sample event | tick | expire event =>
      simpa [ServiceInstruction.isEnvironment] using
        runtime.application.environmentStep_history_length execution _ next supported
  | includeLatest event owner =>
      simpa [ServiceInstruction.isEnvironment] using
        runtime.application.environmentStep_history_length execution _ next supported

/-- Execute the head instruction of a nonempty selected plan. -/
def ServiceControl.executeHead (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (control : ServiceControl runtime) : FinDist (ServiceControl runtime) :=
  match control.plan with
  | [] => FinDist.pure control
  | instruction :: rest =>
      (runtime.serviceStep players wire instruction control.execution).map fun execution =>
        { control with plan := rest, execution := execution }

/-- One small service-control transition. At an epoch boundary it samples the
actual adaptive order policy; inside an epoch it executes exactly one existing
service instruction. Terminal controls stutter. -/
def serviceControlStep (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (control : ServiceControl runtime) : FinDist (ServiceControl runtime) :=
  match control.plan with
  | instruction :: rest =>
      (runtime.serviceStep players wire instruction control.execution).map fun execution =>
        { control with plan := rest, execution := execution }
  | [] => match control.epochs with
    | 0 => FinDist.pure control
    | epochs + 1 =>
        (order control.execution.environmentHistory
          (MessageApplication.State.environmentView runtime.application
            control.execution.native)).map fun chosen =>
          { epochs := epochs
            plan := epochPlan chosen roster reactionRounds
            execution := control.execution }

/-- Every supported control transition is either terminal stuttering, a
public order choice with unchanged execution, or one actual plan instruction. -/
theorem serviceControlStep_cases (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : ServiceControl runtime)
    (member : after ∈
      (runtime.serviceControlStep roster reactionRounds players wire order before).support) :
    (before.plan = [] ∧ before.epochs = 0 ∧ after = before) ∨
      (∃ epochs chosen, before.plan = [] ∧ before.epochs = epochs + 1 ∧
        chosen ∈ (order before.execution.environmentHistory
          (MessageApplication.State.environmentView runtime.application
            before.execution.native)).support ∧
        after = ⟨epochs, epochPlan chosen roster reactionRounds, before.execution⟩) ∨
      ∃ instruction rest, before.plan = instruction :: rest ∧
        after.epochs = before.epochs ∧ after.plan = rest ∧
        after.execution ∈
          (runtime.serviceStep players wire instruction before.execution).support := by
  cases plan : before.plan with
  | nil =>
      cases epochs : before.epochs with
      | zero =>
          simp only [serviceControlStep, plan, epochs, FinDist.mem_support_pure] at member
          exact Or.inl ⟨rfl, rfl, member⟩
      | succ count =>
          simp only [serviceControlStep, plan, epochs, FinDist.support_map, Set.mem_image] at member
          obtain ⟨chosen, chosenMem, same⟩ := member
          exact Or.inr (Or.inl ⟨count, chosen, rfl, rfl, chosenMem, same.symm⟩)
  | cons instruction rest =>
      simp only [serviceControlStep, plan, FinDist.support_map, Set.mem_image] at member
      obtain ⟨execution, executionMem, same⟩ := member
      subst after
      exact Or.inr (Or.inr ⟨instruction, rest, rfl, rfl, rfl, executionMem⟩)

/-- The number of instructions in every epoch plan. The increasing order is
only a canonical representative; the value is independent of the selected
permutation. -/
def epochInstructionCount (_runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat) : Nat :=
  (epochPlan (ServiceOrder.increasing graph) roster reactionRounds).length

omit [DecidableEq Player] in
/-- Permuting the event sweep does not change the number of service
instructions in an epoch. -/
theorem epochPlan_length_eq_epochInstructionCount (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat) (chosen : ServiceOrder graph) :
    (epochPlan chosen roster reactionRounds).length =
      runtime.epochInstructionCount roster reactionRounds := by
  have eventLengths := chosen.property.map
    (fun event => (eventServicePlan roster reactionRounds event).length)
  have sumEq := eventLengths.sum_eq
  simpa only [epochPlan, epochInstructionCount, ServiceOrder.increasing,
    List.length_append, List.length_flatMap, List.length_cons, List.length_nil,
    Nat.add_zero, List.length_map] using congrArg (fun length => length + 1 +
      (List.finRange graph.order.eventCount).length) sumEq

/-- Exact number of small control transitions needed to consume the current
plan and all not-yet-selected epochs. Each future epoch contributes one order
selection followed by its uniform instruction count. -/
def serviceControlFuel (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (epochs : Nat) (plan : List (ServiceInstruction graph)) : Nat :=
  plan.length + epochs * (runtime.epochInstructionCount roster reactionRounds + 1)

/-- Iterate the small-step control, stopping once its terminal state is
reached. Extra fuel is therefore harmless. -/
def runServiceControlSteps (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    Nat → ServiceControl runtime → FinDist (ServiceControl runtime)
  | 0, control => FinDist.pure control
  | fuel + 1, control =>
      match control.epochs, control.plan with
      | 0, [] => FinDist.pure control
      | _, _ => (runtime.serviceControlStep roster reactionRounds players wire order control).bind
          (runtime.runServiceControlSteps roster reactionRounds players wire order fuel)

/-- Big-step evaluation from an explicit plan suffix. This definition exposes
order selection separately but delegates an installed plan to the already
verified `runServicePlan` semantics. -/
def evalServiceControl (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    Nat → List (ServiceInstruction graph) → runtime.application.PolicyExecution →
      FinDist runtime.application.PolicyExecution
  | 0, plan, execution => runtime.runServicePlan players wire plan execution
  | epochs + 1, plan, execution =>
      (runtime.runServicePlan players wire plan execution).bind fun boundary =>
        (order boundary.environmentHistory
          (MessageApplication.State.environmentView runtime.application boundary.native)).bind
            fun chosen => runtime.evalServiceControl roster reactionRounds players wire order
              epochs (epochPlan chosen roster reactionRounds) boundary

/-- At its exact uniform fuel, the small-step controller executes its installed
plan and then the original bounded service recursion. -/
theorem runServiceControlSteps_map_execution_eq_bind (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ∀ epochs plan execution,
      (runtime.runServiceControlSteps roster reactionRounds players wire order
        (runtime.serviceControlFuel roster reactionRounds epochs plan)
        ⟨epochs, plan, execution⟩).map ServiceControl.execution =
          (runtime.runServicePlan players wire plan execution).bind
            (runtime.runService roster reactionRounds players wire order epochs) := by
  intro epochs
  induction epochs with
  | zero =>
      intro plan
      induction plan with
      | nil =>
          intro execution
          simp [serviceControlFuel, runServiceControlSteps, runService, runServicePlan]
      | cons instruction rest ih =>
          intro execution
          have fuelEq : runtime.serviceControlFuel roster reactionRounds 0
                (instruction :: rest) =
              runtime.serviceControlFuel roster reactionRounds 0 rest + 1 := by
            simp [serviceControlFuel]
          rw [fuelEq]
          simp only [runServiceControlSteps, serviceControlStep, FinDist.map_bind,
            FinDist.bind_map, runServicePlan, runService, FinDist.bind_pure]
          apply FinDist.bind_congr
          intro next _
          simpa only [serviceControlFuel, Nat.zero_mul, Nat.add_zero, runService,
            FinDist.bind_pure] using ih next
  | succ epochs outer =>
      intro plan
      induction plan with
      | cons instruction rest ih =>
          intro execution
          have fuelEq : runtime.serviceControlFuel roster reactionRounds (epochs + 1)
                (instruction :: rest) =
              runtime.serviceControlFuel roster reactionRounds (epochs + 1) rest + 1 := by
            simp [serviceControlFuel, Nat.add_assoc]
            omega
          rw [fuelEq]
          simp only [runServiceControlSteps, serviceControlStep, FinDist.map_bind,
            FinDist.bind_map, runServicePlan, FinDist.bind_bind]
          apply FinDist.bind_congr
          intro next _
          simpa only [serviceControlFuel] using ih next
      | nil =>
          intro execution
          have fuelEq : runtime.serviceControlFuel roster reactionRounds (epochs + 1) [] =
              runtime.serviceControlFuel roster reactionRounds epochs
                (epochPlan (ServiceOrder.increasing graph) roster reactionRounds) + 1 := by
            simp only [serviceControlFuel, List.length_nil, zero_add, Nat.succ_mul,
              epochPlan_length_eq_epochInstructionCount runtime roster reactionRounds
                (ServiceOrder.increasing graph)]
            omega
          rw [fuelEq]
          simp only [runServiceControlSteps, serviceControlStep, FinDist.map_bind,
            FinDist.bind_map, runServicePlan, FinDist.pure_bind, runService, serviceEpoch,
            FinDist.bind_bind]
          apply FinDist.bind_congr
          intro chosen _
          have chosenLength := runtime.epochPlan_length_eq_epochInstructionCount roster
            reactionRounds chosen
          have canonicalLength := runtime.epochPlan_length_eq_epochInstructionCount roster
            reactionRounds (ServiceOrder.increasing graph)
          have sameFuel : runtime.serviceControlFuel roster reactionRounds epochs
                (epochPlan (ServiceOrder.increasing graph) roster reactionRounds) =
              runtime.serviceControlFuel roster reactionRounds epochs
                (epochPlan chosen roster reactionRounds) := by
            simp only [serviceControlFuel, chosenLength, canonicalLength]
          rw [sameFuel]
          exact outer (epochPlan chosen roster reactionRounds) execution

/-- Evaluating a control with no installed plan is exactly the original
bounded service recursion. -/
theorem evalServiceControl_eq_runServicePlan_bind (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ∀ epochs plan execution,
      runtime.evalServiceControl roster reactionRounds players wire order epochs plan execution =
        (runtime.runServicePlan players wire plan execution).bind
          (runtime.runService roster reactionRounds players wire order epochs) := by
  intro epochs
  induction epochs with
  | zero =>
      intro plan execution
      simp [evalServiceControl, runService]
  | succ epochs ih =>
      intro plan execution
      simp only [evalServiceControl, runService, serviceEpoch, FinDist.bind_bind]
      apply FinDist.bind_congr
      intro boundary _
      apply FinDist.bind_congr
      intro chosen _
      exact ih _ _

/-- At the uniform finite horizon, small-step evaluation and the big-step
control evaluator have exactly the same execution law. -/
theorem runServiceControlSteps_map_execution (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (epochs : Nat) (plan : List (ServiceInstruction graph))
    (execution : runtime.application.PolicyExecution) :
    (runtime.runServiceControlSteps roster reactionRounds players wire order
      (runtime.serviceControlFuel roster reactionRounds epochs plan)
      ⟨epochs, plan, execution⟩).map ServiceControl.execution =
        runtime.evalServiceControl roster reactionRounds players wire order
          epochs plan execution := by
  rw [runtime.runServiceControlSteps_map_execution_eq_bind roster reactionRounds players
    wire order epochs plan execution]
  exact (runtime.evalServiceControl_eq_runServicePlan_bind roster reactionRounds players
    wire order epochs plan execution).symm

/-- Empty-plan specialization of the control evaluation law. -/
theorem evalServiceControl_nil (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (epochs : Nat) (execution : runtime.application.PolicyExecution) :
    runtime.evalServiceControl roster reactionRounds players wire order epochs [] execution =
      runtime.runService roster reactionRounds players wire order epochs execution := by
  simpa only [runServicePlan, FinDist.pure_bind] using
    runtime.evalServiceControl_eq_runServicePlan_bind roster reactionRounds players wire order
      epochs [] execution

/-- The serviced event game is the setup law followed by evaluation of the
initial empty control. -/
theorem servicedEventGame_eq_evalServiceControl (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (players : Player → runtime.application.PlayerPolicy) :
    (runtime.servicedEventGame inputs roster reactionRounds wire order).play players =
      inputs.bind fun input =>
        runtime.evalServiceControl roster reactionRounds players wire order
          runtime.serviceEpochs []
          (MessageApplication.PolicyExecution.initial runtime.application
            (MessageApplication.State.initial runtime.application (State.initial input))) := by
  unfold servicedEventGame
  apply FinDist.bind_congr
  intro input _
  exact (runtime.evalServiceControl_nil roster reactionRounds players wire order
    runtime.serviceEpochs _).symm

end Vegas.EventGraphRuntime
