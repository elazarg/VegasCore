/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventSubmission
import Interaction.MessageApplicationWirePolicy

/-! # Bounded public service for dependency-driven pending messages

Each epoch visits every event in a permutation chosen from the full public
environment observation. A public grant identifies the event receiving reserved
service; it does not constrain player commands or wire inclusion. All grants
precede the epoch's one clock advance and expiry sweep. Player policies and the
wire policy use the shared message runner and retain their actual histories.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- One complete event sweep; its order need not be topological. Readiness is
checked by the application, so visiting an unavailable event simply waits. -/
def ServiceOrder (graph : Vegas.EventGraph Player L) :=
  { events : List graph.EventId // events.Perm (List.finRange graph.order.eventCount) }

namespace ServiceOrder

def increasing (graph : Vegas.EventGraph Player L) : ServiceOrder graph :=
  ⟨List.finRange graph.order.eventCount, List.Perm.refl _⟩

def decreasing (graph : Vegas.EventGraph Player L) : ServiceOrder graph :=
  ⟨(List.finRange graph.order.eventCount).reverse, List.reverse_perm _⟩

omit [DecidableEq Player] in
theorem mem (order : ServiceOrder graph) (event : graph.EventId) : event ∈ order.val :=
  order.property.mem_iff.mpr (List.mem_finRange event)

end ServiceOrder

/-- Order choices may depend on the entire public pool, receipts, application
projection, and environment history. They cannot inspect hidden meanings. -/
abbrev ServiceOrderPolicy (runtime : EventGraphRuntime graph) :=
  List runtime.application.EnvironmentEntry → runtime.application.EnvironmentObservation →
    FinDist (ServiceOrder graph)

/-- A service instruction reserves an opportunity, never a player command. -/
inductive ServiceInstruction (graph : Vegas.EventGraph Player L) where
  | player (who : Player)
  | wire
  | grant (event : graph.EventId)
  | includeLatest (event : graph.EventId) (owner : Player)
  | sample (event : graph.EventId)
  | tick
  | expire (event : graph.EventId)

/-- Only a clock instruction advances the clock. -/
def ServiceInstruction.ticks : ServiceInstruction graph → Nat
  | .tick => 1
  | _ => 0

def serviceTicks (plan : List (ServiceInstruction graph)) : Nat :=
  (plan.map ServiceInstruction.ticks).sum

omit [DecidableEq Player] in
@[simp] theorem serviceTicks_nil : serviceTicks ([] : List (ServiceInstruction graph)) = 0 :=
  rfl

omit [DecidableEq Player] in
@[simp] theorem serviceTicks_cons (instruction : ServiceInstruction graph)
    (rest : List (ServiceInstruction graph)) :
    serviceTicks (instruction :: rest) = instruction.ticks + serviceTicks rest := rfl

omit [DecidableEq Player] in
theorem serviceTicks_append (first second : List (ServiceInstruction graph)) :
    serviceTicks (first ++ second) = serviceTicks first + serviceTicks second := by
  simp [serviceTicks, List.sum_append]

/-- Interpret one service instruction through the existing policy transitions. -/
def serviceStep (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy)
    (instruction : ServiceInstruction graph)
    (execution : runtime.application.PolicyExecution) :
    FinDist runtime.application.PolicyExecution :=
  match instruction with
  | .player who => runtime.application.invoke players
      (runtime.application.wireEnvironment wire) execution (.player who)
  | .wire => runtime.application.invoke players
      (runtime.application.wireEnvironment wire) execution .environment
  | .grant event => runtime.application.environmentPolicyStep execution
      (.application (.grant event))
  | .includeLatest event owner => runtime.application.environmentPolicyStep execution
      (runtime.latestEventSubmissionCommand event owner
        (MessageApplication.State.environmentView runtime.application execution.native))
  | .sample event => runtime.application.environmentPolicyStep execution
      (.application (.executeSample event))
  | .tick => runtime.application.environmentPolicyStep execution (.application .advanceClock)
  | .expire event => runtime.application.environmentPolicyStep execution
      (.application (.expire event))

/-- Sequence concrete service opportunities without projecting away histories,
packets, receipts, private commands, or native chance. -/
def runServicePlan (runtime : EventGraphRuntime graph)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) :
    List (ServiceInstruction graph) → runtime.application.PolicyExecution →
      FinDist runtime.application.PolicyExecution
  | [], execution => FinDist.pure execution
  | instruction :: rest, execution =>
      (runtime.serviceStep players wire instruction execution).bind
        (runtime.runServicePlan players wire rest)

/-- Three owner calls accommodate remembering, preparing, and submitting a
binding; shorter actions may wait. Every wire slot permits roster reactions. -/
def eventServicePlan (roster : List Player) (reactionRounds : Nat)
    (event : graph.EventId) : List (ServiceInstruction graph) :=
  [.grant event] ++
    (match graph.actor? event with
    | none => []
    | some owner => List.replicate 3 (.player owner) ++
        (List.replicate reactionRounds (.wire :: roster.map .player)).flatten ++
        [.includeLatest event owner]) ++
    [.sample event]

/-- One clock-free service sweep, then one clock increment and all local
expiry checks. The expiry checks do not increment the clock. -/
def epochPlan (order : ServiceOrder graph) (roster : List Player)
    (reactionRounds : Nat) : List (ServiceInstruction graph) :=
  (order.val.flatMap (eventServicePlan roster reactionRounds)) ++ [.tick] ++
    (List.finRange graph.order.eventCount).map .expire

omit [DecidableEq Player] in
theorem eventServicePlan_ticks (roster : List Player) (reactionRounds : Nat)
    (event : graph.EventId) : serviceTicks (eventServicePlan roster reactionRounds event) = 0 := by
  simp only [eventServicePlan, serviceTicks_append]
  cases graph.actor? event <;>
    simp [serviceTicks, ServiceInstruction.ticks, List.map_flatten, List.sum_flatten,
      Function.comp_def]

omit [DecidableEq Player] in
theorem epochPlan_ticks (order : ServiceOrder graph) (roster : List Player)
    (reactionRounds : Nat) : serviceTicks (epochPlan order roster reactionRounds) = 1 := by
  have sweep : ∀ events : List graph.EventId,
      serviceTicks (events.flatMap (eventServicePlan roster reactionRounds)) = 0 := by
    intro events
    induction events with
    | nil => rfl
    | cons event rest ih =>
        simp [List.flatMap_cons, serviceTicks_append, eventServicePlan_ticks, ih]
  simp only [epochPlan, serviceTicks_append, sweep]
  simp [serviceTicks, ServiceInstruction.ticks, Function.comp_def]

def serviceEpoch (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (execution : runtime.application.PolicyExecution) :
    FinDist runtime.application.PolicyExecution :=
  (order execution.environmentHistory
    (MessageApplication.State.environmentView runtime.application execution.native)).bind
      fun chosen => runtime.runServicePlan players wire
        (epochPlan chosen roster reactionRounds) execution

/-- The finite driver samples a fresh public order at each epoch boundary.
Only the environment is restricted; all native player policies remain legal. -/
def runService (runtime : EventGraphRuntime graph)
    (roster : List Player) (reactionRounds : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    Nat → runtime.application.PolicyExecution → FinDist runtime.application.PolicyExecution
  | 0, execution => FinDist.pure execution
  | count + 1, execution =>
      (runtime.serviceEpoch roster reactionRounds players wire order execution).bind
        (runtime.runService roster reactionRounds players wire order count)

/-- Arithmetic service configuration for later honest-protection laws. An
event enabled mid-epoch has the following epoch available before expiry. -/
def ServiceFeasible (runtime : EventGraphRuntime graph) : Prop :=
  ∀ event, 2 ≤ runtime.deadline event

/-- Uniform upper bound on all local deadline lengths. -/
def maxDeadline (runtime : EventGraphRuntime graph) : Nat :=
  Finset.univ.sup runtime.deadline

/-- At most one full deadline window per graph event is needed for completion. -/
def serviceEpochs (runtime : EventGraphRuntime graph) : Nat :=
  graph.order.eventCount * (runtime.maxDeadline + 1)

/-- The concrete native game, including public adaptive service ordering. -/
def servicedEventGame (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    GameForm Player where
  sig := MessageApplication.policySignature Player runtime.application
  play players := inputs.bind fun input =>
    runtime.runService roster reactionRounds players wire order runtime.serviceEpochs
      (MessageApplication.PolicyExecution.initial _
        (MessageApplication.State.initial _ (State.initial input)))

end Vegas.EventGraphRuntime
