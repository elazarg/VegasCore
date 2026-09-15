/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessagePolicies
import Interaction.MessageApplicationImmediateService
import Interaction.MessageApplicationWirePolicy

/-! # Reserved inclusion with adaptive pending-message delivery

The service expands each graph phase into calls to the shared message runner.
Its owner receives preparation and submission opportunities, followed by
adaptive wire delivery and player reactions, a reserved inclusion opportunity,
and enough ideal progress ticks to expire that phase. Ticks reserved for a
completed phase wait instead of expiring a later phase prematurely.

The wire policy retains the complete public pool and environment history. It
can deliver, include, or wait at every wire slot. Player reaction commands are
unrestricted. This is a concrete bounded service realization, not a theorem
about every fair scheduler or about automatic blockchain execution.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- A service plan chooses invocation opportunities, not player commands. -/
inductive ServiceInstruction (Player : Type) where
  | player (who : Player)
  | wire
  | includeLatest (who : Player)
  | expire (phase : Nat)

namespace ServiceInstruction

def invocation : ServiceInstruction Player → @MessageApplication.Invocation Player
  | .player who => .player who
  | .wire | .includeLatest _ | .expire _ => .environment

/-- Player calls do not consume an environment-policy history entry. -/
def environmentSlot : ServiceInstruction Player → Option (ServiceInstruction Player)
  | .player _ => none
  | instruction => some instruction

end ServiceInstruction

/-- A wire choice followed by observation-local reactions from a finite roster. -/
def reactionRound (roster : List Player) : List (ServiceInstruction Player) :=
  .wire :: roster.map .player

/-- The plan follows the complete graph, including chance and initial-field
resolutions. It does not inspect payloads, guards, or a satisfying assignment. -/
def servicePlan (runtime : GraphRuntime Player L Δ) (roster : List Player)
    (reactionRounds : Nat) : {Γ : VCtx Player L} → Graph Player L Γ Δ → Nat →
      List (ServiceInstruction Player)
  | _, .ret _, _ => []
  | _, .sample _ _ _ next, phase =>
      .expire phase :: servicePlan runtime roster reactionRounds next (phase + 1)
  | _, .bind _ owner _ next, phase =>
      [.player owner, .player owner] ++
        (List.replicate reactionRounds (reactionRound roster)).flatten ++
        [.includeLatest owner] ++ List.replicate (max 1 (runtime.deadline phase)) (.expire phase) ++
        servicePlan runtime roster reactionRounds next (phase + 1)
  | _, .resolve _ owner _ _ _ _ next, phase =>
      [.player owner, .player owner] ++
        (List.replicate reactionRounds (reactionRound roster)).flatten ++
        [.includeLatest owner] ++ List.replicate (max 1 (runtime.deadline phase)) (.expire phase) ++
        servicePlan runtime roster reactionRounds next (phase + 1)

/-- Reserved commands are determined from public state. Unreserved wire choices
retain the supplied policy's actual observation and environment history. -/
def serviceEnvironment (runtime : GraphRuntime Player L Δ)
    (plan : List (ServiceInstruction Player)) (wire : runtime.application.WirePolicy) :
    runtime.application.EnvironmentPolicy := fun history view =>
  match (plan.filterMap ServiceInstruction.environmentSlot)[history.length]? with
  | some .wire => runtime.application.wireEnvironment wire history view
  | some (.includeLatest who) =>
      FinDist.pure (runtime.application.latestSubmissionCommand who view)
  | some (.expire phase) =>
      FinDist.pure (if view.application.pc = phase then .application .tick else .wait)
  | _ => FinDist.pure .wait

/-- The native policy game uses the existing runner and admits every player
policy in that runner. Service restricts the environment, not the deviator. -/
def servicedGame (runtime : GraphRuntime Player L Δ) (graph : Graph Player L Γ Δ)
    (inputs : FinDist (VEnv L Γ)) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) : GameForm Player where
  sig := MessageApplication.policySignature Player runtime.application
  play players :=
    let plan := runtime.servicePlan roster reactionRounds graph 0
    inputs.bind fun input =>
      runtime.application.runPolicies players (runtime.serviceEnvironment plan wire)
        (plan.map ServiceInstruction.invocation)
        (MessageApplication.PolicyExecution.initial _
          (MessageApplication.State.initial _ (State.initial graph input)))

theorem serviceEnvironment_wire (runtime : GraphRuntime Player L Δ)
    (plan : List (ServiceInstruction Player)) (wire : runtime.application.WirePolicy)
    (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation)
    (slot : (plan.filterMap ServiceInstruction.environmentSlot)[history.length]? = some .wire) :
    runtime.serviceEnvironment plan wire history view =
      runtime.application.wireEnvironment wire history view := by
  simp [serviceEnvironment, slot]

theorem serviceEnvironment_expire (runtime : GraphRuntime Player L Δ)
    (plan : List (ServiceInstruction Player)) (wire : runtime.application.WirePolicy)
    (history : List runtime.application.EnvironmentEntry)
    (view : runtime.application.EnvironmentObservation) (phase : Nat)
    (slot : (plan.filterMap ServiceInstruction.environmentSlot)[history.length]? =
      some (.expire phase)) :
    runtime.serviceEnvironment plan wire history view =
      FinDist.pure (if view.application.pc = phase then .application .tick else .wait) := by
  simp [serviceEnvironment, slot]

end Vegas.GraphRuntime
