/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventServiceProtocol
import Interaction.MessageApplicationResponse
import GameTheory.Protocol.Information

/-! # Multiplayer service with atomic player responses

The actual players choose responses from their own invocation arguments. Setup,
wire behavior, and adaptive order selection belong to the transition kernel.
A response performs finite private work and one network command. Only that
response is atomic: later wire slots still permit delivery, inclusion, and
roster reactions before the reserved inclusion opportunity.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Setup has no active player. After setup, the state retains the complete
native execution and the unconsumed service suffix. -/
abbrev ResponseProtocolState (runtime : EventGraphRuntime graph) := Option (ServiceControl runtime)

def responseActor (runtime : EventGraphRuntime graph) :
    ResponseProtocolState runtime → Option Player
  | some ⟨_, .player who :: _, _⟩ => some who
  | _ => none

/-- Exactly the arguments supplied to a native response policy. An inactive
information state is a placeholder; it supplies no strategic choice. -/
abbrev ResponseInfo (runtime : EventGraphRuntime graph) :=
  Option (List runtime.application.PlayerEntry × runtime.application.View)

def responseObserve (runtime : EventGraphRuntime graph) (who : Player)
    (state : ResponseProtocolState runtime) : ResponseInfo runtime :=
  match state with
  | none => none
  | some control =>
      if runtime.responseActor state = some who then
        some (control.execution.principalHistory who,
          MessageApplication.State.observe runtime.application control.execution.native who)
      else none

def responseTerminal (runtime : EventGraphRuntime graph) : ResponseProtocolState runtime → Prop
  | none => False
  | some control => control.Terminal runtime

def idleResponse (runtime : EventGraphRuntime graph) : runtime.application.PlayerResponse :=
  ⟨[], .wait⟩

/-- Environment instructions are delegated to the existing service transition.
The fallback player policy is unused: every player instruction takes the first
branch and executes the selected atomic response. -/
def responseInstructionStep (runtime : EventGraphRuntime graph)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (execution : runtime.application.PolicyExecution)
    (joint : Player → Option runtime.application.PlayerResponse) :
    FinDist runtime.application.PolicyExecution :=
  match instruction with
  | .player who => runtime.application.responseStep who execution
      ((joint who).getD runtime.idleResponse)
  | _ => runtime.serviceStep (fun _ _ _ => FinDist.pure .wait) wire instruction execution

def responseTransition (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ResponseProtocolState runtime → (Player → Option runtime.application.PlayerResponse) →
      FinDist (ResponseProtocolState runtime)
  | none, _ => inputs.map fun input => some
      { epochs := runtime.serviceEpochs
        plan := []
        execution := MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application (State.initial input)) }
  | some control, joint => match control.plan with
    | instruction :: rest =>
        (runtime.responseInstructionStep wire instruction control.execution joint).map
          fun execution => some { control with plan := rest, execution := execution }
    | [] => match control.epochs with
      | 0 => FinDist.pure (some control)
      | epochs + 1 =>
          (order control.execution.environmentHistory
            (MessageApplication.State.environmentView runtime.application
              control.execution.native)).map fun chosen => some
                { epochs := epochs
                  plan := epochPlan chosen roster reactionRounds
                  execution := control.execution }

/-- Only native player responses are strategic coordinates. Service policies
are fixed parameters, evaluated on their original public observations. -/
def responseProtocol (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ExecutionProtocol Player where
  State := ResponseProtocolState runtime
  Action _ := runtime.application.PlayerResponse
  init := none
  active state who := runtime.responseActor state = some who
  available _ _ := Set.univ
  terminal := runtime.responseTerminal
  step state joint :=
    runtime.responseTransition inputs roster reactionRounds wire order state joint.1
  progress state _ := by
    refine ⟨fun who => if runtime.responseActor state = some who then
      some runtime.idleResponse else none, ?_⟩
    intro who
    by_cases acts : runtime.responseActor state = some who <;> simp [acts]

theorem response_singleMover (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (state : ResponseProtocolState runtime) {first second : Player}
    (firstActs : (runtime.responseProtocol inputs roster reactionRounds wire order).active
      state first)
    (secondActs : (runtime.responseProtocol inputs roster reactionRounds wire order).active
      state second) : first = second :=
  Option.some.inj (firstActs.symm.trans secondActs)

theorem responseObserve_isSome (runtime : EventGraphRuntime graph) (who : Player)
    (state : ResponseProtocolState runtime) :
    (runtime.responseObserve who state).isSome ↔ runtime.responseActor state = some who := by
  cases state with
  | none => simp [responseObserve, responseActor]
  | some control =>
      by_cases acts : runtime.responseActor (some control) = some who <;>
        simp [responseObserve, acts]

def responseSignals (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    InfoSignals (runtime.responseProtocol inputs roster reactionRounds wire order) where
  PublicSignal := Unit
  PrivateSignal _ := ResponseInfo runtime
  initialPublic := ()
  initialPrivate _ := none
  publicSignal _ := ()
  privateSignal who event := runtime.responseObserve who event.target
  InfoState _ := ResponseInfo runtime
  initInfo _ view _ := view
  pushInfo _ _ _ view _ := view

theorem response_info (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) (who : Player) :
    ∀ {state}
      (trace : (runtime.responseProtocol inputs roster reactionRounds wire order).Trace state),
      (runtime.responseSignals inputs roster reactionRounds wire order).infoOf who trace =
        runtime.responseObserve who state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def responseInformation (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    InformationModel (runtime.responseProtocol inputs roster reactionRounds wire order) where
  toInfoSignals := runtime.responseSignals inputs roster reactionRounds wire order
  menu _ info := {choice | choice.isSome = info.isSome}
  menu_adequate := by
    intro who state trace choice
    rw [runtime.response_info inputs roster reactionRounds wire order who trace]
    have active := runtime.responseObserve_isSome who state
    cases observed : runtime.responseObserve who state <;> cases choice <;>
      simp_all [LegalOption, responseProtocol]

end Vegas.EventGraphRuntime
