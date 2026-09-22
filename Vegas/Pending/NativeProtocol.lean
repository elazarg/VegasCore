/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventServiceProtocol
import Vegas.Pending.EventPlayerAction
import GameTheory.Protocol.Information

/-! # Native service as a multiplayer game

The actual players choose actions from their own invocation arguments. Setup,
wire behavior, and adaptive order selection belong to the transition kernel.
One action records private memory and optionally transmits a packet. Wire
slots permit delivery, inclusion, and reactions before reserved inclusion.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

structure NativeControl (runtime : EventGraphRuntime graph) where
  epochs : Nat
  plan : List (ServiceInstruction graph)
  execution : NativeExecution runtime

def NativeControl.Terminal (runtime : EventGraphRuntime graph)
    (control : NativeControl runtime) : Prop := control.epochs = 0 ∧ control.plan = []

/-- Setup has no active player. After setup, the state retains the complete
native execution and the unconsumed service suffix. -/
abbrev NativeProtocolState (runtime : EventGraphRuntime graph) := Option (NativeControl runtime)

def nativeActor (runtime : EventGraphRuntime graph) :
    NativeProtocolState runtime → Option Player
  | some ⟨_, .player who :: _, _⟩ => some who
  | _ => none

/-- Exactly the arguments supplied to a player policy. An inactive
information state is a placeholder; it supplies no strategic choice. -/
abbrev NativeInfo (graph : Vegas.EventGraph Player L) :=
  Option (List (NativeEntry graph) × NativeView graph)

def nativeObserve (runtime : EventGraphRuntime graph) (who : Player)
    (state : NativeProtocolState runtime) : NativeInfo graph :=
  match state with
  | none => none
  | some control =>
      if runtime.nativeActor state = some who then
        some (control.execution.principalHistory who,
          runtime.nativeView control.execution.native who)
      else none

def nativeTerminal (runtime : EventGraphRuntime graph) : NativeProtocolState runtime → Prop
  | none => False
  | some control => control.Terminal runtime

/-- Environment instructions are delegated to the existing service transition.
The fallback player policy is unused: every player instruction takes the first
branch and executes the selected action. -/
def nativeInstructionStep (runtime : EventGraphRuntime graph)
    (wire : runtime.application.WirePolicy) (instruction : ServiceInstruction graph)
    (execution : NativeExecution runtime)
    (joint : Player → Option (PlayerAction graph)) :
    FinDist (NativeExecution runtime) :=
  match instruction with
  | .player who => runtime.actionStep who execution
      ((joint who).getD PlayerAction.wait)
  | _ => (runtime.serviceStep (fun _ _ _ => FinDist.pure .wait) wire instruction
      (execution.environmentExecution runtime)).map fun next =>
        { execution with native := next.native, environmentHistory := next.environmentHistory }

def nativeTransition (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    NativeProtocolState runtime → (Player → Option (PlayerAction graph)) →
      FinDist (NativeProtocolState runtime)
  | none, _ => inputs.map fun input => some
      { epochs := runtime.serviceEpochs
        plan := []
        execution := NativeExecution.initial runtime
          (MessageApplication.State.initial runtime.application (State.initial input)) }
  | some control, joint => match control.plan with
    | instruction :: rest =>
        (runtime.nativeInstructionStep wire instruction control.execution joint).map
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

/-- Only player actions are strategic coordinates. Service policies
are fixed parameters, evaluated on their original public observations. -/
def nativeProtocol (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ExecutionProtocol Player where
  State := NativeProtocolState runtime
  Action _ := PlayerAction graph
  init := none
  active state who := runtime.nativeActor state = some who
  available _ _ := Set.univ
  terminal := runtime.nativeTerminal
  step state joint :=
    runtime.nativeTransition inputs roster reactionRounds wire order state joint.1
  progress state _ := by
    refine ⟨fun who => if runtime.nativeActor state = some who then
      some PlayerAction.wait else none, ?_⟩
    intro who
    by_cases acts : runtime.nativeActor state = some who <;> simp [acts]

theorem native_singleMover (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (state : NativeProtocolState runtime) {first second : Player}
    (firstActs : (runtime.nativeProtocol inputs roster reactionRounds wire order).active
      state first)
    (secondActs : (runtime.nativeProtocol inputs roster reactionRounds wire order).active
      state second) : first = second :=
  Option.some.inj (firstActs.symm.trans secondActs)

theorem nativeObserve_isSome (runtime : EventGraphRuntime graph) (who : Player)
    (state : NativeProtocolState runtime) :
    (runtime.nativeObserve who state).isSome ↔ runtime.nativeActor state = some who := by
  cases state with
  | none => simp [nativeObserve, nativeActor]
  | some control =>
      by_cases acts : runtime.nativeActor (some control) = some who <;>
        simp [nativeObserve, acts]

def nativeSignals (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    InfoSignals (runtime.nativeProtocol inputs roster reactionRounds wire order) where
  PublicSignal := Unit
  PrivateSignal _ := NativeInfo graph
  initialPublic := ()
  initialPrivate _ := none
  publicSignal _ := ()
  privateSignal who event := runtime.nativeObserve who event.target
  InfoState _ := NativeInfo graph
  initInfo _ view _ := view
  pushInfo _ _ _ view _ := view

theorem native_info (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) (who : Player) :
    ∀ {state}
      (trace : (runtime.nativeProtocol inputs roster reactionRounds wire order).Trace state),
      (runtime.nativeSignals inputs roster reactionRounds wire order).infoOf who trace =
        runtime.nativeObserve who state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def nativeInformation (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    InformationModel (runtime.nativeProtocol inputs roster reactionRounds wire order) where
  toInfoSignals := runtime.nativeSignals inputs roster reactionRounds wire order
  menu _ info := {choice | choice.isSome = info.isSome}
  menu_adequate := by
    intro who state trace choice
    rw [runtime.native_info inputs roster reactionRounds wire order who trace]
    have active := runtime.nativeObserve_isSome who state
    cases observed : runtime.nativeObserve who state <;> cases choice <;>
      simp_all [LegalOption, nativeProtocol]

end Vegas.EventGraphRuntime
