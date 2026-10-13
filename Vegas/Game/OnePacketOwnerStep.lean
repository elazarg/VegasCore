/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLumpingInstance

/-! # The owner's step of the one-packet game at a pending publication

A response changes the operational state only through the envelope it emits:
the actor clears, the envelope joins the network, and the responder's recall
gains its current operational view with the envelope
(`Vegas.operationalState_respond`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The envelope a response emits. -/
def emittedEnvelope (execution : (application setup leaks).Execution) (who : Player)
    (action : (application setup leaks).Action) :
    Option (Message Player (application setup leaks).Payload) :=
  match action.transmission with
  | none => none
  | some submission => some ⟨(who, execution.network.nextSerial who),
      (application setup leaks).packet
        ((application setup leaks).submit execution.application who submission) who
        (execution.network.known who) submission⟩

/-- A response on the operational state: the actor clears, the emitted envelope
joins the network, and the responder's recall gains its current operational
view with the envelope. -/
def OperationalState.respond (responder : Player)
    (emitted : Option (Message Player (application setup leaks).Payload))
    (state : OperationalState setup leaks) : OperationalState setup leaks :=
  { state with
    actor := none
    environment := { state.environment with
      network := match emitted with
        | none => state.environment.network
        | some envelope => (state.network.submit responder envelope.payload).2.publicView }
    keys := fun who => if who = responder then (state.keys who).map fun key =>
      { key with recalled := key.recalled ++ [(key.current, emitted)] } else state.keys who }

/-- A response leaves every player's operational view and delivered value
unchanged. -/
theorem respond_observe_operational (execution : (application setup leaks).Execution)
    (responder : Player) (action : (application setup leaks).Action) (who : Player) :
    operationalView setup leaks ((execution.respond (application setup leaks) responder
        action).observe (application setup leaks) who) =
      operationalView setup leaks (execution.observe (application setup leaks) who) ∧
    deliveredValue setup leaks who ((execution.respond (application setup leaks) responder
        action).observe (application setup leaks) who) =
      deliveredValue setup leaks who (execution.observe (application setup leaks) who) := by
  have contract := (runtime setup).reactive_respond_application leaks execution responder action
  constructor
  · change ((execution.respond (application setup leaks) responder action).application.publicView,
        (execution.respond (application setup leaks) responder action).network.observe who,
        (execution.respond (application setup leaks) responder action).receipts) =
      (execution.application.publicView, execution.network.observe who, execution.receipts)
    rw [contract.2]
    rcases action with ⟨_ | _⟩ <;> rfl
  · apply deliveredValue_congr
    · change (execution.respond (application setup leaks) responder
        action).application.publicView.ownTurn? who = execution.application.publicView.ownTurn? who
      rw [contract.2]
    · change ((graph setup).playerObserve who
          (execution.respond (application setup leaks) responder action).application.config).store =
        ((graph setup).playerObserve who execution.application.config).store
      rw [contract.1]

/-- **A response on the operational state.** -/
theorem operationalState_respond (control : (application setup leaks).Control)
    (responder : Player) (action : (application setup leaks).Action) :
    operationalState setup leaks (some { control with
      actor := none
      execution := control.execution.respond (application setup leaks) responder action }) =
      (operationalState setup leaks (some control)).map
        (OperationalState.respond responder
          (emittedEnvelope control.execution responder action)) := by
  have contract := (runtime setup).reactive_respond_application leaks control.execution
    responder action
  rcases control with ⟨remaining, actor, execution⟩
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      simp only [operationalState, Option.map_some, OperationalState.respond, emittedEnvelope,
        Option.some.injEq, OperationalState.mk.injEq]
      refine ⟨trivial, trivial, rfl, rfl, rfl, ?_⟩
      funext who
      by_cases same : who = responder
      · subst same
        simp only [↓reduceIte, Option.map_some, lateKey, ReactiveApplication.Execution.respond,
          List.map_append, List.map_cons, List.map_nil]
        rfl
      · simp only [same, ↓reduceIte]
        rw [(application setup leaks).respond_recall_other execution responder who same]
        rfl
  | some submission =>
      simp only [operationalState, Option.map_some, OperationalState.respond, emittedEnvelope,
        Option.some.injEq, OperationalState.mk.injEq]
      refine ⟨trivial, trivial, rfl, ?_, rfl, ?_⟩
      · unfold ReactiveApplication.Execution.observeEnvironment
        congr 1
        exact contract.2
      · funext who
        obtain ⟨current, delivered⟩ := respond_observe_operational execution responder
          ⟨some submission⟩ who
        by_cases same : who = responder
        · subst same
          simp only [↓reduceIte, Option.map_some, lateKey, Option.some.injEq, LateKey.mk.injEq]
          refine ⟨trivial, current, ?_, delivered⟩
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.map_append,
            List.map_cons, List.map_nil]
          rfl
        · simp only [same, ↓reduceIte, lateKey, Option.some.injEq, LateKey.mk.injEq]
          rw [(application setup leaks).respond_recall_other execution responder who same]
          exact ⟨trivial, current, rfl, delivered⟩

end Vegas
