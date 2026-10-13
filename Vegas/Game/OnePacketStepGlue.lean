/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketOperationalFactors

/-! # Response steps of the one-packet game

A step of the one-packet game from a state where a player is activated is that
player's response (`Vegas.onePacket_response_step`): its legal choice is a
response the one-packet menu offers at its recall and view, the next execution
is the response applied, and the player's information is its recall and view.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **A response step.** A step of the one-packet game from a state where a
player is activated is its response: the legal choice is a response the
one-packet menu offers at its recall and view, the next execution is that
response applied, and the player's information is its recall and view. -/
theorem onePacket_response_step {before after : (application setup leaks).ProtocolState}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace before)
    (joint : Player → Option (application setup leaks).Action)
    (legal : (onePacketProtocol setup leaks bounds horizon scheduler).Legal before joint)
    (realized : after ∈ ((onePacketProtocol setup leaks bounds horizon scheduler).step before
      ⟨joint, legal⟩).support) (control next : (application setup leaks).Control)
    (initialized : before = some control) (reached : after = some next) {actor : Player}
    (acting : control.actor = some actor) :
    ∃ response, joint actor = some response ∧
      response ∈ bounds.onePacketActions (runtime setup) leaks actor
        (control.execution.recall actor)
        (control.execution.observe (application setup leaks) actor) ∧
      next.execution = control.execution.respond (application setup leaks) actor response ∧
      (onePacketInformation setup leaks bounds horizon scheduler).infoOf actor prior =
        some (control.execution.recall actor,
          control.execution.observe (application setup leaks) actor) := by
  subst initialized reached
  have localLegal := legal.2 actor
  cases chosen : joint actor with
  | none =>
      rw [chosen] at localLegal
      exact (localLegal acting).elim
  | some response =>
      rw [chosen] at localLegal
      refine ⟨response, rfl, localLegal.2, ?_, ?_⟩
      · change some next ∈ ((application setup leaks).transition (initialLaw setup) horizon
          scheduler (some control) joint).support at realized
        rw [transition_respond control acting joint] at realized
        have same := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp realized)
        rw [same, chosen]
        rfl
      · change ((bounds.onePacketMenu (runtime setup) leaks).signals (initialLaw setup) horizon
          scheduler).infoOf actor prior = _
        rw [ReactiveApplication.ResponseMenu.info]
        change (if control.actor = some actor then some _ else none) = _
        rw [ite_eq_left acting]

end Vegas
