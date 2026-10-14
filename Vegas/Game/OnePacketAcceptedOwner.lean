/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketSwapGuardSite

/-! # Accepted handles belong to the owner of their binding

Every handle the default runtime accepts at a field belongs to the owner of that
field's binding (`Vegas.accepted_owner_of_trace`). Initially only binding inputs
accept their initial handles; a commitment is accepted only from the owner of the
binding event it fills; every other operation leaves the table unchanged
(`Vegas.acceptedOwned_invariant`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

omit [Fintype Player] in
variable (setup leaks) in
/-- **Accepted handles are owned** by the owner of their field's binding, at
every state of the default runtime. -/
theorem acceptedOwned_invariant :
    (application setup leaks).Invariant (fun state => ∀ field handle,
      state.accepted field = some handle →
        ∃ payload, (graph setup).layout field = .binding handle.1 payload) where
  submit state who material held field handle accepted := by
    change (submitStep (material.call.register state who) who
      material.call.packet).accepted field = _ at accepted
    rw [submitStep_accepted, Submission.register_accepted] at accepted
    exact held field handle accepted
  handle state message next held handled field handle accepted := by
    have call := reactiveHandle_call handled
    cases packet : message.payload.call with
    | malformed raw =>
        rw [packet] at call
        simp [EventGraphRuntime.handle] at call
    | opening named other raw =>
        rw [packet] at call
        have tables := handle_resolution_tables (runtime setup) state next _
          (fun _ _ same => by cases same) call
        rw [tables.1] at accepted
        exact held field handle accepted
    | commitment named other =>
        rw [packet] at call
        obtain ⟨_, _, owner, payload, outputEq, _, _, _, candidateOwner, _, _⟩ :=
          handle_commitment_conditions (runtime setup) state next message.id named other call
        rw [(handle_commitment_tables (runtime setup) state next message.id named other
          call).2.1] at accepted
        by_cases same : field = .inr named
        · subst same
          rw [Function.update_self] at accepted
          cases accepted
          exact ⟨payload, candidateOwner ▸ outputEq⟩
        · rw [Function.update_of_ne same] at accepted
          exact held field handle accepted
  environment state command next held reached field handle accepted := by
    rw [(environmentStep_tables (runtime setup) state next command reached).1] at accepted
    exact held field handle accepted

/-- **Every accepted handle belongs to the owner** of its field's binding, along
every history of the one-packet game. -/
theorem accepted_owner_of_trace {bounds : MessageBounds (graph setup)} {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    {field : (graph setup).Field} {handle : Handle (graph setup)}
    (accepted : control.execution.application.accepted field = some handle) :
    ∃ payload, (graph setup).layout field = .binding handle.1 payload := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  refine (acceptedOwned_invariant setup leaks).history (initialLaw setup) horizon scheduler
    (fun state member => ?_) rawTrace field handle accepted
  rw [initialLaw, serviceInitialLaw, PMF.support_map] at member
  obtain ⟨_, _, rfl⟩ := member
  intro field handle initialAccepted
  obtain ⟨input, owner, payload, rfl, layoutEq, rfl⟩ :=
    State.initial_accepted_eq_some _ field handle initialAccepted
  exact ⟨payload, layoutEq⟩

end Vegas
