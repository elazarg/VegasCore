/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceDecidedCompletion

/-! # Ready sites and the initialized source law

A decision on the sequentialized graph is located by its ready site: the event
whose phase it lies in, that event's readiness, and that it is the only ready
event (`Vegas.ReadySite`). No plan position, roster or calendar is involved.

The source continuation from the initial boundary, averaged over the native
prior, is the source law (`Vegas.initialLaw_bind_sourceContinuation`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The position-free datum of a decision: the event whose phase the execution
is in, that event's readiness, and that it is the only ready event. -/
structure ReadySite (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (execution : (application setup (Vegas.runtime setup) leaks).Execution) where
  event : (graph setup).EventId
  ready : execution.application.config.cut.Ready event
  sole : execution.application.publicView.SoleReady event

/-! ## The initialized law -/

section Initialized

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The source continuation from the initial boundary, averaged over the
native prior, is the source law. -/
theorem initialLaw_bind_sourceContinuation (profile : BehavioralProfile setup.program) :
    (initialLaw setup).bind (fun state => sourceContinuation setup profile 0 state.config) =
      (setup.run profile).map some := by
  rw [initialLaw, serviceInitialLaw, PMF.bind_map, Setup.run, PMF.map_bind]
  congr 1
  funext initial
  simp only [Function.comp_apply, sourceContinuation, serviceSourcePrefix?_initial,
    Setup.continuationLaw, ProtocolState.continuationLaw_entry]
  rfl

variable {setup leaks} [Fintype Player]

end Initialized

end Vegas
