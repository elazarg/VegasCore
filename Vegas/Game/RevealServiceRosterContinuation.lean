/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealServicePayoffs
import Vegas.Compile.EventGraphReadoutComplete

/-! # Source continuations after completed roster phases

The existing public checkpoint locates the source protocol state inside the
original program. Executing the remaining actual roster blocks has its exact
source continuation law. Actual response counts and published-message invariants
are retained; there is no reset of private recall or passive observations.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
/-- The compiler's terminal context contains every event output. Consequently
the explicit terminal-cut guard is redundant with successful typed decoding,
even at an arbitrary structurally valid native control state, in every
dependency mode. -/
theorem serviceSourceReadout_eq_decode (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (control : (serviceApplication setup mode deadline leaks).Control) :
    serviceSourceReadout setup mode deadline leaks (some control) =
      decodeState? (terminalRefs setup.program) control.execution.application.config.store := by
  unfold serviceSourceReadout
  rw [Option.bind_some]
  cases decoded : decodeState? (terminalRefs setup.program)
      control.execution.application.config.store with
  | none => simp only [decoded, ite_self]
  | some source =>
      have complete := terminal_decode_complete setup.program mode
        control.execution.application.config (by rw [decoded]; rfl)
      dsimp only
      rw [ite_eq_left complete, decoded]

omit [Fintype Player] in
theorem sourceReadout_eq_decode (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (control : (application setup leaks).Control) :
    sourceReadout setup leaks (some control) =
      decodeState? (terminalRefs setup.program) control.execution.application.config.store :=
  serviceSourceReadout_eq_decode setup leaks control

end Vegas
