/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProgramPayoffs

/-! # Common terminal observations and monetary receipt readouts

The fixed reader retains original inputs, the complete optional typed terminal
store, the public result and the whole realized vector. Valuation inversion
changes only that vector and keeps the same source-defined input reader.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The complete observation whose JOINT law must be preserved. The four fields
name the four outcome coordinates, including the entire payoff vector. -/
structure TerminalObservation (setup : Setup (Player := Player) (L := L)) where
  initialInputs : Option (State L setup.context)
  terminalState : Option (State L setup.program.terminalCtx)
  publicResult : Option (PublicOutcome setup.program)
  netPayoffs : Player → ℝ

namespace TerminalObservation

/-- Both games use this same fixed reader; no alternative input decoder is a
parameter of the preservation proposition. -/
def read (setup : Setup (Player := Player) (L := L))
    (terminal : Option (State L setup.program.terminalCtx)) (netPayoffs : Player → ℝ) :
    TerminalObservation setup where
  initialInputs := terminal.map (initialState setup.program)
  terminalState := terminal
  publicResult := terminal.map (publicOutcome setup.program)
  netPayoffs := netPayoffs

end TerminalObservation

namespace TerminalObservation

/-- Change only the monetary coordinate: every original input, typed terminal
state and public-result coordinate is retained. Absent readout keeps zero valuation. -/
def cashReadout (setup : Setup (Player := Player) (L := L))
    (valuation : State L setup.program.terminalCtx → Player → ℝ)
    (observation : TerminalObservation setup) : TerminalObservation setup :=
  { observation with netPayoffs := fun who => observation.netPayoffs who -
      observation.terminalState.elim 0 (fun terminal => valuation terminal who) }

theorem cashReadout_read (setup : Setup (Player := Player) (L := L))
    (valuation : State L setup.program.terminalCtx → Player → ℝ)
    (terminal : Option (State L setup.program.terminalCtx)) (payoffs : Player → ℝ) :
    cashReadout setup valuation (read setup terminal payoffs) =
      read setup terminal (fun who => payoffs who -
        terminal.elim 0 (fun state => valuation state who)) := rfl

end TerminalObservation

end Vegas
