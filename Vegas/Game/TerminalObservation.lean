module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Source.InitialState

@[expose] public section

/-! # Common terminal observations and monetary receipt readouts

The fixed reader retains original inputs, optional typed terminal cells and
public default history, the public result and the whole realized vector.
Valuation inversion changes only that vector and keeps the same input reader.
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The compiler observation retains the terminal cells, public default history
and realized payoff vector, with their fixed input and public-result readers. -/
structure TerminalObservation (setup : Setup (Player := Player) (L := L)) where
  initialInputs : Option (State L setup.context)
  terminal : Option (State L setup.program.terminalCtx × DefaultHistory Player)
  publicResult : Option (PublicOutcome setup.program)
  netPayoffs : Player → ℝ

namespace TerminalObservation

/-- Both games use this same fixed reader; no alternative input decoder is a
parameter of the preservation proposition. -/
def read (setup : Setup (Player := Player) (L := L))
    (terminal : Option (State L setup.program.terminalCtx × DefaultHistory Player))
    (netPayoffs : Player → ℝ) :
    TerminalObservation setup where
  initialInputs := terminal.map (fun final => initialState setup.program final.1)
  terminal := terminal
  publicResult := terminal.map (fun final => ⟨sourcePublicEnv final.1, final.2⟩)
  netPayoffs := netPayoffs

end TerminalObservation

namespace TerminalObservation

/-- Change only the monetary coordinate: every original input, typed terminal
state and public-result coordinate is retained. Absent readout keeps zero valuation. -/
def cashReadout (setup : Setup (Player := Player) (L := L))
    (valuation : State L setup.program.terminalCtx × DefaultHistory Player → Player → ℝ)
    (observation : TerminalObservation setup) : TerminalObservation setup :=
  { observation with netPayoffs := fun who => observation.netPayoffs who -
      observation.terminal.elim 0 (fun terminal => valuation terminal who) }

theorem cashReadout_read (setup : Setup (Player := Player) (L := L))
    (valuation : State L setup.program.terminalCtx × DefaultHistory Player → Player → ℝ)
    (terminal : Option (State L setup.program.terminalCtx × DefaultHistory Player))
    (payoffs : Player → ℝ) :
    cashReadout setup valuation (read setup terminal payoffs) =
      read setup terminal (fun who => payoffs who -
        terminal.elim 0 (fun state => valuation state who)) := rfl

end TerminalObservation

end Vegas
