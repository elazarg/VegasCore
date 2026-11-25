module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceFirstTurnCompletion

@[expose] public section

/-! # Source law of the first-turn compiler

First-turn clients preserve the complete source configuration under the
asynchronous service contract on the source information graph.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- First-turn clients preserve the source's full terminal configuration under
an asynchronous scheduler and its reaction and inclusion timing budget. -/
theorem firstTurn_readout_distribution
    (setup : Setup (Player := Player) (L := L))
    {duration : setup.informationGraph.EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon : Nat} {scheduler : (application setup ⟨duration⟩ leaks).Scheduler}
    {delay bound : setup.informationGraph.EventId → Nat}
    (contract : AsyncContract ⟨duration⟩ leaks (initialDistribution setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely ⟨duration⟩ delay bound) (turns : Nat)
    (profile : BehavioralProfile setup.program)
    (authentic : ∀ who, (profile who).AuthenticDisclosures setup.program) :
    FirstTurnSourceAgreement setup setup.informationDependencies duration leaks horizon scheduler
      bound
      turns profile :=
  FirstTurnSourceMatches_of_async ⟨duration⟩ leaks scheduler delay bound profile contract timely
    authentic

end Vegas
