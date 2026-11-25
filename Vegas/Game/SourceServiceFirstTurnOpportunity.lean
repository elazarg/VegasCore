module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceCompletion
public import Vegas.Game.SourceServiceTurnPolicy
public import Vegas.Pending.FirstCallback

@[expose] public section

/-! # Protection of the owner's first ready turn

Every completed scheduler round answers an activation, regardless of the
activated player's policy. The opportunity contract therefore bounds the
clock at an owner's first ready turn: a later clock would require an earlier
answered activation in the same readiness episode. The timing budget leaves
that first turn inside the protected inclusion window.

Foreign policies are unrestricted. No submission or silence premise is used
to infer protection of the current turn.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- The first ready own turn is protected under the reaction and inclusion
budget. The view may be the freshly sampled activation view: only its first
turn count is needed, while the clock and readiness come from the actual raw
scheduler boundary. -/
theorem firstTurn_inclusionFits {event : (serviceGraph setup deps).EventId}
    (ownerSolitary : (serviceGraph setup deps).OwnerSolitary event)
    {horizon : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
        (serviceInitialDistribution setup deps) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceTimeouts setup deps duration) delay bound)
    {remaining : Nat} {execution : (serviceApplication setup deps duration leaks).Execution}
    (trace :
        ((serviceApplication setup deps duration leaks).protocol
          (serviceInitialDistribution setup deps)
        horizon scheduler).Trace (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution)
    {owner : Player}
    (owned : (serviceGraph setup deps).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    {view : (serviceApplication setup deps duration leaks).PlayerView}
    (first : turnIndex (serviceTimeouts setup deps duration)
      leaks owner event (execution.logs owner) view =
        some 0) :
    execution.application.publicView.InclusionFitsDeadline (serviceTimeouts setup deps duration)
        bound event := by
  rw [serviceInitialDistribution_eq_inputs setup] at contract trace
  exact EventGraphRuntime.firstTurn_inclusionFits (serviceTimeouts setup deps duration) leaks
    ownerSolitary contract timely trace answered owned ready first

end Vegas
