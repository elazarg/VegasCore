/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecidedCompletion

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
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- The first ready own turn is protected under the reaction and inclusion
budget. The view may be the freshly sampled activation view: only its first
turn count is needed, while the clock and readiness come from the actual raw
scheduler boundary. -/
theorem firstTurn_inclusionFits {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    {remaining : Nat} {execution : (serviceApplication setup mode deadline leaks).Execution}
    (trace :
        ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution)
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    {view : (serviceApplication setup mode deadline leaks).PlayerView}
    (first : serviceTurn setup mode deadline leaks owner event (execution.recall owner) view =
        some 0) :
    execution.application.publicView.InclusionFitsDeadline (serviceRuntime setup mode deadline)
        bound event := by
  obtain ⟨inputs, invariant⟩ := (roster_trace_facts setup leaks horizon scheduler trace).1
  obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event ready
    (by rw [owned]; rfl)
  have early : execution.application.clock ≤ entered + delay event := by
    by_contra late
    obtain ⟨answer, member, turn⟩ := opportunity_turn contract trace answered owned ready entered
      activated (by omega)
    exact (sourceServiceTurn_first first).2 answer member turn
  have budget := timely event (by rw [owned]; rfl)
  change (match execution.application.activatedAt event with
    | none => False
    | some started => execution.application.clock - started + bound event <
        (serviceRuntime setup mode deadline).deadline event)
  rw [activated]
  omega

end Vegas
