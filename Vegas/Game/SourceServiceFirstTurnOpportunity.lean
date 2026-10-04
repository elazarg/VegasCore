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
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The first ready own turn is protected under the reaction and inclusion
budget. The view may be the freshly sampled activation view: only its first
turn count is needed, while the clock and readiness come from the actual raw
scheduler boundary. -/
theorem firstTurn_inclusionFits {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (answered : ActivationsAnswered setup leaks execution)
    {owner : Player} {event : (graph setup).EventId}
    (owned : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    {view : (application setup leaks).PlayerView}
    (first : sourceServiceTurn setup leaks owner event (execution.recall owner) view = some 0) :
    execution.application.publicView.InclusionFitsDeadline (runtime setup) bound event := by
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
        (runtime setup).deadline event)
  rw [activated]
  omega

end Vegas
