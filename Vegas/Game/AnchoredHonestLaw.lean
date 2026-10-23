/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AnchoredOpeningClients
import Vegas.Game.OnePacketHonestForced
import Vegas.Game.OnePacketOwnSubmissions

/-! # Histories as-if-honest play reaches from a boundary

An information state is reached from a history when as-if-honest play in the
one-packet game reaches it from there (`Vegas.HonestReachedFrom`). A one-packet
history ending between rounds at an untouched prefix that decodes to a point of
the intended game ends at a reached boundary
(`Vegas.reachedBoundary_of_onePacket`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Under a global horizon, terminal play from a history reached by play of
some length from `start` is reached by play from `start` of that length plus
the horizon. -/
private theorem mem_runBehavioralFrom_of_terminalFrom [Fintype Player]
    {E : ExecutionProtocol Player}
    (M : InformationModel E) (certificate : E.WellFoundedHistories) {bound : Nat}
    (bounded : E.BoundedHorizon bound) (profile : ∀ who, M.BehavioralPolicy who) {fuel : Nat}
    {start history final : E.History}
    (reached : history ∈ (M.runBehavioralFrom profile fuel start).support)
    (finished : final ∈ (M.runBehavioralTerminalFrom certificate profile history).support) :
    final ∈ (M.runBehavioralFrom profile (fuel + bound) start).support := by
  rw [M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded] at finished
  rw [M.runBehavioralFrom_add]
  exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨history, reached, finished⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem apply_eq_one_of_subsingleton {α : Type} [Subsingleton α] (law : PMF α) (a : α) :
    law a = 1 := by
  rw [← law.tsum_coe, tsum_eq_single a (fun other different =>
    (different (Subsingleton.elim other a)).elim)]

variable (setup leaks) in
/-- An information state of `who` at some history as-if-honest play reaches
from `start` in the one-packet game. -/
def HonestReachedFrom [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) (who : Player) (info : (application setup leaks).Info) : Prop :=
  ∃ fuel, ∃ history ∈ ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).runBehavioralFrom
      (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment) fuel
      start).support,
    (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).infoOf who
      history.trace = info

/-- **One-packet boundaries are reached boundaries.** A history of the
one-packet game ending between rounds at an execution whose configuration is a
prefix of `rank`, with every event from `rank` on untouched and a decoding to a
point of the intended game, ends at a reached boundary: its own submissions
were made at the owners' turns (`Vegas.onePacket_ownSubmissionsAtTurn`). -/
theorem reachedBoundary_of_onePacket [Fintype Player] (bounds : MessageBounds (graph setup))
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler} {rank : Nat}
    {anchor : (application setup leaks).Execution}
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (bounded : anchor.environmentRecall.length ≤ horizon)
    (ordered : anchor.application.config.cut.IsPrefix rank)
    (untouched : ∀ event : (graph setup).EventId, rank ≤ event.val →
      Untouched setup leaks event anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point) :
    ReachedBoundary setup leaks horizon scheduler rank anchor := by
  have trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩) :=
    state ▸ start.trace
  exact ⟨⟨(bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
      scheduler trace⟩, bounded, ordered, untouched,
    onePacket_ownSubmissionsAtTurn bounds trace ordered point decoded intendedPoint⟩

end Vegas
