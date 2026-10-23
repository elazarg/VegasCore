/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.AnchoredOpeningClients
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
private theorem apply_eq_one_of_subsingleton {α : Type} [Subsingleton α] (law : PMF α) (a : α) :
    law a = 1 := by
  rw [← law.tsum_coe, tsum_eq_single a (fun other different =>
    (different (Subsingleton.elim other a)).elim)]

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
