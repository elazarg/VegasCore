/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProposalRecoveryArchiveChronology
import Vegas.Source.CommitRecoveryPublicScan
import Vegas.Game.ProposalRecoveryPublicHistory
import Vegas.Game.CommitRecoveryAncillaryBelief

/-! # Canonical proposal archives determine actual public disclosure histories -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

def proposalRecoveryPublicCursor (who : Player)
    (signal : setup.ProtocolView who × (Finset Player × Nat × Nat)) : Option (Nat × Nat) :=
  let address := setup.commitRecoveryPublicAddress who signal
  address.1.map fun rank => (address.2.2.1, rank)

theorem proposalRecoveryPublicCursor_signal (who : Player)
    (state : setup.proposalRecoveryProtocol.State) :
    setup.proposalRecoveryPublicCursor who (setup.attemptPublicSignal who state) =
      setup.proposalRecoveryCursor state := by
  cases state with
  | none => rfl
  | some current =>
      unfold proposalRecoveryPublicCursor
      rw [setup.commitRecoveryPublicAddress_signal]
      rfl

theorem proposalRecovery_public_cursors (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace trace)).map
        (setup.proposalRecoveryPublicCursor who) =
      setup.proposalRecoveryCursor state :: setup.proposalRecoveryCursorWord trace := by
  induction trace with
  | start => rfl
  | extend prior joint legal supported ih =>
      rw [proposalRecoveryEraseTrace, setup.publicRecall_extend, List.map_cons,
        setup.proposalRecoveryPublicCursor_signal, ih]
      rfl

theorem proposalRecoveryCursorWord_eq_of_semantic_public (who : Player)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (same : setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace left) =
      setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace right)) :
    setup.proposalRecoveryCursorWord left = setup.proposalRecoveryCursorWord right := by
  have words := congrArg (List.map (setup.proposalRecoveryPublicCursor who)) same
  rw [setup.proposalRecovery_public_cursors, setup.proposalRecovery_public_cursors] at words
  exact (List.cons.inj words).2

theorem proposalRecoveryPublicRecall_deltas (who : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryPublicRecall who trace).map Prod.snd =
      setup.proposalRecoveryDeltaRecall trace ++ [none] := by
  induction trace with
  | start => rfl
  | extend prior joint legal supported ih =>
      simp only [proposalRecoveryPublicRecall, List.map_cons, proposalRecoveryDeltaRecall,
        List.cons_append, ih]

/-- Actual semantic public chronology and the canonical proposal archive recover
the entire labeled public chronology, including the positions of silent steps. -/
theorem proposalRecoveryPublicRecall_eq_of_semantic_archive (who : Player)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (semantic : setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace left) =
      setup.attemptPublicRecall who (setup.proposalRecoveryEraseTrace right))
    (archive : setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who left) =
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who right)) :
    setup.proposalRecoveryPublicRecall who left = setup.proposalRecoveryPublicRecall who right := by
  have cursors := setup.proposalRecoveryCursorWord_eq_of_semantic_public who left right semantic
  have deltas := setup.proposalRecoveryDeltaRecall_eq_of_archive_cursor_word who
    left right cursors archive
  have first : (setup.proposalRecoveryPublicRecall who left).map Prod.fst =
      (setup.proposalRecoveryPublicRecall who right).map Prod.fst := by
    rw [setup.proposalRecoveryPublicRecall_semantic,
      setup.proposalRecoveryPublicRecall_semantic, semantic]
  have second : (setup.proposalRecoveryPublicRecall who left).map Prod.snd =
      (setup.proposalRecoveryPublicRecall who right).map Prod.snd := by
    rw [setup.proposalRecoveryPublicRecall_deltas,
      setup.proposalRecoveryPublicRecall_deltas, deltas]
  have combined : (setup.proposalRecoveryPublicRecall who left).unzip =
      (setup.proposalRecoveryPublicRecall who right).unzip := by
    simpa only [List.unzip_eq_map] using Prod.ext first second
  exact (List.zip_unzip _).symm.trans
    ((congrArg (Function.uncurry List.zip) combined).trans (List.zip_unzip _))

theorem proposalRecoveryPublicRecall_eq_of_erased_archive (who : Player)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (semantic : setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace left)) =
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who (setup.proposalRecoveryEraseTrace right)))
    (archive : setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who left) =
      setup.proposalRecoveryArchive who (setup.proposalRecoveryModel.infoOf who right)) :
    setup.proposalRecoveryPublicRecall who left = setup.proposalRecoveryPublicRecall who right := by
  exact setup.proposalRecoveryPublicRecall_eq_of_semantic_archive who left right
    (setup.commitRecovery_publicRecall_eq_of_erasedInformation_eq who
      (setup.proposalRecoveryEraseTrace left) (setup.proposalRecoveryEraseTrace right) semantic)
    archive

end Vegas.SourceProgram.Setup
