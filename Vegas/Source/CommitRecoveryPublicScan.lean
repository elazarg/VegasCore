/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryPublicReadback
import Vegas.Source.CommitRecoveryPublicPadding
import Vegas.Source.CommitRecoveryAttemptReset
import Vegas.Source.CommitRecoveryInstructions

/-! # Public source chronology read from numeric controls and retained cells -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The source signal's cursor and exact original exclusion/attempt controls.
Private typed values and remembered own actions are absent from this readout. -/
def commitRecoveryPublicAddress (who : Player)
    (signal : setup.ProtocolView who × (Finset Player × Nat × Nat)) :
    Option Nat × (Finset Player × Nat × Nat) :=
  (signal.1.map (ProtocolView.position who setup.program), signal.2)

/-- The public signal's numeric fields are the actual state address, not an
independently selected endpoint label. -/
theorem commitRecoveryPublicAddress_signal (who : Player)
    (current : CommitRecoveryState setup.program) :
    setup.commitRecoveryPublicAddress who (setup.attemptPublicSignal who (some current)) =
      current.publicAddress := by
  have point := ProtocolView.position_add_remaining who setup.program current.point
  unfold commitRecoveryPublicAddress attemptPublicSignal commitRecoveryPrivate
    commitRecoveryPublic CommitRecoveryState.publicAddress
  simp only [Option.map_some, ProtocolView.position_publicOnly]
  have first : ProtocolView.position who setup.program
      (ProtocolState.observe who setup.program current.point) =
      instructionCount setup.program - ProtocolState.remaining setup.program current.point := by
    omega
  rw [first]

/-- The chronological transition fold supplies exactly the numeric part of
the complete source recall, with its single pre-setup observation retained. -/
theorem commitRecovery_publicRecall_addresses (who : Player)
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.attemptPublicRecall who trace).map (setup.commitRecoveryPublicAddress who) =
      (setup.recoveryAddressWord trace).reverse ++ [(none, (∅, 0, 0))] := by
  induction trace with
  | start => rfl
  | @extend before after prior joint legal supported ih =>
      have signal : setup.commitRecoveryPublicAddress who
          (setup.attemptPublicSignal who after) =
          after.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress := by
        cases after with
        | none => rfl
        | some current => exact setup.commitRecoveryPublicAddress_signal who current
      have recall : setup.attemptPublicRecall who (prior.extend joint legal supported) =
          setup.attemptPublicSignal who after :: setup.attemptPublicRecall who prior := by
        rw [attemptPublicRecall, InfoSignals.infoOf_extend]
        rfl
      rw [recall, List.map_cons, signal, ih, setup.recoveryAddressWord_extend]
      simp only [List.reverse_append, List.reverse_singleton, List.cons_append,
        List.nil_append]

/-- Read a public signal at its original static cursor from the retained,
padded typed public image. Retry controls are supplied by its numeric address. -/
def commitRecoveryPublicRead (who : Player)
    (image : SourceProgram.ProtocolView who setup.program)
    (address : Option Nat × (Finset Player × Nat × Nat)) :
    setup.ProtocolView who × (Finset Player × Nat × Nat) :=
  (address.1.bind fun rank =>
    (ProtocolView.atRank who setup.program rank image).map
      (ProtocolView.publicOnly who setup.program), address.2)

theorem commitRecoveryPublicRead_publicOnly (who : Player)
    (image : SourceProgram.ProtocolView who setup.program)
    (address : Option Nat × (Finset Player × Nat × Nat)) :
    setup.commitRecoveryPublicRead who (ProtocolView.publicOnly who setup.program image) address =
      setup.commitRecoveryPublicRead who image address := by
  rcases address with ⟨rank, controls⟩
  cases rank with
  | none => rfl
  | some rank =>
      apply Prod.ext
      · simp only [commitRecoveryPublicRead, Option.bind_some, ProtocolView.atRank_publicOnly,
          Option.map_map, Function.comp_def, ProtocolView.publicOnly_idempotent]
      · rfl

/-- The complete genuine public source recall, including observations in
voided attempts, is exactly the numeric chronological word read through one
retained public typed image. Setup and every actual close occur exactly once. -/
theorem commitRecovery_publicRecall_read
    (who : Player) (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (survives : who ∉ current.excluded) :
    setup.attemptPublicRecall who trace =
      ((setup.attemptPublicRecall who trace).map
        (setup.commitRecoveryPublicAddress who)).map
          (setup.commitRecoveryPublicRead who (ProtocolState.observe who setup.program
            (ProtocolState.automaticCommitBlock setup.program current.point))) := by
  let image := ProtocolState.observe who setup.program
    (ProtocolState.automaticCommitBlock setup.program current.point)
  have readSignal : ∀ {state : setup.commitRecoveryProtocol.State}
      (priorTrace : setup.commitRecoveryProtocol.Trace state) {fuel : Nat},
      setup.commitRecoveryProtocol.ReachesWithin fuel ⟨state, priorTrace⟩ ⟨some current, trace⟩ →
      setup.commitRecoveryPublicRead who image
        (setup.commitRecoveryPublicAddress who (setup.attemptPublicSignal who state)) =
          setup.attemptPublicSignal who state := by
    intro state priorTrace fuel path
    cases state with
    | none => rfl
    | some before =>
        have read := setup.commitRecovery_public_rank_of_reaches who path before current rfl rfl
          survives
        apply Prod.ext
        · simpa only [commitRecoveryPublicRead, commitRecoveryPublicAddress, attemptPublicSignal,
            commitRecoveryPrivate, Option.map_some, ProtocolView.position_publicOnly,
            Option.bind_some, image] using read
        · rfl
  have all : ∀ {state : setup.commitRecoveryProtocol.State}
      (priorTrace : setup.commitRecoveryProtocol.Trace state) {fuel : Nat},
      setup.commitRecoveryProtocol.ReachesWithin fuel ⟨state, priorTrace⟩ ⟨some current, trace⟩ →
      ∀ signal ∈ setup.attemptPublicRecall who priorTrace,
        setup.commitRecoveryPublicRead who image
          (setup.commitRecoveryPublicAddress who signal) = signal := by
    intro state priorTrace
    induction priorTrace with
    | start =>
        intro fuel path signal member
        change signal ∈ [setup.attemptPublicSignal who none] at member
        cases List.mem_singleton.mp member
        exact readSignal .start path
    | @extend before after prior joint legal realized ih =>
        intro fuel path signal member
        have recall : setup.attemptPublicRecall who (prior.extend joint legal realized) =
            setup.attemptPublicSignal who after :: setup.attemptPublicRecall who prior := by
          rw [attemptPublicRecall, InfoSignals.infoOf_extend]
          rfl
        rw [recall, List.mem_cons] at member
        rcases member with now | earlier
        · subst signal
          exact readSignal (prior.extend joint legal realized) path
        · exact ih (ReachesWithin.step joint legal realized path) signal earlier
  symm
  rw [List.map_map]
  calc
    _ = (setup.attemptPublicRecall who trace).map id :=
      List.map_congr_left fun signal member => all trace (.refl 0 _) signal member
    _ = _ := List.map_id _

/-- Two genuine surviving histories with the same numeric public word and
retained public image have the same entire public source signal recall.
No equality of prior private words is required. -/
theorem commitRecovery_publicRecall_eq_of_numeric
    (who : Player) (first second : CommitRecoveryState setup.program)
    (left : setup.commitRecoveryProtocol.Trace (some first))
    (right : setup.commitRecoveryProtocol.Trace (some second))
    (leftSurvives : who ∉ first.excluded) (rightSurvives : who ∉ second.excluded)
    (image : ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program
          (ProtocolState.automaticCommitBlock setup.program first.point)) =
      ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program
          (ProtocolState.automaticCommitBlock setup.program second.point)))
    (numeric : (setup.attemptPublicRecall who left).map
        (setup.commitRecoveryPublicAddress who) =
      (setup.attemptPublicRecall who right).map (setup.commitRecoveryPublicAddress who)) :
    setup.attemptPublicRecall who left = setup.attemptPublicRecall who right := by
  rw [setup.commitRecovery_publicRecall_read who first left leftSurvives,
    setup.commitRecovery_publicRecall_read who second right rightSurvives, numeric]
  apply List.map_congr_left
  intro address _member
  apply Prod.ext
  · apply congrArg (Option.bind address.1)
    funext rank
    simpa only [ProtocolView.atRank_publicOnly] using
      congrArg (ProtocolView.atRank who setup.program rank) image
  · rfl

/-- Rebuild the erased full information label from the current live typed view
and the chronological numeric word. The public image is read from that same
view; retired own words and prior private observations are never reconstructed. -/
def commitRecoveryErasedRead (who : Player)
    (view : SourceProgram.ProtocolView who setup.program)
    (controls : Finset Player × Nat × Nat)
    (addresses : List (Option Nat × (Finset Player × Nat × Nat))) :
    setup.commitRecoveryModel.InfoState who :=
  (((some (ProtocolView.eraseHistory who setup.program view), controls),
    (addresses.map (setup.commitRecoveryPublicRead who
      (ProtocolView.publicPadding who setup.program view))).tail), [])

/-- Every genuine surviving source history has exactly this readback, retaining
the entire true public chronology and the literal current live private cells. -/
theorem commitRecovery_erasedInformation_read
    (who : Player) (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (survives : who ∉ current.excluded) :
    setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who trace) =
      setup.commitRecoveryErasedRead who (ProtocolState.observe who setup.program current.point)
        (setup.commitRecoveryPublic (some current))
        ((setup.attemptPublicRecall who trace).map
          (setup.commitRecoveryPublicAddress who)) := by
  rw [setup.erasedInformation_publicRecall who trace]
  unfold commitRecoveryErasedRead
  rw [ProtocolView.publicPadding_observe]
  rw [funext (setup.commitRecoveryPublicRead_publicOnly who
    (ProtocolState.observe who setup.program
      (ProtocolState.automaticCommitBlock setup.program current.point)))]
  rw [← setup.commitRecovery_publicRecall_read who current trace survives]
  rfl

end Vegas.SourceProgram.Setup
