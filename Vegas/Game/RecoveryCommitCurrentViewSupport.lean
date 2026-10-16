/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryCommitPrefixSupport
import Vegas.Source.CommitPrefixWordProjection

/-! # Current source-view support in the same original complete prefix law -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Any typed clear prefix Attempt supplies positive current-view support in
its SAME original residual-profile complete word law. -/
theorem RecoverySourceCheckpoint.current_view_mem_prefixLaw
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {state : EventGraphRuntime.PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (savedClear : state.entry.excluded = ∅) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (residual : SourceProgram.BehavioralProfile checkpoint.residual.tail)
    (raw : ∀ owner point, (residual owner).protocolAction checkpoint.residual.tail
      (ProtocolState.observe owner checkpoint.residual.tail point) =
      (setup.commitRecoveryNonmissingProfile assessment.strategy owner
        (setup.commitRecoveryClearInformation wellFormed owner
          (some (ProtocolState.observe owner setup.program
            (checkpoint.residual.lift point))))).map
        (fun choice => CommitRecoveryMove.underlying choice.1))
    {Δ Ξ : SourceCtx Player L} {P Q : Finset VarId}
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (later : SourceProgram.CommitPrefix Δ P Ξ Q) (suffix : SourceProgram Player L Ξ Q)
    (reconstruct : (earlier.append later).prepend suffix = checkpoint.residual.tail)
    (final : Config Player L Δ) (attempt : earlier.Attempt checkpoint.source ∅ final ∅)
    (focal : Player) :
    let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
    final.view focal ∈ (((earlier.append later).prefixLaw suffix typed checkpoint.source).map
      (fun complete => later.entryView focal (complete.view focal))).support := by
  intro typed
  let split := cast (congrArg SourceProgram.BehavioralProfile
    (earlier.prepend_append later suffix)) typed
  have reconstructEarlier : earlier.prepend (later.prepend suffix) = checkpoint.residual.tail :=
    (earlier.prepend_append later suffix).symm.trans reconstruct
  have supported := checkpoint.attempt_mem_prefixLaw savedClear wellFormed assessment mixed residual
    raw earlier (later.prepend suffix) reconstructEarlier final attempt
  have present : final.view focal ∈
      ((earlier.prefixLaw (later.prepend suffix) split checkpoint.source).map
        (SourceProgram.Config.view focal)).support := by
    apply (PMF.mem_support_map_iff _ _ _).mpr
    refine ⟨final, ?_, rfl⟩
    simpa only [split, typed, cast_cast] using supported
  have complete := earlier.prefixLaw_append later suffix typed checkpoint.source
  have projected := earlier.prefixLaw_split_entryView later suffix split checkpoint.source focal
  dsimp only at projected
  rw [PMF.map_comp] at projected
  dsimp only [Function.comp_def] at projected
  change (earlier.append later).prefixLaw suffix typed checkpoint.source =
    (earlier.prefixLaw (later.prepend suffix) split checkpoint.source).bind
      (later.prefixLaw suffix (earlier.tailProfile (later.prepend suffix) split)) at complete
  rw [← complete] at projected
  rw [projected]
  exact present

end Vegas
