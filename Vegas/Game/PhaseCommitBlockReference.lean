/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProtocolSuffixPolicy
import Vegas.Source.CommitPrefixConditioning
import Vegas.Game.CommitRecoveryNonmissingSource
import Vegas.Game.RecoveryCheckpointHistory
import Vegas.Game.CompiledCommitControl

/-! # Complete latent source-block reference laws at actual native callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- An actual initialized binding callback determines its saved source entry
and the entire current source block. The block is sampled with the original
conditional AUX kernels at lifted updated views. Distinct owners factor only
conditional on this entry; no native/source posterior identity is asserted. -/
theorem phase_ready_binding_block_reference
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
        horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (clear : control.execution.application.current.excluded = ∅)
    (wellFormed : setup.WellFormed)
    (profile : ∀ owner, setup.commitRecoveryModel.BehavioralPolicy owner) :
    ∃ checkpoint : RecoverySourceCheckpoint setup mode control.execution.application,
      control.execution.application.entry.excluded = ∅ ∧
      ∃ residual : SourceProgram.BehavioralProfile checkpoint.residual.tail,
        (∀ owner point,
          (residual owner).protocolAction checkpoint.residual.tail
              (ProtocolState.observe owner checkpoint.residual.tail point) =
            (setup.commitRecoveryNonmissingProfile profile owner
              (setup.commitRecoveryClearInformation wellFormed owner
                (some (ProtocolState.observe owner setup.program
                  (checkpoint.residual.lift point))))).map
                    (fun choice => CommitRecoveryMove.underlying choice.1)) ∧
        ∃ (Δ : SourceCtx Player L) (P : Finset VarId)
          (suffix : SourceProgram Player L Δ P)
          (block : SourceProgram.CommitPrefix checkpoint.residual.context
            checkpoint.residual.names Δ P)
          (reconstruct : block.prepend suffix = checkpoint.residual.tail),
          0 < block.length ∧ IsCommitBoundary suffix ∧
          let typed := cast (congrArg (fun program => SourceProgram.BehavioralProfile program)
            reconstruct.symm) residual
          (block.prefixLaw suffix typed checkpoint.source).map
              (fun final owner => final.view owner) =
            independentProduct (fun owner =>
              (block.prefixLaw suffix typed checkpoint.source).map (Config.view owner)) := by
  obtain ⟨checkpoint⟩ := recoverySourceCheckpoint_history setup mode runtime leaks plan maximal
    horizon scheduler trace
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have physical : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have coverage := phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    physical
  have savedClear : control.execution.application.entry.excluded = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro owner excluded
    have active := coverage.inherited excluded
    rw [clear] at active
    exact Finset.notMem_empty _ active
  obtain ⟨residual, same⟩ := checkpoint.origin.exists_behavioralProfile
    (setup.commitRecoveryNonmissingSourceProfile wellFormed profile)
  refine ⟨checkpoint, savedClear, residual, ?_, ?_⟩
  · intro owner point
    exact (same owner point).trans (setup.commitRecovery_nonmissingSource_raw wellFormed profile
      owner (ProtocolState.observe owner setup.program (checkpoint.residual.lift point)))
  · obtain ⟨phase, head, inside⟩ := request.2.1
    have interval := phase.mem_events event |>.mp inside
    have field := phase.fields event interval.1 interval.2
    have kind : phase.kind = .commitment := by
      cases selected : phase.kind with
      | commitment => rfl
      | reveal =>
          rw [selected, RuntimePhaseKind.Matches, binding] at field
          obtain ⟨other, impossible⟩ := field
          cases impossible
      | sample =>
          rw [selected, RuntimePhaseKind.Matches, binding] at field
          obtain ⟨other, impossible⟩ := field
          cases impossible
    have low : phase.low = control.execution.application.attempt.phase := by
      rw [PhaseRuntimeState.attempt, Option.mem_def.mp head]
      rfl
    have committing := CompiledSuffix.atCommit_of_bindingPhase setup.program mode
      checkpoint.residual.tail checkpoint.refs checkpoint.source.revelations checkpoint.registry
      checkpoint.embedding checkpoint.before control.execution.application.attempt.phase
      checkpoint.compiled phase kind low checkpoint.source
    obtain ⟨Δ, P, suffix, block, reconstruct, boundary⟩ := commitPhase checkpoint.residual.tail
    have positive : 0 < block.length := by
      rw [← reconstruct] at committing
      exact block.length_pos_of_committing suffix checkpoint.source boundary committing
    refine ⟨Δ, P, suffix, block, reconstruct, positive, boundary, ?_⟩
    exact block.prefixLaw_views_product suffix _ checkpoint.source

end Vegas
