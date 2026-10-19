/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryCommitPhaseArchive
import Vegas.Game.RecoveryCompletedPhaseWitness

/-! # Full witnesses at the same selected ordinary binding boundary -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The existing clean binding producer retains its actual full source word
and full witness at the drained intermediate, before the real settle. -/
theorem RecoverySourceWitness.completed_binding_history
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {plan : RuntimePhasePlan (serviceGraph setup mode)}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (witness : RecoverySourceWitness setup mode plan state)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .commitment)
    (finished : phase.Finished (phase.drain state.current))
    (clean : ¬ (((phase.drain state.current).excluded \ state.entry.excluded) ∩
      phase.owners).Nonempty) :
    ∃ next : RecoverySourceWitness setup mode plan
      (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
        state.retired⟩ : PhaseRuntimeState (serviceGraph setup mode)),
      next.checkpoint.residual.lift
          (ProtocolState.entry next.checkpoint.residual.tail next.checkpoint.source) =
        witness.checkpoint.commitResultPoint (phase.drain state.current) ∧
      (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
          ⟨_, witness.checkpoint.trace⟩ ⟨_, next.checkpoint.trace⟩ ∧
        setup.recoveryJointRecall next.checkpoint.trace =
          (witness.checkpoint.commitInstructionWord (phase.drain state.current).native).reverse ++
            setup.recoveryJointRecall witness.checkpoint.trace) ∧
      witness.checkpoint.ProposalDelta plan next.checkpoint ∧
      state.normalize = PhaseRuntimeState.settle remaining state.generation
        (phase.drain state.current) (phase.drain state.current) state.retired := by
  have phaseMaximal := maximal.suffix witness.suffix
  have member : phase ∈ plan.phases := witness.suffix.subset (by
    rw [installed]
    exact List.mem_cons_self)
  have low : phase.low = state.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have committing := witness.checkpoint.compiled.atCommit_of_bindingPhase setup.program mode
    witness.checkpoint.residual.tail witness.checkpoint.refs witness.checkpoint.source.revelations
      witness.checkpoint.registry witness.checkpoint.embedding witness.checkpoint.before
        state.attempt.phase phase kind low witness.checkpoint.source
  obtain ⟨inputs, native⟩ := witness.native
  have imageNative := phase.drain_invariant state.current native.active
  obtain ⟨⟨next, point, ⟨fuel, path, instructions⟩, word, _intended⟩, normalized⟩ :=
    witness.checkpoint.after_commit_clean committing phase remaining installed phaseMaximal
      witness.binding witness.receipts witness.stored witness.remembered native
        witness.order.coverage finished clean
  obtain ⟨aligned, chronology, origins, delta⟩ :=
    witness.checkpoint.commit_phase_archive plan phase remaining installed member phaseMaximal
      kind committing witness.aligned witness.chronology witness.origins witness.exclusions
        witness.failures witness.archives witness.receipts witness.stored witness.remembered
          witness.order ⟨inputs, imageNative⟩ finished next path instructions word
  let nextWitness := witness.completed_phase_checkpoint phase remaining installed finished next
    aligned chronology origins
  exact ⟨nextWitness, point, ⟨fuel, path, instructions⟩, delta, normalized⟩

end Vegas
