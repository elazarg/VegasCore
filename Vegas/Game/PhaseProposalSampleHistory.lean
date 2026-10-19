/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySampleHistory
import Vegas.Game.RecoveryCompletedPhaseWitness

/-! # Selected full source witnesses through actual singleton samples -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The existing completed sample producer retains its selected value and
source point in the SAME full witness used by subsequent normalization. -/
theorem RecoverySourceWitness.completed_sample_history
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {plan : RuntimePhasePlan (serviceGraph setup mode)}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (witness : RecoverySourceWitness setup mode plan state)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .sample)
    (finished : phase.Finished (phase.drain state.current)) :
    ∃ next : RecoverySourceWitness setup mode plan
      (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
        state.retired⟩ : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)),
      (∃ fuel : Nat,
        setup.commitRecoveryProtocol.ReachesWithin fuel
          ⟨_, witness.checkpoint.trace⟩ ⟨_, next.checkpoint.trace⟩) ∧
      Relation.ReflTransGen
        (NativePublicSourceStep (phase.drain state.current).native 0 setup.program)
        (witness.checkpoint.residual.lift
          (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source),
          state.entry.excluded)
        (next.checkpoint.residual.lift
          (ProtocolState.entry next.checkpoint.residual.tail next.checkpoint.source),
          (phase.drain state.current).excluded) ∧
      (∃ states : List (ProtocolState setup.program × Finset Player),
        ((witness.checkpoint.residual.lift
          (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source),
          state.entry.excluded) :: states).IsChain
            (NativePublicSourceStep (phase.drain state.current).native 0 setup.program) ∧
        ((witness.checkpoint.residual.lift
          (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source),
          state.entry.excluded) :: states).getLast (List.cons_ne_nil _ _) =
          (next.checkpoint.residual.lift
          (ProtocolState.entry next.checkpoint.residual.tail next.checkpoint.source),
            (phase.drain state.current).excluded) ∧
        setup.recoveryAddressWord next.checkpoint.trace =
          setup.recoveryAddressWord witness.checkpoint.trace ++
          states.map (fun point =>
            (CommitRecoveryState.atPoint point.1 point.2 state.generation).publicAddress)) ∧
      (∀ who, who ∉ (phase.drain state.current).excluded →
        next.checkpoint.source.history who = witness.checkpoint.source.history who ++
          (decodeHistory setup.program ((phase.drain state.current).native.config.history.map
            ((toEventGraph setup.program).fromModeCompletion mode)) who).drop
              (decodeHistory setup.program (state.entry.native.config.history.map
                ((toEventGraph setup.program).fromModeCompletion mode)) who).length) ∧
      ((phase.drain state.current).excluded = ∅ →
      ProtocolState.Intended setup.program (witness.checkpoint.residual.lift
        (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source)) →
      ProtocolState.Intended setup.program (next.checkpoint.residual.lift
        (ProtocolState.entry next.checkpoint.residual.tail next.checkpoint.source))) ∧
      NativeSourceReplayExtension setup (phase.drain state.current).native state.generation
        witness.checkpoint.trace next.checkpoint.trace ∧
      (phase.drain state.current).excluded = state.entry.excluded ∧
      witness.checkpoint.ProposalDelta plan next.checkpoint ∧
      (let observed : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
          (program : SourceProgram Player L Γ O),
          SourceProgram.Config Player L Γ →
            (ProtocolState program → ProtocolState setup.program) → Prop :=
        (fun {_Γ} {_O} program => match program with
      | .sample (payload := payload) name _fresh law suffix => fun source lift =>
          ∃ (event : ((toEventGraph setup.program).withMode mode).EventId)
            (output : ((toEventGraph setup.program).withMode mode).outputLayout event =
              .publicData payload) (sampled : L.Val payload),
            sampled ∈ (L.evalDist law (sourcePublicEnv source.state)).support ∧
            event.val = state.attempt.phase ∧
            (⟨.inr event, output⟩ : FieldRef (graphLayout setup.program)
              (.publicData payload)).get? (phase.drain state.current).native.config.store =
                some sampled ∧
            next.checkpoint.residual.lift
              (ProtocolState.entry next.checkpoint.residual.tail next.checkpoint.source) =
              lift (.inr (ProtocolState.entry suffix (sampleSuccessor name source sampled)))
      | .ret _ => fun _ _ => False
      | .commit _ _ _ _ _ => fun _ _ => False
      | .reveal _ _ _ _ _ _ _ => fun _ _ => False);
        observed witness.checkpoint.residual.tail witness.checkpoint.source
          witness.checkpoint.residual.lift) := by
  let image := phase.drain state.current
  have planMember : phase ∈ plan.phases := witness.suffix.subset (by
    rw [installed]
    exact List.mem_cons_self)
  obtain ⟨inputs, native⟩ := witness.native
  have imageNative := phase.drain_invariant state.current native.active
  obtain ⟨next, ⟨fuel, path⟩, publicSteps, addresses, word, intended, replay, sameExcluded,
    observed⟩ :=
    witness.checkpoint.after_sample_history phase remaining installed kind
      witness.receipts.exclusion
      witness.stored witness.remembered imageNative.reachable finished
  obtain ⟨aligned, chronology, origins, delta⟩ :=
    witness.checkpoint.public_phase_archive plan maximal phase remaining installed planMember
      (by simp only [kind]; decide) witness.aligned witness.chronology witness.origins
        witness.exclusions witness.failures witness.archives witness.receipts witness.stored
          witness.remembered witness.order ⟨inputs, imageNative⟩ finished next path publicSteps
            addresses word replay
  let nextWitness := witness.completed_phase_checkpoint phase remaining installed finished next
    aligned chronology origins
  exact ⟨nextWitness, ⟨fuel, path⟩, publicSteps, addresses, word, intended, replay, sameExcluded,
    delta, observed⟩

end Vegas
