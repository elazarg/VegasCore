/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCommitTimingWordPolicy

/-! # Original source-word realization of actual finite timing components -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]


omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem binding_before_block_end
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Δ)
      (insert name P) Ξ Q) :
    earlier.length < (earlier.append (.commit name owner fresh guard later)).length := by
  induction earlier with
  | nil => simp only [CommitPrefix.append, CommitPrefix.length]; omega
  | commit _ _ _ _ rest ih =>
      simpa only [CommitPrefix.append, CommitPrefix.length] using Nat.succ_lt_succ (ih fresh guard
        later)

/-- The actual finite timing component, with RAW removed rather than hidden
in a source prior, is realized by ONE original complete source word for every
operational option. The actual checkpoint derives the source fiber, and the
original serial namespace derives its addressed word readout. -/
theorem RecoverySourceCheckpoint.binding_timing_word_strategy_of_ready
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (execution : (phaseApplication runtime leaks).Execution)
    (checkpoint : RecoverySourceCheckpoint setup mode execution.application)
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    {Δ Ξ : SourceCtx Player L} {P Q : Finset VarId} {name : VarId} {owner : Player}
    {payload : L.Ty} (fresh : name ∉ Δ.map Prod.fst)
    (guard : SourceGuard L Δ owner name payload)
    (later : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Δ)
      (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (earlier : SourceProgram.CommitPrefix checkpoint.residual.context checkpoint.residual.names Δ P)
    (reconstruct : earlier.prepend (.commit name owner fresh guard (later.prepend suffix)) =
      checkpoint.residual.tail)
    (clear : execution.application.entry.excluded = ∅)
    (stored : execution.application.StoredCheckpoint)
    (selected : Fin (eventCount checkpoint.residual.tail))
    (atEnd : selected.val = earlier.length)
    (ready : execution.application.current.native.config.cut.Ready
      (checkpoint.embedding.event selected))
    (acting : (serviceGraph setup mode).actor? (checkpoint.embedding.event selected) = some owner)
    (notPublication : ¬ ((serviceGraph setup mode).outputLayout
      (checkpoint.embedding.event selected)).IsPublication)
    (valid : execution.application.current.native.BindingInvariant) {inputs}
    (reachable : execution.application.current.native.config.Reachable inputs)
    (applicationValid : execution.application.Invariant inputs)
    (retained : execution.application.HistoryCheckpoint)
    (saved : execution.application.entry.native.config.cut.IsPrefix
      execution.application.attempt.phase)
    (bounds : MessageBounds (serviceGraph setup mode))
    (binding : (serviceGraph setup mode).outputLayout (checkpoint.embedding.event selected) =
      .binding owner payload)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, checkpoint.embedding.event selected⟩)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight)
    (slotBounded : slotWeight ≤ 1) :
    ∃ residual : SourceProgram.BehavioralProfile checkpoint.residual.tail,
      let typed := cast (congrArg SourceProgram.BehavioralProfile reconstruct.symm) residual
      let embedding := cast (congrArg
        (fun program => OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
          program) reconstruct.symm) checkpoint.embedding
      let filled := fillCommitPrefix setup.program earlier
        (.commit name owner fresh guard (later.prepend suffix)) embedding
        execution.application.current.native.config.store checkpoint.source
      let current := earlier.tailProfile
        (.commit name owner fresh guard (later.prepend suffix)) typed
      let before := earlier.prefixLaw
        (.commit name owner fresh guard (later.prepend suffix)) typed checkpoint.source
      let complete := before.bind (fun config =>
        ((SourceProgram.CommitPrefix.commit name owner fresh guard later).prefixLaw suffix
          current config))
      let beforeView := fun view : DecisionView owner Ξ =>
        (later.entryView owner view).back true
      (filled.view owner ∈ (before.map (SourceProgram.Config.view owner)).support) ∧
        ∀ option : LateOption bounds.candidateCount,
          phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon scheduler
            wellFormed assessment 0 le_rfl (by norm_num) slotWeight slotNonnegative slotBounded
            owner (some (execution.recall owner,
              execution.observe (phaseApplication runtime leaks) owner)) option =
          (fiberPosterior (complete.map (SourceProgram.Config.view owner)) beforeView
            (filled.view owner)).bind (fun word =>
              (phaseCommitTimingWordStrategy setup mode runtime leaks bounds wellFormed assessment
                (earlier.append (.commit name owner fresh guard later))
                execution.application.attempt.phase execution.application.generation slotWeight
                slotNonnegative slotBounded initial horizon scheduler option owner word)
                (some (execution.recall owner,
                  execution.observe (phaseApplication runtime leaks) owner))) := by
  obtain ⟨residual, prediction⟩ := checkpoint.binding_timing_word_response_of_ready runtime leaks
    execution wellFormed assessment mixed fresh guard later suffix earlier reconstruct clear stored
    selected atEnd ready acting notPublication valid reachable retained saved bounds binding
      slotWeight
    slotNonnegative slotBounded
  refine ⟨residual, ?_⟩
  intro typed embedding filled current before complete beforeView
  obtain ⟨present, predicts⟩ := prediction
  refine ⟨present, ?_⟩
  have rank := checkpoint.compiled.rankEq selected
  have indexEq : (checkpoint.embedding.event selected).val -
      execution.application.attempt.phase = earlier.length := by
    rw [rank, Nat.add_sub_cancel_left, atEnd]
  have lengthBound : earlier.length <
      (earlier.append (.commit name owner fresh guard later)).length := by
    exact binding_before_block_end fresh guard earlier later
  have inside : execution.application.attempt.phase ≤ (checkpoint.embedding.event selected).val ∧
      (checkpoint.embedding.event selected).val < execution.application.attempt.phase +
        (earlier.append (.commit name owner fresh guard later)).length := by
    rw [rank, atEnd]
    omega
  have address : execution.application.attempt =
      ⟨execution.application.attempt.phase, execution.application.generation⟩ := by
    rfl
  intro option
  apply pmf_map_injective Subtype.val_injective
  rw [phaseSourceTimingComponent, mix_zero, mix_map,
    phaseSourceSlotStrategy_map_val setup mode runtime leaks bounds wellFormed assessment,
    phaseSourceTimingStrategy_map_val setup mode runtime leaks bounds wellFormed assessment,
    ← mix_map]
  rw [phaseSourceSlotPolicy_binding setup mode runtime leaks bounds wellFormed assessment execution
    applicationValid owner (checkpoint.embedding.event selected) payload binding request]
  rw [phaseSourceTimingPolicy_binding setup mode runtime leaks bounds wellFormed assessment option
    execution applicationValid owner (checkpoint.embedding.event selected) payload binding request]
  rw [predicts option]
  conv_lhs => rw [PMF.map_bind]
  conv_rhs => rw [PMF.map_bind]
  apply bind_congr_on_support
  intro word _supported
  rw [phaseCommitTimingWordStrategy_map_val]
  rw [phaseCommitTimingWordPolicy_binding setup mode runtime leaks bounds wellFormed assessment
    (earlier.append (.commit name owner fresh guard later)) execution.application.attempt.phase
    execution.application.generation slotWeight slotNonnegative slotBounded option owner word
      execution
    applicationValid (checkpoint.embedding.event selected) payload binding request inside address]
  simp only [indexEq]

end Vegas
