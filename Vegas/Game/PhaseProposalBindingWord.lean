/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitPrefixReadStability
import Vegas.Source.CommitRecoveryInstructions
import Vegas.EventGraph.SchedulerErasure
import Vegas.EventGraph.SequentialLaw

/-! # The current binding word as a readout of the emission frontier

The filled configuration supplies a typed word selector only. Excluded owners
contribute literal absent joints; its registry and private history are not
claimed to be the runtime's automatically drained source configuration.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
  (whole : SourceProgram Player L wholeΓ wholeO)
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- Read the current addressed source instructions, retaining one automatic
NONE instruction at every already excluded owner's coordinate. -/
def phaseProposalBindingWord (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (excluded : Finset Player)
    (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ) :
    List (Player → Option (CommitRecoveryMove Player L)) :=
  (List.range block.length).map fun index who =>
    if who ∈ excluded then none else
      (block.wordAction who index
        ((fillCommitPrefix whole block suffix embedding store entry).view who)).map
          (fun action => ⟨action, false⟩)

/-- No source word of an excluded owner is synthesized from a latent filled
cell. Its automatic absent joints are fixed by the block-entry exclusions. -/
theorem phaseProposalBindingWord_excluded (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (excluded : Finset Player)
    (store : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
    (who : Player) (inactive : who ∈ excluded) :
    (phaseProposalBindingWord whole block suffix embedding excluded store entry).map
        (fun joint => joint who) = List.replicate block.length none := by
  simp only [phaseProposalBindingWord, List.map_map, Function.comp_def, inactive, ↓reduceIte]
  simp

/-- Equal current binding fields of surviving owners give the same complete
addressed word. Foreign history, output order, and outside fields are irrelevant
to this readout; the source reconstruction itself still uses actual joints. -/
theorem phaseProposalBindingWord_congr (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (excluded : Finset Player)
    (first second : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
    (same : ∀ who ∉ excluded,
      ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
        eventOwner? (block.prepend suffix) index = some who →
          (embedding.ref index).get? first = (embedding.ref index).get? second) :
    phaseProposalBindingWord whole block suffix embedding excluded first entry =
      phaseProposalBindingWord whole block suffix embedding excluded second entry := by
  unfold phaseProposalBindingWord
  apply List.map_congr_left
  intro index _inside
  funext who
  by_cases inactive : who ∈ excluded
  · simp only [inactive, ↓reduceIte]
  · simp only [inactive, ↓reduceIte]
    have views := fillCommitPrefix_view_congr whole block suffix embedding first second
      entry entry who rfl (same who inactive)
    rw [views]

/-- Once the current ordinary bindings are present, later graph evaluation
cannot alter their addressed source word. This includes arbitrary synthetic
outside-interval completion used by the continuation potential. -/
theorem phaseProposalBindingWord_of_extension (block : CommitPrefix Γ O Δ P)
    (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (excluded : Finset Player)
    (first second : Store (graphLayout whole)) (entry : SourceProgram.Config Player L Γ)
    (preserved : ∀ field value, first field = some value → second field = some value)
    (available : ∀ who ∉ excluded,
      ∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
        eventOwner? (block.prepend suffix) index = some who →
          ((embedding.ref index).get? first).isSome = true) :
    phaseProposalBindingWord whole block suffix embedding excluded first entry =
      phaseProposalBindingWord whole block suffix embedding excluded second entry := by
  apply phaseProposalBindingWord_congr whole block suffix embedding excluded first second entry
  intro who active index inside owned
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
    (available who active index inside owned)
  exact stored.trans ((embedding.ref index).get?_preserved first second preserved value stored).symm

/-- An arbitrary remaining graph plan has a point-mass current-word readout
once this interval is complete. Consequently dummy continuation actions never
become actual runtime exclusions or source failure controls. -/
theorem phaseProposalBindingWord_runPlan (mode : ExecutionMode)
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout wholeΓ) (outputLayout whole)
      (block.prepend suffix)) (excluded : Finset Player)
    (entry : SourceProgram.Config Player L Γ)
    (plan : ((toEventGraph whole).withMode mode).EventPlan) :
    ∀ fuel (config : ((toEventGraph whole).withMode mode).Config),
      (∀ index : Fin (eventCount (block.prepend suffix)), index.val < block.length →
        embedding.event index ∈ config.cut.completed) →
      (((toEventGraph whole).withMode mode).runPlan plan fuel config).map
          (fun next => phaseProposalBindingWord whole block suffix embedding excluded
            next.store entry) =
        PMF.pure (phaseProposalBindingWord whole block suffix embedding excluded config.store
          entry) := by
  intro fuel
  induction fuel with
  | zero =>
      intro config _completed
      simp only [EventGraph.runPlan, PMF.pure_map]
  | succ fuel ih =>
    intro config completed
    rw [EventGraph.runPlan]
    split
    · simp only [PMF.pure_map]
    · simp only [PMF.map_bind]
      calc
        _ = (plan config _).bind (fun choice =>
            (config.step choice.1.1 choice.1.2 choice.2).bind (fun _ =>
              PMF.pure (phaseProposalBindingWord whole block suffix embedding excluded
                config.store entry))) := by
          apply bind_congr_on_support _
          intro choice _selected
          apply bind_congr_on_support _
          intro next supported
          have later : ∀ index : Fin (eventCount (block.prepend suffix)),
              index.val < block.length → embedding.event index ∈ next.cut.completed := by
            intro index inside
            rw [config.step_cut _ choice.1.2 choice.2 next supported]
            exact Finset.mem_insert.mpr (Or.inr (completed index inside))
          rw [ih next later]
          apply congrArg PMF.pure
          symm
          apply phaseProposalBindingWord_of_extension whole block suffix embedding excluded
            config.store next.store entry
          · exact config.step_store_of_some next _ choice.1.2 choice.2 supported
          · intro who _active index inside _owned
            apply (embedding.ref index).get?_isSome
            change (config.store (.inr (embedding.event index))).isSome = true
            rw [Config.store_output, config.output_available]
            exact completed index inside
        _ = _ := by simp only [PMF.bind_const]

end Vegas
