/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalTransition

/-! # Full source witnesses at selected drained phase checkpoints -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Attach the existing physical and archive invariants to the SAME selected
phase checkpoint, before the actual automatic normalization. -/
def RecoverySourceWitness.completed_phase_checkpoint
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {plan : RuntimePhasePlan (serviceGraph setup mode)}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (witness : RecoverySourceWitness setup mode plan state)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining)
    (finished : phase.Finished (phase.drain state.current))
    (next : RecoverySourceCheckpoint setup mode
      (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
        state.retired⟩ : PhaseRuntimeState (serviceGraph setup mode)))
    (aligned : next.ArchivedRecall) (chronology : next.PublicChronology plan)
    (origins : ArchivedSourceOrigins setup mode state.retired ⟨_, next.trace⟩) :
    RecoverySourceWitness setup mode plan
      (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
        state.retired⟩ : PhaseRuntimeState (serviceGraph setup mode)) := by
  let image := phase.drain state.current
  have member : phase ∈ state.phases.head? := by simp only [installed, List.head?_cons]; rfl
  have frontier := witness.receipts.exclusion.frontier
  have position := frontier.positioned
  rw [installed] at position
  have within := phase.drain_within state.current position.2
  have imagePrefix := phase.finished_prefix image within finished
  let inputs := witness.native.choose
  have native := witness.native.choose_spec
  have imageNative := phase.drain_invariant state.current native.active
  have imageBinding := phase.drain_bindingInvariant state.current witness.binding.active
  have imageRecord := (witness.receipts.exclusion.installed phase member).phase_drain phase
  have imageCoverage := witness.order.coverage.active.drain phase
  have imageArchived := witness.exclusions.active.phase_drain phase
  have adjacent := frontier.adjacent
  have last := frontier.last
  rw [installed] at adjacent last
  have nextPosition := PhaseRuntimeState.positioned_next phase remaining image adjacent last
    imagePrefix
  have nextFrontier : (⟨remaining, state.generation, image, image, state.retired⟩ :
      PhaseRuntimeState (serviceGraph setup mode)).Frontier :=
    ⟨nextPosition.adjacent, nextPosition.last, nextPosition.positioned⟩
  exact {
    checkpoint := next
    aligned := aligned
    chronology := chronology
    origins := origins
    native := ⟨inputs, imageNative, imageNative⟩
    binding := ⟨imageBinding, imageBinding, fun _ _ => rfl⟩
    receipts := PhaseRuntimeState.fresh_receiptRecord remaining state.generation image
      state.retired nextFrontier imageRecord.receipts
    stored := fun _ _ present => present
    remembered := ⟨[], by simp⟩
    order := PhaseRuntimeState.fresh_publicFailureOrder remaining state.generation image
      state.retired nextFrontier imageCoverage
    suffix := (List.suffix_cons phase remaining).trans (installed ▸ witness.suffix)
    archives := by
      intro record present
      have earlier := witness.archives record present
      have lower : state.attempt.phase = phase.low := by
        simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
          Option.getD_some]
      have later := PhaseRuntimeState.phaseLow_suffix adjacent
        (List.suffix_cons phase remaining)
      change record.attempt.phase ≤ PhaseRuntimeState.phaseLow remaining
      rw [lower] at earlier
      exact earlier.trans later
    exclusions := ⟨⟨imageCoverage, imageCoverage, Finset.Subset.refl _⟩,
      imageArchived, imageArchived⟩
    failures := State.PublicFailureExtension.refl _ }

end Vegas
