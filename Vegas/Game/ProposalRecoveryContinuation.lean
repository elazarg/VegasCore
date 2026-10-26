/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryEvolution
import GameTheoryExtensions.Analysis.Protocol.StoppedKernelComparison
import GameTheory.Math.Probability.Conditioning

/-! # Complete stopped source laws with retained proposal disclosures -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

private theorem oneStep_coupled
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (normalized : ∀ who first second,
      setup.proposalRecoveryQuery who first = setup.proposalRecoveryQuery who second →
        (profile who first).map Subtype.val = (profile who second).map Subtype.val)
    (first second : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryErasedHistory first =
      setup.proposalRecoveryErasedHistory second)
    (running : ¬ setup.proposalRecoveryProtocol.terminal first.state) :
    ∃ joint : PMF (setup.proposalRecoveryProtocol.History ×
        setup.proposalRecoveryProtocol.History),
      joint.map Prod.fst = setup.proposalRecoveryModel.runBehavioralFrom profile 1 first ∧
      joint.map Prod.snd = setup.proposalRecoveryModel.runBehavioralFrom profile 1 second ∧
      ∀ next ∈ joint.support, setup.proposalRecoveryErasedHistory next.1 =
        setup.proposalRecoveryErasedHistory next.2 := by
  let left := setup.proposalRecoveryModel.runBehavioralFrom profile 1 first
  let right := setup.proposalRecoveryModel.runBehavioralFrom profile 1 second
  let read := setup.proposalRecoveryErasedHistory
  have images : left.map read = right.map read :=
    setup.proposalRecovery_oneStep_erased_eq profile normalized first second same running
  let joint := left.bind fun prior =>
    (fiberPosterior right read (read prior)).map fun later => (prior, later)
  refine ⟨joint, ?_, ?_, ?_⟩
  · change (left.bind fun prior =>
      (fiberPosterior right read (read prior)).map fun later => (prior, later)).map Prod.fst = left
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    change (left.bind fun prior =>
      (fiberPosterior right read (read prior)).map (Function.const _ prior)) = left
    simp only [PMF.map_const, PMF.bind_pure]
  · change (left.bind fun prior =>
      (fiberPosterior right read (read prior)).map fun later => (prior, later)).map Prod.snd = right
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    change (left.bind fun prior =>
      (fiberPosterior right read (read prior)).map id) = right
    simp only [PMF.map_id]
    change left.bind (fiberPosterior right read ∘ read) = right
    rw [← PMF.bind_map, images, fiberPosterior_reconstruct]
  · intro next supported
    obtain ⟨prior, priorSupport, laterSupport⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
    obtain ⟨later, fiberSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp laterSupport
    have observed : read prior ∈ (right.map read).support := by
      rw [← images]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨prior, priorSupport, rfl⟩
    exact (mem_support_fiberPosterior observed fiberSupport).1.symm

/-- Existing stopped-kernel comparison applied to the actual one-step laws.
No boundary posterior or terminal continuation law is an input. -/
theorem proposalRecovery_runUntil_erased_eq
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (normalized : ∀ who first second,
      setup.proposalRecoveryQuery who first = setup.proposalRecoveryQuery who second →
        (profile who first).map Subtype.val = (profile who second).map Subtype.val)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (stopped : setup.ProposalRecoveryHistoryImage → Prop)
    (first second : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryErasedHistory first =
      setup.proposalRecoveryErasedHistory second) :
    (setup.proposalRecoveryModel.runBehavioralUntil certificate profile
        (stopped ∘ setup.proposalRecoveryErasedHistory) first).map
        setup.proposalRecoveryErasedHistory =
      (setup.proposalRecoveryModel.runBehavioralUntil certificate profile
        (stopped ∘ setup.proposalRecoveryErasedHistory) second).map
        setup.proposalRecoveryErasedHistory := by
  apply setup.proposalRecoveryModel.runBehavioralUntil_map_eq_of_paired_steps
    setup.proposalRecoveryModel certificate certificate profile profile
    (stopped ∘ setup.proposalRecoveryErasedHistory)
    (stopped ∘ setup.proposalRecoveryErasedHistory)
    setup.proposalRecoveryErasedHistory setup.proposalRecoveryErasedHistory
    (fun left right => setup.proposalRecoveryErasedHistory left =
      setup.proposalRecoveryErasedHistory right) ?_ ?_ ?_ first second same
  · intro left right equal
    have terminal := setup.commitRecovery_terminal_eq_of_erased
      (congrArg Prod.fst (congrArg Prod.fst equal))
    change (stopped (setup.proposalRecoveryErasedHistory left) ∨
      setup.commitRecoveryProtocol.terminal left.state) ↔
        (stopped (setup.proposalRecoveryErasedHistory right) ∨
          setup.commitRecoveryProtocol.terminal right.state)
    rw [equal]
    exact or_congr Iff.rfl terminal
  · intro left right equal _halt
    exact equal
  · intro left right equal _going running
    exact setup.oneStep_coupled profile normalized left right equal running

/-- The full terminal semantic state, erased information and all actual
proposal deltas have the same joint law under the selected prescription. -/
theorem proposalRecovery_terminal_erased_eq
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (normalized : ∀ who first second,
      setup.proposalRecoveryQuery who first = setup.proposalRecoveryQuery who second →
        (profile who first).map Subtype.val = (profile who second).map Subtype.val)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (first second : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryErasedHistory first =
      setup.proposalRecoveryErasedHistory second) :
    (setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate profile first).map
        setup.proposalRecoveryErasedHistory =
      (setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate profile second).map
        setup.proposalRecoveryErasedHistory := by
  have law := setup.proposalRecovery_runUntil_erased_eq profile normalized certificate
    (fun _ => False) first second same
  simpa only [Function.comp_def,
    ← setup.proposalRecoveryModel.runBehavioralTerminalFrom_eq_until_false] using law

end Vegas.SourceProgram.Setup
