/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CommitRecoveryOmissionKernel
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.Joint
import Interaction.ReactiveProtocol

/-! # Accepted failure compared with actual domain choices

The two original commitment-window laws are coupled on their common omission
word. A failed close erases both attempts; a clean close checkpoints the
actual failed declaration and forces its owner's permanent exclusion payoff.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
theorem commitRecovery_joint_word_prefix
    {state : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace state)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal state joint)
    {target : setup.commitRecoveryProtocol.State}
    (realized : target ∈ (setup.commitRecoveryProtocol.step state ⟨joint, legal⟩).support)
    (later : setup.commitRecoveryProtocol.History)
    (kept : TracePrefix (prior.extend joint legal realized) later.trace) :
    ∃ added, setup.recoveryJointRecall later.trace =
      added ++ joint :: setup.recoveryJointRecall prior ∧
      later.trace.length = prior.length + 1 + added.length := by
  rcases later with ⟨laterState, laterTrace⟩
  dsimp only at kept ⊢
  induction kept with
  | refl => exact ⟨[], rfl, by simp only [Trace.length, List.length_nil, Nat.add_zero]⟩
  | @extend _ _ _ _ actual _ _ ih =>
      obtain ⟨added, word, length⟩ := ih
      refine ⟨actual :: added, ?_, ?_⟩
      · simp only [recoveryJointRecall, word, List.cons_append]
      · simp only [Trace.length, List.length_cons]
        omega

variable
  (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
  (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
  (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
    PMF (setup.CommitRecoveryValueChoice who info))

local notation "baseline" => setup.commitRecoveryNormalizedTrembledProfile omission
  omissionNonnegative omissionBounded bad badNonnegative badBounded values

end Vegas.SourceProgram.Setup
