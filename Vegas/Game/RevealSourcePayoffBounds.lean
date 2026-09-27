/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealSourceContinuation
import Vegas.Game.RevealServiceMixing
import GameTheoryExtensions.Analysis.FinitePayoffBounds

/-! # A uniform payoff range over actual source continuations

The bound ranges over legal finite source histories. The source state carrier
and utility function need not be globally bounded. It applies to every source
assessment, including off-path beliefs, and every legal continuation policy.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Finite Player]
  {L : IExpr} [IExpr.ResultTypes L]

open Classical in
theorem reveal_boolean_value_range
    (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (reveals : setup.program.RevealOnly)
    (utility : State L setup.program.terminalCtx → Player → ℝ) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ (assessment : (setup.informationModel admission).BehavioralAssessment)
        (who : Player) (site : (setup.informationModel admission).InformationSite who)
        (joint : Bool → Player → Option (OwnAction Player L))
        (_chosen : ∀ disclose, OwnAction.disclosure (joint disclose who) = disclose),
        let value := fun disclose => (assessment.stateBelief who site).expect (fun state =>
          ((setup.protocolStep state (joint disclose)).bind (setup.continuationLaw
            (setup.decodeBehavioralProfile admission assessment.strategy))).expect
              (fun final => utility final who))
        |value true - value false| ≤ bound := by
  let _ := Fintype.ofFinite Player
  let _ := setup.reveal_finite_history reveals admission
  let _ := Fintype.ofFinite (setup.executionProtocol admission).History
  let _ : Nonempty (setup.executionProtocol admission).History :=
    ⟨(setup.executionProtocol admission).initHistory⟩
  let payoff := fun who (history : (setup.executionProtocol admission).History) =>
    (setup.protocolReadout history.state).elim 0 (fun final => utility final who)
  let lower := fun who => FinitePayoffBounds.lower (payoff who)
  let upper := fun who => FinitePayoffBounds.upper (payoff who)
  let range := fun who => upper who - lower who
  have nonnegative (who : Player) : 0 ≤ range who :=
    sub_nonneg.mpr (FinitePayoffBounds.lower_le_upper (payoff who))
  refine ⟨∑ who, range who, Finset.sum_nonneg (fun who _ => nonnegative who), ?_⟩
  intro assessment who site joint chosen value
  have valueBound (disclose : Bool) : lower who ≤ value disclose ∧ value disclose ≤ upper who := by
    have full := setup.reveal_choice_fullSupport reveals admission
      (setup.revealReference reveals admission) (setup.revealReference_fullyMixed reveals admission)
      who site
    obtain ⟨choice, _, same⟩ := FinDist.support_map .. ▸ full disclose
    have equal := setup.reveal_local_value admission reveals assessment who site
      (FinDist.pure choice) joint chosen (fun final => utility final who)
    simp only [FinDist.map_pure, FinDist.expect_pure, same] at equal
    change _ = value disclose at equal
    rw [← equal, InformationModel.BehavioralAssessment.continuationContext_value]
    constructor
    · rw [← FinDist.expect_const _ (lower who)]
      apply FinDist.expect_mono
      intro history _
      exact FinitePayoffBounds.lower_le (payoff who) history
    · rw [← FinDist.expect_const _ (upper who)]
      apply FinDist.expect_mono
      intro history _
      exact FinitePayoffBounds.le_upper (payoff who) history
  have first := valueBound true
  have second := valueBound false
  have difference : |value true - value false| ≤ range who := by
    rw [abs_le]
    dsimp only [range]
    constructor <;> linarith
  exact difference.trans (Finset.single_le_sum (fun player _ => nonnegative player)
    (Finset.mem_univ who))

end Vegas.SourceProgram.Setup
