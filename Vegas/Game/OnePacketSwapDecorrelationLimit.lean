/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSwapDecorrelation

/-! # Vanishing decorrelation along a sequence

Every law decorrelates any record and hidden part up to two
(`Vegas.beliefDecorrelated_two`). Along a sequence of stages with the
forced-belief inputs at every stage, the explicit bound of
`Vegas.ForcedBeliefInputs.beliefDecorrelated` vanishes with the factorization
error and the irregular ratio, so the beliefs at an own-turn site decorrelate the
operational record from the decoded point up to a vanishing bound
(`Vegas.tendsto_beliefDecorrelated`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

/-- **Every law decorrelates up to two.** -/
theorem beliefDecorrelated_two {H R T : Type*} (law : PMF H) (record : H → R)
    (hidden : H → T) : BeliefDecorrelated law record hidden 2 := by
  intro first second firstBounded secondBounded
  have product : |expect law fun h => first (record h) * second (hidden h)| ≤ 1 :=
    expect_abs_le_of_bounded zero_le_one fun h => by
      rw [abs_mul]
      exact (mul_le_mul (firstBounded _) (secondBounded _) (abs_nonneg _) zero_le_one).trans_eq
        (one_mul 1)
  have firstExpect : |expect law fun h => first (record h)| ≤ 1 :=
    expect_abs_le_of_bounded zero_le_one fun h => firstBounded _
  have secondExpect : |expect law fun h => second (hidden h)| ≤ 1 :=
    expect_abs_le_of_bounded zero_le_one fun h => secondBounded _
  have both : |(expect law fun h => first (record h)) * expect law fun h => second (hidden h)| ≤
      1 := by
    rw [abs_mul]
    exact (mul_le_mul firstExpect secondExpect (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  calc _ ≤ |expect law fun h => first (record h) * second (hidden h)| +
        |(expect law fun h => first (record h)) * expect law fun h => second (hidden h)| :=
        abs_sub _ _
    _ ≤ 2 := by linarith

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)} [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  {who : Player}
  {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
  {sourceSite : setup.intendedModel.InformationSite who}
  {past : List (application setup runtime leaks).PlayerEntry} {view : (application setup runtime
    leaks).PlayerView}
  {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
  {profiles : ℕ → ∀ player,
    (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player}
  {steps : OperationalSteps setup runtime leaks bounds horizon scheduler sequence profiles who}
  [Fintype ((onePacketInformation setup runtime leaks bounds horizon scheduler).InformationHistory
    who
    site.1)]
  [DecidableEq (setup.intendedModel.InformationHistory who sourceSite.1)]
  {scale floors : ℕ → ℝ} {depth : ℕ} {slack : ℝ}

open Classical in
/-- **Vanishing decorrelation at an own turn.** Along native assessments playing
the native profiles, fully mixed and Bayes consistent, with the forced-belief
inputs, own completions intended and a fully mixed intended assessment at every
stage, floors positive and the scale negligible against the floor to the depth,
the beliefs at an own-turn site decorrelate the operational record from the
decoded point up to a vanishing bound. -/
theorem tendsto_beliefDecorrelated
    [Finite (setup.intendedModel.InformationHistory who sourceSite.1)]
    (wellFormed : setup.WellFormed) (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup runtime leaks who site.1)
    (inputs : ∀ n, ForcedBeliefInputs setup runtime leaks bounds horizon scheduler sequence
      profiles steps
      site sourceSite (replayProjection setup runtime leaks bounds horizon scheduler sourceSite site
        decision projected) scale floors depth slack n)
    (ownIntended : ∀ n, ∀ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1,
      RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who history.1.trace →
      OwnCompletionsIntended (runtime := runtime) (bounds := bounds) (horizon := horizon)
        (scheduler := scheduler)
        who history.1.trace)
    (mixed : ∀ n, (sequence n).IsFullyMixed) {event : (graph setup).EventId}
    (turn : view.application.publicView.ownTurn? who = some event)
    (covered : BindingFieldsCovered bounds)
    {targetSequence : ℕ →
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralAssessment}
    {antichain : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).DecisionInformationAntichain}
    (played : ∀ n, (targetSequence n).strategy = profiles n)
    (targetMixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent _ (targetSequence n) antichain)
    (floorPos : ∀ n, 0 < floors n) (scaleNonneg : ∀ n, 0 ≤ scale n)
    (negligible : Tendsto (fun n => scale n / floors n ^ depth) atTop (nhds 0))
    (slackNonneg : 0 ≤ slack) :
    ∃ bound : ℕ → ℝ, Tendsto bound atTop (nhds 0) ∧ ∀ n,
      BeliefDecorrelated ((targetSequence n).belief who site)
        (fun history => operationalRecord setup runtime leaks bounds horizon scheduler
          history.1.trace)
        (fun history => nativeDecodedState setup runtime leaks history.1.state) (bound n) := by
  set error := fun n => (1 + steps.error n) ^ (2 * horizon + 1) - 1 with
    errorEq
  set ratio := fun n => (Fintype.card ((onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who site.1) : ℝ) * (slack * scale n / floors n ^ depth)
    with ratioEq
  have errorLimit : Tendsto error atTop (nhds 0) := (onePacketReachFactorization (runtime :=
    runtime) steps).1
  have ratioLimit : Tendsto ratio atTop (nhds 0) := tendsto_irregularRatio negligible _
  let formula := fun n => 3 * (2 * (error n + ratio n * (1 + error n)) / (1 - error n))
  have formulaLimit : Tendsto formula atTop (nhds 0) := by
    have numerator : Tendsto (fun n => 2 * (error n + ratio n * (1 + error n))) atTop
        (nhds (2 * (0 + 0 * (1 + 0)))) :=
      (errorLimit.add (ratioLimit.mul (tendsto_const_nhds.add errorLimit))).const_mul 2
    have denominator : Tendsto (fun n => 1 - error n) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub errorLimit
    have quotient := (numerator.div denominator (by norm_num)).const_mul 3
    simp only [add_zero, zero_mul, mul_zero, sub_zero, zero_div] at quotient
    exact quotient
  have small : ∀ᶠ n in atTop, error n < 1 :=
    errorLimit.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  refine ⟨fun n => if error n < 1 then formula n else 2, ?_, fun n => ?_⟩
  · refine formulaLimit.congr' ?_
    filter_upwards [small] with n smallAt
    simp only [smallAt, ↓reduceIte]
  · by_cases smallAt : error n < 1
    · simp only [smallAt, ↓reduceIte]
      exact (inputs n).beliefDecorrelated wellFormed decision projected
        (ownIntended n)
        (mixed n) turn covered (played n) (bayes n)
        (InformationModel.informationMass_pos_of_fullSupport _ _ (targetMixed n) who site)
        (floorPos n) (scaleNonneg n) slackNonneg smallAt
    · simp only [smallAt, ↓reduceIte]
      exact beliefDecorrelated_two _ _ _

end Vegas
