/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFactorization
import GameTheoryExtensions.Analysis.Protocol.ProjectedBeliefTransport

/-! # Forced beliefs of the one-packet game are honest

Fix an information site of a player `who` in the one-packet game, a site of the
intended game, and a map `project` from the native site's histories to the
intended site's: the projection of a native history to the source history of
its committed values, draws and publications. Along a sequence of intended
assessments and native profiles, the inputs at stage `n` are
(`Vegas.ForcedBeliefInputs`):

* *Source weights.* At a regular history the source weight of
  `Vegas.othersSourceWeight` is the intended reach of the projection, divided
  by a positive constant of the site: the observer's own intended choice masses,
  which its recall fixes.
* *Common operational fibers.* The operational weights of the regular
  histories projecting to each intended history sum to one common mass. The
  scheduler and the observation rule read only operational data, and
  well-formed bindings carry no evidence and are opaque, so exchanging the
  other players' hidden values leaves the operational record unchanged. This
  needs that no reveal is pending at the site: a pending reveal puts its
  owner's opened value into the owner's late-delivery key, which the record
  carries.
* *Honest counterparts.* Every irregular history (a bad binding or a value
  outside the as-if-honest support of another player) has a regular
  counterpart at the same site: the same public record and slot, with each of
  the author's offending commitments replaced by an honest value. The irregular
  history has reach at most the cube of a scale times a common weight; the
  counterpart at least the square of the scale times a floor to the depth
  times that weight, up to a fixed slack. At a forced site nobody is publicly
  doomed, so such a counterpart exists.

The scale and the floor are parameters: the results hold for every scale
sequence negligible against the floor to the depth.

Each input quantifies only over what the proofs read: the regular histories
of the site, the irregular histories of the site, and the intended histories
of the intended site. The common fibers force every intended history of the
intended site to have regular preimages at the native site, which holds when
the two sites differ only in values hidden from `who`. The inputs are meant at
own-turn sites with no pending reveal; elsewhere the fibers need not be
common.

**Negligible irregular histories.** At each stage the reach of an irregular
history is at most `slack * scale / floor ^ depth` times the reach of its
counterpart (`Vegas.ForcedBeliefInputs.reach_le_counterpart`), so the irregular
reach is at most the number of the site's histories times that ratio times the
regular reach (`Vegas.ForcedBeliefInputs.irregular_reach_le`). When the scale is
negligible against the floor to the depth, this bound's factor vanishes
(`Vegas.tendsto_irregularRatio`).

**Honest beliefs.** With the uniform operational factorization of
`Vegas.onePacketReachFactorization`, under which the observer's own mass is
constant on a decision site (`Vegas.ownerRecall_eq_of_infoOf`), the native
Bayes belief pushed forward along `project` is within an explicit bound of the
intended Bayes belief at the same stage
(`Vegas.ForcedBeliefInputs.sum_abs_projectedBelief_sub_le`). The bound vanishes,
so the distance vanishes (`Vegas.tendsto_projectedBelief_sub`). The claims
concern the other players' values only: the observer's own commitments are
fixed by its information.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter Finset

section Scale

/-- **An irregular history against its counterpart.** A reach at most the cube
of the scale times a common weight is at most `slack * scale / floor ^ depth`
times a reach whose `slack` multiple is at least the square of the scale times
the floor to the depth times that weight. -/
theorem le_mul_of_tremble_counterpart {scale floor common reach other slack : ℝ} {depth : ℕ}
    (scaleNonneg : 0 ≤ scale) (floorPos : 0 < floor) (upper : reach ≤ scale ^ 3 * common)
    (lower : scale ^ 2 * floor ^ depth * common ≤ slack * other) :
    reach ≤ slack * scale / floor ^ depth * other := by
  have powerPos : 0 < floor ^ depth := pow_pos floorPos depth
  calc reach ≤ scale ^ 3 * common := upper
    _ = scale / floor ^ depth * (scale ^ 2 * floor ^ depth * common) := by
        field_simp
    _ ≤ scale / floor ^ depth * (slack * other) :=
        mul_le_mul_of_nonneg_left lower (div_nonneg scaleNonneg powerPos.le)
    _ = slack * scale / floor ^ depth * other := by ring

end Scale

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

omit [Fintype Player] in
/-- The observer's recall at every history of a decision site is the recall of
the site. -/
theorem ownerRecall_eq_of_infoOf {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {state : (application setup leaks).ProtocolState}
    (seen : (application setup leaks).observe who state = some (past, view)) :
    ownerRecall setup leaks who state = past := by
  cases state with
  | none => cases seen
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte, Option.some.injEq,
          Prod.mk.injEq] at seen
        exact seen.1
      · simp only [ReactiveApplication.observe, active, ↓reduceIte, reduceCtorEq] at seen

open Classical in
/-- **The inputs of honest forced beliefs at one stage.** For a site `site` of
`who` in the one-packet game, an intended site sourceSite at its projected
view, and the projection `project` of native histories to intended ones, at
stage `n` of the intended sequence `sequence`, the native profiles `profiles`
and the operational steps `steps`:

* `sourceWeight`: at every regular history, the source weight times the
  positive constant `sourceScale` is the intended reach of the projection;
* `fiber`: the operational weights of the regular histories projecting to each
  intended history sum to a common mass;
* `counterpart`: every irregular history has a regular counterpart; the
  irregular reach is at most `scale n ^ 3` times commonWeight, and `slack`
  times the counterpart's reach is at least `scale n ^ 2` times
  `floors n ^ depth` times commonWeight. -/
structure ForcedBeliefInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (profiles : ℕ → ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    {who : Player} (steps : OperationalSteps setup leaks bounds horizon scheduler sequence
      profiles who)
    (site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    (sourceSite : setup.intendedModel.InformationSite who)
    [Fintype ((onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1)]
    [DecidableEq (setup.intendedModel.InformationHistory who sourceSite.1)]
    (project : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1 → setup.intendedModel.InformationHistory who sourceSite.1)
    (scale floors : ℕ → ℝ) (depth : ℕ) (slack : ℝ) (n : ℕ) where
  /-- The site is forced for its owner. -/
  forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
    scheduler who site.1
  /-- The intended site is at the projected view. -/
  projected : sourceSite.1 = projectView setup leaks who site.1
  /-- The constant relating source weights to intended reach. -/
  sourceScale : ℝ
  sourceScale_pos : 0 < sourceScale
  sourceWeight : ∀ history, RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      history.1.trace →
    othersSourceWeight setup leaks bounds horizon scheduler (sequence n) who history.1.trace *
        sourceScale =
      (setup.intendedModel.historyReachWeight (sequence n).strategy (project history).1).toReal
  /-- The common operational mass of the fibers. -/
  fiberMass : ℝ
  fiber : ∀ point, ∑ history with RegularTrace setup leaks bounds horizon scheduler (sequence n)
      who history.1.trace ∧ project history = point,
    operationalWeight setup leaks who (steps.mass n)
      (operationalRecord setup leaks bounds horizon scheduler history.1.trace) = fiberMass
  /-- The honest counterpart of each irregular history. -/
  counterpart : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1 →
    (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who site.1
  /-- The weight common to an irregular history and its counterpart. -/
  commonWeight : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory
      who site.1 → ℝ
  counterpart_regular : ∀ history, ¬ RegularTrace setup leaks bounds horizon scheduler
      (sequence n) who history.1.trace →
    RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      (counterpart history).1.trace
  irregular_le : ∀ history, ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      history.1.trace →
    ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight (profiles n)
        history.1).toReal ≤
      scale n ^ 3 * commonWeight history
  counterpart_ge : ∀ history, ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n)
      who history.1.trace →
    scale n ^ 2 * floors n ^ depth * commonWeight history ≤
      slack * ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
        (profiles n) (counterpart history).1).toReal

variable {setup leaks bounds horizon scheduler}

section Stage

variable {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
  {profiles : ℕ → ∀ player,
    (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
  {who : Player}
  {steps : OperationalSteps setup leaks bounds horizon scheduler sequence profiles who}
  {site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
  {sourceSite : setup.intendedModel.InformationSite who}
  [Fintype ((onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
    site.1)]
  [DecidableEq (setup.intendedModel.InformationHistory who sourceSite.1)]
  {project : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
    site.1 → setup.intendedModel.InformationHistory who sourceSite.1}
  {scale floors : ℕ → ℝ} {depth : ℕ} {slack : ℝ} {n : ℕ}

open Classical in
/-- The ratio of the native reach of an irregular history to that of its
counterpart is at most `slack * scale / floor ^ depth`. -/
theorem ForcedBeliefInputs.reach_le_counterpart
    (inputs : ForcedBeliefInputs setup leaks bounds horizon scheduler sequence profiles steps site
      sourceSite project scale floors depth slack n)
    (floorPos : 0 < floors n) (scaleNonneg : 0 ≤ scale n)
    (history : (onePacketInformation setup leaks bounds horizon
      scheduler).InformationHistory who site.1)
    (irregular : ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      history.1.trace) :
    ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight (profiles n)
        history.1).toReal ≤
      slack * scale n / floors n ^ depth *
        ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
          (profiles n) (inputs.counterpart history).1).toReal :=
  le_mul_of_tremble_counterpart (scaleNonneg) floorPos
    (inputs.irregular_le history irregular) (inputs.counterpart_ge history irregular)

open Classical in
/-- The irregular reach is at most the number of the site's histories times
`slack * scale / floor ^ depth` times the regular reach. -/
theorem ForcedBeliefInputs.irregular_reach_le
    (inputs : ForcedBeliefInputs setup leaks bounds horizon scheduler sequence profiles steps site
      sourceSite project scale floors depth slack n)
    (floorPos : 0 < floors n) (scaleNonneg : 0 ≤ scale n) (slackNonneg : 0 ≤ slack) :
    ∑ history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who site.1 with ¬ RegularTrace setup leaks bounds horizon
          scheduler (sequence n) who history.1.trace,
      ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight (profiles n)
        history.1).toReal ≤
      (Fintype.card ((onePacketInformation setup leaks bounds horizon
          scheduler).InformationHistory who site.1) *
        (slack * scale n / floors n ^ depth)) *
      ∑ history : (onePacketInformation setup leaks bounds horizon
          scheduler).InformationHistory who site.1 with RegularTrace setup leaks bounds horizon
            scheduler (sequence n) who history.1.trace,
        ((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight
          (profiles n) history.1).toReal := by
  have bound := sum_reach_le_of_counterpart (profiles n)
    (fun history : (onePacketInformation setup leaks bounds horizon
      scheduler).InformationHistory who site.1 =>
      ¬ RegularTrace setup leaks bounds horizon scheduler (sequence n) who history.1.trace)
    inputs.counterpart
    (div_nonneg (mul_nonneg slackNonneg (scaleNonneg))
      (pow_nonneg floorPos.le _))
    (fun history irregular => not_not.mpr (inputs.counterpart_regular history irregular))
    fun history irregular => inputs.reach_le_counterpart floorPos scaleNonneg history irregular
  simpa only [not_not] using bound

/-- The operational weight of a regular history at stage `n`: its operational
weight times the observer's own mass at the site's recall, divided by the
source scale. -/
def ForcedBeliefInputs.projectedOperational
    (inputs : ForcedBeliefInputs setup leaks bounds horizon scheduler sequence profiles steps site
      sourceSite project scale floors depth slack n)
    (past : List (application setup leaks).PlayerEntry)
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1) : ℝ :=
  operationalWeight setup leaks who (steps.mass n)
      (operationalRecord setup leaks bounds horizon scheduler history.1.trace) *
    ownerMass setup leaks bounds horizon scheduler (profiles n who) past / inputs.sourceScale

theorem ForcedBeliefInputs.projectedOperational_nonneg
    (inputs : ForcedBeliefInputs setup leaks bounds horizon scheduler sequence profiles steps site
      sourceSite project scale floors depth slack n)
    (past : List (application setup leaks).PlayerEntry)
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1) :
    0 ≤ inputs.projectedOperational past history :=
  div_nonneg (mul_nonneg (operationalWeight_nonneg setup leaks (steps.mass_nonneg n) _)
    (ownerMassFrom_nonneg setup leaks bounds horizon scheduler _ _ _)) inputs.sourceScale_pos.le

/-- At a decision site with recall `past`, the factored weight of a regular
history is the intended reach of its projection times its projected
operational weight. -/
theorem ForcedBeliefInputs.factoredWeight_eq
    (inputs : ForcedBeliefInputs setup leaks bounds horizon scheduler sequence profiles steps site
      sourceSite project scale floors depth slack n)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (decision : site.1 = some (past, view))
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1)
    (regular : RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      history.1.trace) :
    factoredWeight sequence profiles steps n history.1.trace =
      (setup.intendedModel.historyReachWeight (sequence n).strategy (project history).1).toReal *
        inputs.projectedOperational past history := by
  have recalled : ownerRecall setup leaks who history.1.state = past := by
    apply ownerRecall_eq_of_infoOf setup leaks (view := view)
    rw [← onePacket_infoOf who history.1.trace, history.2, decision]
  unfold factoredWeight ForcedBeliefInputs.projectedOperational
  rw [recalled, ← inputs.sourceWeight history regular]
  field_simp [inputs.sourceScale_pos.ne']

/-- At a decision site, the regular reach at stage `n` is within the uniform
factorization error of the intended reach of the projection times the
projected operational weight. -/
theorem ForcedBeliefInputs.factor_close
    (inputs : ForcedBeliefInputs setup leaks bounds horizon scheduler sequence profiles steps site
      sourceSite project scale floors depth slack n)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (decision : site.1 = some (past, view))
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1)
    (regular : RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      history.1.trace) :
    |((onePacketInformation setup leaks bounds horizon scheduler).historyReachWeight (profiles n)
        history.1).toReal -
      (setup.intendedModel.historyReachWeight (sequence n).strategy (project history).1).toReal *
        inputs.projectedOperational past history| ≤
      ((1 + steps.error n) ^ (2 * horizon + 1) - 1) *
        ((setup.intendedModel.historyReachWeight (sequence n).strategy
          (project history).1).toReal * inputs.projectedOperational past history) := by
  rw [← inputs.factoredWeight_eq decision history regular]
  exact (onePacketReachFactorization steps).2 n history.1.trace regular

open Classical in
/-- The projected operational weights of each fiber sum to the common mass
times the observer's own mass divided by the source scale. -/
theorem ForcedBeliefInputs.fiber_sum
    (inputs : ForcedBeliefInputs setup leaks bounds horizon scheduler sequence profiles steps site
      sourceSite project scale floors depth slack n)
    (past : List (application setup leaks).PlayerEntry)
    (point : setup.intendedModel.InformationHistory who sourceSite.1) :
    ∑ history with RegularTrace setup leaks bounds horizon scheduler (sequence n) who
        history.1.trace ∧ project history = point,
      inputs.projectedOperational past history =
    inputs.fiberMass * ownerMass setup leaks bounds horizon scheduler (profiles n who) past /
      inputs.sourceScale := by
  unfold ForcedBeliefInputs.projectedOperational
  rw [← sum_div, ← sum_mul, inputs.fiber point]

open Classical in
theorem ForcedBeliefInputs.fiberMass_nonneg
    (inputs : ForcedBeliefInputs setup leaks bounds horizon scheduler sequence profiles steps site
      sourceSite project scale floors depth slack n) :
    0 ≤ inputs.fiberMass := by
  obtain ⟨point, _⟩ := sourceSite.2
  rw [← inputs.fiber point]
  exact sum_nonneg fun _ _ => operationalWeight_nonneg setup leaks (steps.mass_nonneg n) _

open Classical in
/-- **Honest beliefs at one stage.** At a decision site of `who` with recall
`past`, under a Bayes consistent native assessment playing the stage-`n` profile
and a Bayes consistent intended assessment at stage `n`, both at sites of
positive mass, the native belief pushed forward along `project` is within
`projectionErrorBound` of the factorization error, zero, and the irregular
ratio of the intended belief, in `ℓ¹`. -/
theorem ForcedBeliefInputs.sum_abs_projectedBelief_sub_le
    [Fintype (setup.intendedModel.InformationHistory who sourceSite.1)]
    (inputs : ForcedBeliefInputs setup leaks bounds horizon scheduler sequence profiles steps site
      sourceSite project scale floors depth slack n)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (decision : site.1 = some (past, view))
    {target : (onePacketInformation setup leaks bounds horizon scheduler).BehavioralAssessment}
    {antichain : (onePacketInformation setup leaks bounds horizon
      scheduler).DecisionInformationAntichain}
    {sourceAntichain : setup.intendedModel.DecisionInformationAntichain}
    (played : target.strategy = profiles n)
    (bayes : BehavioralAssessment.IsBayesConsistent _ target antichain)
    (sourceBayes : BehavioralAssessment.IsBayesConsistent _ (sequence n) sourceAntichain)
    (positive : 0 < (onePacketInformation setup leaks bounds horizon scheduler).informationMass
      target.strategy who site)
    (sourcePositive : 0 < setup.intendedModel.informationMass (sequence n).strategy who sourceSite)
    (floorPos : 0 < floors n) (scaleNonneg : 0 ≤ scale n) (slackNonneg : 0 ≤ slack)
    (factorSmall : (1 + steps.error n) ^ (2 * horizon + 1) - 1 < 1) :
    ∑ point, |(((target.belief who site).map project) point).toReal -
        ((sequence n).belief who sourceSite point).toReal| ≤
      projectionErrorBound ((1 + steps.error n) ^ (2 * horizon + 1) - 1) 0
        (Fintype.card ((onePacketInformation setup leaks bounds horizon
            scheduler).InformationHistory who site.1) *
          (slack * scale n / floors n ^ depth)) := by
  have factorNonneg : 0 ≤ (1 + steps.error n) ^ (2 * horizon + 1) - 1 := by
    have := one_le_pow₀ (n := 2 * horizon + 1)
      (show (1 : ℝ) ≤ 1 + steps.error n by linarith [steps.error_nonneg n])
    linarith
  refine InformationModel.sum_abs_projectedBelief_sub_le bayes sourceBayes positive
    sourcePositive project
    (fun history => RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      history.1.trace)
    (inputs.projectedOperational past)
    (inputs.fiberMass * ownerMass setup leaks bounds horizon scheduler (profiles n who) past /
      inputs.sourceScale)
    (inputs.projectedOperational_nonneg past)
    (div_nonneg (mul_nonneg inputs.fiberMass_nonneg
      (ownerMassFrom_nonneg setup leaks bounds horizon scheduler _ _ _))
      inputs.sourceScale_pos.le)
    factorNonneg factorSmall le_rfl (by norm_num) (fun history regular => ?_)
    (fun point => ?_) ?_
  · rw [played]
    exact inputs.factor_close decision history regular
  · rw [inputs.fiber_sum past point, sub_self, abs_zero, zero_mul]
  · rw [played]
    exact inputs.irregular_reach_le floorPos scaleNonneg slackNonneg

end Stage

section Sequence

variable {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
  {profiles : ℕ → ∀ player,
    (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player}
  {who : Player}
  {steps : OperationalSteps setup leaks bounds horizon scheduler sequence profiles who}
  {site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
  {sourceSite : setup.intendedModel.InformationSite who}
  [Fintype ((onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
    site.1)]
  [DecidableEq (setup.intendedModel.InformationHistory who sourceSite.1)]
  {project : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
    site.1 → setup.intendedModel.InformationHistory who sourceSite.1}
  {scale floors : ℕ → ℝ} {depth : ℕ} {slack : ℝ}

/-- The irregular ratio vanishes along floors in `(0, 1]`. -/
theorem tendsto_irregularRatio
    (negligible : Tendsto (fun n => scale n / floors n ^ depth) atTop (nhds 0)) (count : ℕ) :
    Tendsto (fun n => (count : ℝ) * (slack * scale n / floors n ^ depth)) atTop (nhds 0) := by
  have limit := (negligible.const_mul slack).const_mul (count : ℝ)
  simp only [mul_zero] at limit
  refine limit.congr fun n => ?_
  ring

open Classical in
/-- **Honest forced beliefs.** At a decision site of `who`, along native
assessments playing the native profiles and intended assessments of the
intended sequence, all fully mixed and Bayes consistent, with the inputs at
every stage and floors in `(0, 1]`, the native beliefs pushed forward along
`project` approach the intended beliefs in `ℓ¹`. -/
theorem tendsto_projectedBelief_sub [Fintype (setup.intendedModel.InformationHistory who
      sourceSite.1)]
    (inputs : ∀ n, ForcedBeliefInputs setup leaks bounds horizon scheduler sequence profiles steps
      site sourceSite project scale floors depth slack n)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (decision : site.1 = some (past, view))
    {targetSequence : ℕ →
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralAssessment}
    {antichain : (onePacketInformation setup leaks bounds horizon
      scheduler).DecisionInformationAntichain}
    {sourceAntichain : setup.intendedModel.DecisionInformationAntichain}
    (played : ∀ n, (targetSequence n).strategy = profiles n)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent _ (targetSequence n) antichain)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent _ (sequence n) sourceAntichain)
    (positive : ∀ n, 0 < floors n) (scaleNonneg : ∀ n, 0 ≤ scale n)
    (negligible : Tendsto (fun n => scale n / floors n ^ depth) atTop (nhds 0))
    (slackNonneg : 0 ≤ slack) :
    Tendsto (fun n => ∑ point, |((((targetSequence n).belief who site).map project)
        point).toReal - ((sequence n).belief who sourceSite point).toReal|) atTop (nhds 0) :=
  InformationModel.tendsto_sum_abs_projectedBelief_sub bayes sourceBayes
    (fun n => InformationModel.informationMass_pos_of_fullSupport _ _ (mixed n) who site)
    (fun n => InformationModel.informationMass_pos_of_fullSupport _ _ (sourceMixed n) who
      sourceSite)
    project
    (fun n history => RegularTrace setup leaks bounds horizon scheduler (sequence n) who
      history.1.trace)
    (fun n => (inputs n).projectedOperational past)
    (fun n => (inputs n).fiberMass *
      ownerMass setup leaks bounds horizon scheduler (profiles n who) past / (inputs n).sourceScale)
    (fun n => (inputs n).projectedOperational_nonneg past)
    (fun n => div_nonneg (mul_nonneg (inputs n).fiberMass_nonneg
      (ownerMassFrom_nonneg setup leaks bounds horizon scheduler _ _ _))
      (inputs n).sourceScale_pos.le)
    (fun n => by
      have := one_le_pow₀ (n := 2 * horizon + 1)
        (show (1 : ℝ) ≤ 1 + steps.error n by linarith [steps.error_nonneg n])
      linarith)
    (fun _ => le_rfl) (onePacketReachFactorization steps).1 tendsto_const_nhds
    (tendsto_irregularRatio negligible _)
    (fun n history regular => by
      rw [played n]
      exact (inputs n).factor_close decision history regular)
    (fun n point => by rw [(inputs n).fiber_sum past point, sub_self, abs_zero, zero_mul])
    (fun n => by
      rw [played n]
      exact (inputs n).irregular_reach_le (positive n) (scaleNonneg n) slackNonneg)

end Sequence

end Vegas
