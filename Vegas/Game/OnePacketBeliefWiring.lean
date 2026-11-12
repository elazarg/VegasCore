module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketForcedRegular
public import Vegas.Game.OnePacketProjectedDecision
public import Vegas.Game.OnePacketLateSuccess
public import Vegas.Game.OnePacketSequentialPreservation
public import Vegas.Game.OnePacketSlotLawForced

@[expose] public section

/-! # The operational side of the forced-belief inputs

Operational steps depend on their profiles only through their properties, so
steps for one profile sequence are steps for every sequence equal to it
(`Vegas.OperationalSteps.ofProfilesEq`), with the same masses. Profiles
assembled from the certificate's components are the certificate's profiles,
so at the tremble scale over the combined floor the certificate's operational
steps are steps of every assembled sequence
(`Vegas.assembledOperationalSteps`). The tremble scale is negligible against
the combined floor to the depth (`Vegas.tendsto_trembleScale_div_pow`). This
fixes the operational steps, scale, floors and depth of
`Vegas.OnePacketBeliefInputs` (`Vegas.OnePacketBeliefInputs.ofCertificate`),
leaving the intended own completions, the fibers and the honest counterparts as
inputs.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- Operational steps of one profile sequence are operational steps of every
sequence equal to it, with the same masses and errors. -/
def OperationalSteps.ofProfilesEq {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles other : ℕ → ∀ player,
      (onePacketInformation setup timeouts leaks bounds horizon scheduler).BehavioralPolicy player}
    {who : Player} (steps : OperationalSteps setup timeouts leaks bounds horizon scheduler sequence
      profiles who)
    (same : ∀ n, other n = profiles n) :
    OperationalSteps setup timeouts leaks bounds horizon scheduler sequence other who where
  mass := steps.mass
  error := steps.error
  mass_nonneg := steps.mass_nonneg
  error_nonneg := steps.error_nonneg
  error_tendsto := steps.error_tendsto
  environment n := by
    rw [same n]
    exact steps.environment n
  component n := by
    rw [same n]
    exact steps.component n

variable [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  [Finite setup.intendedProtocol.History]

local notation "onePacketN" =>
  onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon scheduler

section BeliefInputs

variable (setup timeouts leaks bounds horizon scheduler)

/-- A site at which `who` owes no failure at the decoded point of any history. -/
def SiteDebtFree {who : Player} (site : (onePacketN).InformationSite who) : Prop :=
  ∀ history : (onePacketN).InformationHistory who site.1,
    ∀ point, nativeDecodedState setup timeouts leaks history.1.state = some point →
      ¬ ProtocolState.OwesFailure who setup.program point

omit [Finite setup.intendedProtocol.History] in
/-- The site of an agent owing no failure is debt free. -/
theorem siteDebtFree_of_not_owing {who : Player} {site : (onePacketN).InformationSite who}
    (notOwing : ¬ OwingAgent setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler ((onePacketN).agentAt
      site)) :
    SiteDebtFree setup timeouts leaks bounds horizon scheduler site :=
  fun history point decoded owes => notOwing ⟨history, point, decoded, owes⟩

open Classical in
/-- **The honest counterparts at one site** along a source sequence and a
target sequence: a tremble scale negligible against a floor to a depth, and at
every stage an honest counterpart of each history at which another player
responded irregularly, reached at least the floor to the depth times the square
of the scale as often as the irregular history up to the cube of the scale. -/
structure OnePacketCounterpartInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who) where
  /-- The tremble scale of irregular histories. -/
  scale : ℕ → ℝ
  /-- The floor of honest masses. -/
  floors : ℕ → ℝ
  /-- The depth of the floor. -/
  depth : ℕ
  /-- The slack of the honest counterparts. -/
  slack : ℝ
  floors_pos : ∀ n, 0 < floors n
  scale_nonneg : ∀ n, 0 ≤ scale n
  negligible : Tendsto (fun n => scale n / floors n ^ depth) atTop (nhds 0)
  slack_nonneg : 0 ≤ slack
  /-- The honest counterpart of each irregular history at each stage. -/
  counterpart : ℕ → (onePacketN).InformationHistory who site.1 →
    (onePacketN).InformationHistory who site.1
  /-- The weight common to an irregular history and its counterpart. -/
  commonWeight : ℕ → (onePacketN).InformationHistory who site.1 → ℝ
  counterpart_regular : ∀ n history, ¬ RegularTrace setup timeouts leaks bounds horizon scheduler
      (sequence n) who history.1.trace →
    RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
      (counterpart n history).1.trace
  irregular_le : ∀ n history, ¬ RegularTrace setup timeouts leaks bounds horizon scheduler
    (sequence n)
      who history.1.trace →
    ((onePacketN).historyReachWeight (targetSequence n).strategy history.1).toReal ≤
      scale n ^ 3 * commonWeight n history
  counterpart_ge : ∀ n history, ¬ RegularTrace setup timeouts leaks bounds horizon scheduler
      (sequence n) who history.1.trace →
    scale n ^ 2 * floors n ^ depth * commonWeight n history ≤
      slack * ((onePacketN).historyReachWeight (targetSequence n).strategy
        (counterpart n history).1).toReal

open Classical in
/-- **The own and replay inputs at one own-turn site** along a source sequence
and a target sequence: operational steps for the target profiles, and at every
stage the intended own completions of regular histories and the common fibers
of the replay projection. -/
structure OnePacketOwnInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who)
    (sourceSite : setup.intendedModel.InformationSite who)
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup timeouts leaks who site.1) where
  /-- Operational steps of the target profiles. -/
  steps : OperationalSteps setup timeouts leaks bounds horizon scheduler sequence
    (fun n => (targetSequence n).strategy) who
  /-- Own completions along regular histories decode to intended actions. -/
  ownIntended : ∀ n (history : (onePacketN).InformationHistory who site.1),
    RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who history.1.trace →
    OwnCompletionsIntended (timeouts := timeouts) (bounds := bounds) (horizon := horizon) (scheduler
      := scheduler) who
      history.1.trace
  /-- The common operational mass of the fibers at each stage. -/
  fiberMass : ℕ → ℝ
  fiber : ∀ n point, ∑ history with RegularTrace setup timeouts leaks bounds horizon scheduler
      (sequence n) who history.1.trace ∧
      replayProjection setup timeouts leaks bounds horizon scheduler sourceSite site decision
        projected
        history = point,
    operationalWeight setup timeouts leaks who (steps.mass n)
      (operationalRecord setup timeouts leaks bounds horizon scheduler history.1.trace) =
        fiberMass n

/-- **The forced-belief inputs at one own-turn site** along a source sequence
and a target sequence: the honest counterparts of irregular histories, and the
own and replay inputs. -/
structure OnePacketBeliefInputs (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment) {who : Player}
    (site : (onePacketN).InformationSite who)
    (sourceSite : setup.intendedModel.InformationSite who)
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup timeouts leaks who site.1) extends
    OnePacketCounterpartInputs setup timeouts leaks bounds horizon scheduler sequence
      targetSequence site,
    OnePacketOwnInputs setup timeouts leaks bounds horizon scheduler sequence targetSequence site
      sourceSite decision projected

omit [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
/-- **Beliefs converge at an own-turn site.** For a well-formed setup, at a
forced site of `who` at its own turn whose projected view is an intended site,
along a fully mixed Bayes source sequence and a fully mixed Bayes target
sequence with the forced-belief inputs, the native belief pushed forward along
the replay projection approaches the intended belief in `ℓ¹`. -/
theorem onePacket_beliefConverges (wellFormed : setup.WellFormed)
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu timeouts leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    {who : Player} {site : (onePacketN).InformationSite who}
    {sourceSite : setup.intendedModel.InformationSite who}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup timeouts leaks who site.1)
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
      setup) horizon
      scheduler who site.1)
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (inputs : OnePacketBeliefInputs setup timeouts leaks bounds horizon scheduler sequence
      targetSequence
      site sourceSite decision projected) :
    Tendsto (fun n => ∑' point,
      |((((targetSequence n).belief who site).map
          (replayProjection setup timeouts leaks bounds horizon scheduler sourceSite site decision
            projected)) point).toReal -
        ((sequence n).belief who sourceSite point).toReal|) atTop (nhds 0) := by
  classical
  let := Fintype.ofFinite (setup.intendedModel.InformationHistory who sourceSite.1)
  simp only [tsum_fintype]
  exact tendsto_projectedBelief_sub (timeouts := timeouts)
    (fun n => ForcedBeliefInputs.ofRegularHistories (timeouts := timeouts) (n := n) wellFormed
      forced decision turn
      projected (sourceMixed n) (inputs.ownIntended n) (inputs.fiberMass n) (inputs.fiber n)
      (inputs.counterpart n) (inputs.commonWeight n)
        (inputs.counterpart_regular n)
      (inputs.irregular_le n) (inputs.counterpart_ge n))
    decision (fun _ => rfl) mixed bayes sourceMixed sourceBayes inputs.floors_pos
    inputs.scale_nonneg inputs.negligible
      inputs.slack_nonneg

omit [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
open Classical in
/-- **Irregular histories vanish at a site with honest counterparts.** Along a
fully mixed Bayes target sequence, the belief mass of the histories at which
another player responded irregularly vanishes when each has an honest
counterpart reached more often by a factor the tremble scale over the floor to
the depth makes negligible. -/
theorem onePacket_irregularVanishes {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu timeouts leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    {who : Player} {site : (onePacketN).InformationSite who}
    (inputs : OnePacketCounterpartInputs setup timeouts leaks bounds horizon scheduler sequence
      targetSequence site) :
    Tendsto (fun n => expect ((targetSequence n).belief who site) (fun history =>
      if RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who history.1.trace
      then (0 : ℝ) else 1)) atTop (nhds 0) := by
  let := Fintype.ofFinite ((onePacketN).InformationHistory who site.1)
  have limit := tendsto_irregularRatio (slack := inputs.slack)
    inputs.negligible
    (Fintype.card ((onePacketN).InformationHistory who site.1))
  refine squeeze_zero (fun n => expect_nonneg _ _ fun history _ => by split <;> norm_num)
    (fun n => ?_) limit
  rw [expect_eq_sum]
  have bound := sum_belief_le_of_counterpart
    (fun history : (onePacketN).InformationHistory who site.1 =>
      ¬ RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who history.1.trace)
    (inputs.counterpart n) (Fintype.card ((onePacketN).InformationHistory who
      site.1)) (bayes n)
    (InformationModel.informationMass_pos_of_fullSupport _ _ (mixed n) who site)
    (div_nonneg (mul_nonneg inputs.slack_nonneg (inputs.scale_nonneg n))
      (pow_nonneg (inputs.floors_pos n).le _))
    (fun history irregular => not_not.mpr (inputs.counterpart_regular n
      history irregular))
    (fun _ _ => Finset.card_le_univ _)
    (fun history irregular => le_mul_of_tremble_counterpart (inputs.scale_nonneg n)
      (inputs.floors_pos n) (inputs.irregular_le n
        history irregular)
      (inputs.counterpart_ge n history irregular))
  have scaleNonnegative : 0 ≤ (Fintype.card ((onePacketN).InformationHistory who site.1) : ℝ) *
      (inputs.slack * inputs.scale n / inputs.floors n ^ inputs.depth) :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg
      (mul_nonneg inputs.slack_nonneg (inputs.scale_nonneg n))
      (pow_nonneg (inputs.floors_pos n).le _))
  refine le_trans (le_of_eq ?_) (bound.trans (div_le_self scaleNonnegative (by linarith)))
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun history _ => ?_
  split_ifs <;> simp

omit [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] in
open Classical in
/-- **Histories outside the forced region vanish at a forced site.** Along a
fully mixed Bayes target sequence, at a forced decision input with honest
counterparts, the belief mass of the histories outside the forced region
vanishes when the owner's own completions along regular histories are
intended: such a regular history is in a forced state
(`Vegas.forcedState_of_regular`), and irregular histories vanish
(`Vegas.onePacket_irregularVanishes`). -/
theorem onePacket_unforcedVanishes (wellFormed : setup.WellFormed)
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (onePacketN) (targetSequence n)
      ((bounds.onePacketMenu timeouts leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    {who : Player} {site : (onePacketN).InformationSite who}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (forced : forcedAgent (timeouts := timeouts) (bounds.onePacketMenu timeouts leaks) (initialLaw
      setup) horizon
      scheduler who site.1)
    (counterparts : OnePacketCounterpartInputs setup timeouts leaks bounds horizon scheduler
      sequence
      targetSequence site)
    (ownIntended : ∀ n (history : (onePacketN).InformationHistory who site.1),
      RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who history.1.trace →
      OwnCompletionsIntended (timeouts := timeouts) (bounds := bounds) (horizon := horizon)
        (scheduler := scheduler) who
        history.1.trace) :
    Tendsto (fun n => expect ((targetSequence n).belief who site) (fun history =>
      if ForcedState setup timeouts leaks who history.1.state then (0 : ℝ) else 1)) atTop (nhds 0)
        := by
  refine squeeze_zero (fun n => expect_nonneg _ _ fun history _ => by split <;> norm_num)
    (fun n => ?_) (onePacket_irregularVanishes setup timeouts leaks bounds horizon scheduler mixed
      bayes
      counterparts)
  refine expect_mono (fun history _ => ?_) (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)
  by_cases regular : RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
    history.1.trace
  · have inForced := forcedState_of_regular (timeouts := timeouts) wellFormed (sequence n) decision
      forced history
      regular (ownIntended n history regular)
    simp only [inForced, regular, ↓reduceIte, le_refl]
  · simp only [regular, ↓reduceIte]
    split <;> norm_num

/-- The intended site at the projected view of a site, when that view is an
intended decision site. -/
def projectedSite {who : Player} {info : (application setup timeouts leaks).Info}
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup timeouts leaks who
      info)) :
    setup.intendedModel.InformationSite who :=
  ⟨projectView setup timeouts leaks who info, decision⟩

omit [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
open Classical Filter in
/-- **Uniform errors from errors at each site.** For a property of errors at a
site that weakens as the error grows, if every site satisfying a condition has
a vanishing sequence of errors satisfying the property, then one vanishing
sequence serves every such site: the sum over the finitely many agents. -/
theorem exists_uniform_of_sites
    (property : ℕ → ∀ who, (onePacketN).InformationSite who → ℝ → Prop)
    (mono : ∀ n who site first second, first ≤ second → property n who site first →
      property n who site second)
    (condition : ∀ who, (onePacketN).InformationSite who → Prop)
    (perSite : ∀ who (site : (onePacketN).InformationSite who), condition who site →
      ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧ ∀ n, property n who site (error n)) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (onePacketN).InformationSite who), condition who site →
        property n who site (error n) := by
  let agentError := fun (agent : (onePacketN).InformationAgent (onePacketN).playedInformation)
      (n : ℕ) =>
    if present : ∃ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
        condition agent.1 ⟨agent.2.1, decision⟩ then
      |(perSite agent.1 ⟨agent.2.1, present.1⟩ present.2).choose n| else 0
  refine ⟨fun n => ∑ agent, agentError agent n, ?_, ?_⟩
  · rw [show (0 : ℝ) = ∑ _agent : (onePacketN).InformationAgent (onePacketN).playedInformation,
      (0 : ℝ) by simp]
    refine tendsto_finsetSum _ fun agent _ => ?_
    by_cases present : ∃ decision : (onePacketN).IsDecisionInfo agent.1 agent.2.1,
        condition agent.1 ⟨agent.2.1, decision⟩
    · simp only [agentError, present, ↓reduceDIte]
      simpa using (perSite agent.1 ⟨agent.2.1, present.1⟩ present.2).choose_spec.1.abs
    · simp only [agentError, present, ↓reduceDIte]
      exact tendsto_const_nhds
  · intro n who site holds
    have present : ∃ decision : (onePacketN).IsDecisionInfo ((onePacketN).agentAt site).1
        ((onePacketN).agentAt site).2.1,
        condition ((onePacketN).agentAt site).1 ⟨((onePacketN).agentAt site).2.1, decision⟩ :=
      ⟨site.2, holds⟩
    have nonneg : ∀ agent, 0 ≤ agentError agent n := fun agent => by
      simp only [agentError]
      split
      · exact abs_nonneg _
      · exact le_rfl
    have single := Finset.single_le_sum (f := fun agent => agentError agent n)
      (fun agent _ => nonneg agent) (Finset.mem_univ ((onePacketN).agentAt site))
    have atSite : agentError ((onePacketN).agentAt site) n =
        |(perSite who site holds).choose n| := by
      simp only [agentError, present, ↓reduceDIte]
    have spec := (perSite who site holds).choose_spec.2 n
    exact mono n who site _ _ ((le_abs_self _).trans (atSite ▸ single)) spec

end BeliefInputs

omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- A forced history whose observer owes no failure decodes to a point reached
by the intended source game. -/
theorem intendedReached_of_forced_debtFree (wellFormed : setup.WellFormed) {who : Player}
    (site : (onePacketN).InformationSite who)
    (debtFree : SiteDebtFree setup timeouts leaks bounds horizon scheduler site)
    (history : (onePacketN).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup timeouts leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (ordered : execution.application.config.cut.IsPrefix (siteRank (timeouts := timeouts) site.1))
    (forced : ForcedState setup timeouts leaks who history.1.state) :
    ∃ point, sourceServicePrefix? setup (siteRank (timeouts := timeouts) site.1)
      execution.application.config =
      some point ∧ ProtocolState.Intended setup.program point ∧ IntendedReached setup point := by
  classical
  let menu := bounds.onePacketMenu timeouts leaks
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.1.trace
  obtain ⟨decodedRank, ⟨residual⟩, holds⟩ := decodedState_intended_or_owes (timeouts := timeouts)
    wellFormed
    (failureProfile setup.program) menu horizon scheduler trace _ rfl
  have sameRank := EventOrder.Cut.IsPrefix.unique residual.checkpoint.ordered ordered
  subst sameRank
  have decoded := residual.decode
  generalize residual.lift (ProtocolState.entry residual.program residual.source) = point
    at decoded
  have pointDecoded : decodedPoint setup execution.application.config = some point :=
    (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have forcedHere := forced
  rw [current] at forcedHere
  obtain ⟨forcedFound, forcedDecoded, forcedHolds⟩ :=
    (forcedState_iff_decodedPoint (timeouts := timeouts) _).mp forcedHere
  rw [pointDecoded, Option.some.injEq] at forcedDecoded
  subst forcedDecoded
  have free : ∀ found, decodedPoint setup execution.application.config = some found →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program found := by
    intro found foundDecoded player
    rw [pointDecoded, Option.some.injEq] at foundDecoded
    subst foundDecoded
    by_cases same : player = who
    · subst same
      exact debtFree history point (by rw [current]; exact pointDecoded)
    · exact (forcedHolds.2 player same).2
  have intendedPoint : ProtocolState.Intended setup.program point := by
    rcases holds point decoded with intendedHere | ⟨player, owed⟩
    · exact intendedHere
    · exact (free point pointDecoded player owed).elim
  obtain ⟨replay, replayed⟩ := intendedHistory?_isSome_of_debtFree (timeouts := timeouts) wellFormed
    trace _ rfl free
  have reachedPoint : IntendedReached setup point :=
    ⟨replay, (intendedHistory?_state (timeouts := timeouts) trace replayed).trans pointDecoded⟩
  exact ⟨point, decoded, intendedPoint, reachedPoint⟩

/-- **Operational steps of assembled profiles.** For a well-formed setup, at
the tremble scale over the combined floor of a source sequence to a depth, the
certificate's operational steps are operational steps of every sequence of
profiles assembled from the certificate's components. -/
def assembledOperationalSteps (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (depth : ℕ)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n)) depth n)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      scale_pos
      scale_le_one weights targetSequence)
    (who : Player) :
    OperationalSteps setup timeouts leaks bounds horizon scheduler sequence
      (fun n => (targetSequence n).strategy) who :=
  have floorPos := fun n => combinedFloor_pos setup timeouts leaks bounds horizon scheduler
    (sequence n)
  have floorLe := fun n => combinedFloor_le_one setup timeouts leaks bounds horizon scheduler
    (sequence n)
  OperationalSteps.ofProfilesEq (timeouts := timeouts)
    (certificateOperationalSteps (timeouts := timeouts) wellFormed sequence scale scale_pos
      scale_le_one
      (fun n => (scaleEq n).trans_le (trembleScale_le_quarter (floorPos n).le (floorLe n)))
      (fun n => combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n)) floorPos
      (fun n => combinedFloor_le_contentFloor setup timeouts leaks bounds horizon scheduler
        (sequence n))
      covers capacity weights who
      (by
        simp only [scaleEq]
        exact tendsto_slotError _ floorPos floorLe depth _))
    assembled

open Classical in
/-- **The forced-belief inputs from the certificate.** For a well-formed setup,
along profiles assembled from the certificate's components at the tremble scale
over the combined floor of the source sequence to a depth, the operational steps
are the certificate's, the scale is the tremble scale, the floors are the
combined floors and the depth is the given depth. The intended own completions,
the common fibers and the honest counterparts remain inputs. -/
def OnePacketBeliefInputs.ofCertificate (wellFormed : setup.WellFormed)
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {scale : ℕ → ℝ} {scale_pos : ∀ n, 0 < scale n} {scale_le_one : ∀ n, scale n ≤ 1}
    (depth : ℕ)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n)) depth n)
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    {weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p)}
    {targetSequence : ℕ → (onePacketN).BehavioralAssessment}
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      scale_pos
      scale_le_one weights targetSequence)
    {who : Player} {site : (onePacketN).InformationSite who}
    {sourceSite : setup.intendedModel.InformationSite who}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    (decision : site.1 = some (past, view))
    (projected : sourceSite.1 = projectView setup timeouts leaks who site.1)
    (slack : ℝ) (slack_nonneg : 0 ≤ slack)
    (ownIntended : ∀ n (history : (onePacketN).InformationHistory who site.1),
      RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who history.1.trace →
      OwnCompletionsIntended (timeouts := timeouts) (bounds := bounds) (horizon := horizon)
        (scheduler := scheduler) who
        history.1.trace)
    (fiberMass : ℕ → ℝ)
    (fiber : ∀ n point, ∑ history with RegularTrace setup timeouts leaks bounds horizon scheduler
        (sequence n) who history.1.trace ∧
        replayProjection setup timeouts leaks bounds horizon scheduler sourceSite site decision
          projected
          history = point,
      operationalWeight setup timeouts leaks who
        (roundOrResponseMass (timeouts := timeouts) (scheduler := scheduler)
          (stepResponse (timeouts := timeouts) bounds (keyWeights setup timeouts leaks bounds
            horizon
            scheduler (weights n))
            (scale n)))
        (operationalRecord setup timeouts leaks bounds horizon scheduler history.1.trace) =
          fiberMass n)
    (counterpart : ℕ → (onePacketN).InformationHistory who site.1 →
      (onePacketN).InformationHistory who site.1)
    (commonWeight : ℕ → (onePacketN).InformationHistory who site.1 → ℝ)
    (counterpart_regular : ∀ n history, ¬ RegularTrace setup timeouts leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
        (counterpart n history).1.trace)
    (irregular_le : ∀ n history, ¬ RegularTrace setup timeouts leaks bounds horizon scheduler
      (sequence n)
        who history.1.trace →
      ((onePacketN).historyReachWeight (targetSequence n).strategy history.1).toReal ≤
        scale n ^ 3 * commonWeight n history)
    (counterpart_ge : ∀ n history, ¬ RegularTrace setup timeouts leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      scale n ^ 2 * combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n) ^
        depth *
          commonWeight n history ≤
        slack * ((onePacketN).historyReachWeight (targetSequence n).strategy
          (counterpart n history).1).toReal) :
    OnePacketBeliefInputs setup timeouts leaks bounds horizon scheduler sequence targetSequence site
      sourceSite decision projected where
  steps := assembledOperationalSteps (timeouts := timeouts) wellFormed sequence
    scale scale_pos scale_le_one depth
    scaleEq covers capacity weights assembled who
  scale := scale
  floors n := combinedFloor setup timeouts leaks bounds horizon scheduler
    (sequence n)
  depth := depth
  slack := slack
  floors_pos n := combinedFloor_pos setup timeouts leaks bounds horizon
    scheduler (sequence n)
  scale_nonneg n := (scale_pos n).le
  negligible := by
    simp only [scaleEq]
    exact tendsto_trembleScale_div_pow _
      (fun n => combinedFloor_pos setup timeouts leaks bounds horizon scheduler (sequence n))
      (fun n => combinedFloor_le_one setup timeouts leaks bounds horizon scheduler (sequence n))
  slack_nonneg := slack_nonneg
  ownIntended := ownIntended
  fiberMass := fiberMass
  fiber := fiber
  counterpart := counterpart
  commonWeight := commonWeight
  counterpart_regular := counterpart_regular
  irregular_le := irregular_le
  counterpart_ge := counterpart_ge

end Vegas
