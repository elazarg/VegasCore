/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryValueTremble
import Vegas.Game.CommitRecoveryErasedPolicyPlan
import Interaction.ReactiveMixtureExtraCoordinate

/-! # Original domain-value plans on genuine reduced recovery coordinates

Only ordinary domain moves and true openings are stored in this table. Source
failure flags and native delivery randomness remain separate private memory.
The table is sampled once; restoring an attempt does not initialize it again.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- The finite coordinate set consists of actual reduced source information,
including every legal retry and every supported original setup draw. -/
def commitRecoveryDomainSites (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (who : Player) :
    Finset (setup.commitRecoveryErasedModel.InfoState who) := by
  classical
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  exact setup.commitRecoveryErasedModel.playedInformation who

/-- A private domain table has no omission, accepted-failure or timing coin. -/
def CommitRecoveryDomainDraw (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (who : Player) :=
  (site : setup.commitRecoveryDomainSites finite who) →
    setup.CommitRecoveryValueChoice who site.val

/-- Deterministic values outside the genuinely sampled set only make the
original full-information policy total. -/
def commitRecoveryDomainFallback (who : Player)
    (info : setup.commitRecoveryErasedModel.InfoState who) :
    setup.CommitRecoveryValueChoice who info :=
  Classical.choice (setup.commitRecoveryValueChoice_nonempty who info)

/-- Resolve the one original domain table into legal reduced source moves. -/
def commitRecoveryDomainPolicy (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (who : Player)
    (draw : setup.CommitRecoveryDomainDraw finite who) :
    setup.commitRecoveryErasedModel.Policy who := by
  classical
  exact fun info =>
    (FiniteAssignment.resolve (setup.commitRecoveryDomainFallback who)
      (setup.commitRecoveryDomainSites finite who) draw info).val

/-- The original domain prior is independent across reduced coordinates. -/
def commitRecoveryDomainPlan (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (who : Player)
    (values : (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info)) :
    PMF (setup.CommitRecoveryDomainDraw finite who) :=
  independentProduct (fun site : setup.commitRecoveryDomainSites finite who => values site.val)

open Classical in
/-- Changing a domain coordinate does not change the source policy at a
different query, including deterministic answers outside the sampled set. -/
theorem commitRecoveryDomainPolicy_update_other
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (draw : setup.CommitRecoveryDomainDraw finite who)
    (selected : setup.commitRecoveryDomainSites finite who)
    (value : setup.CommitRecoveryValueChoice who selected.val)
    (info : setup.commitRecoveryErasedModel.InfoState who) (different : info ≠ selected.val) :
    setup.commitRecoveryDomainPolicy finite who (Function.update draw selected value) info =
      setup.commitRecoveryDomainPolicy finite who draw info := by
  classical
  unfold commitRecoveryDomainPolicy
  by_cases present : info ∈ setup.commitRecoveryDomainSites finite who
  · rw [FiniteAssignment.resolve_of_mem _ _ _ present,
      FiniteAssignment.resolve_of_mem _ _ _ present]
    have distinct : (⟨info, present⟩ : setup.commitRecoveryDomainSites finite who) ≠ selected :=
      fun same => different (congrArg Subtype.val same)
    rw [Function.update_of_ne distinct]
  · rw [FiniteAssignment.resolve_of_not_mem _ _ _ present,
      FiniteAssignment.resolve_of_not_mem _ _ _ present]

/-- Every sampled domain plan has finite support, independently of the size
of the ambient full-information type. -/
theorem commitRecoveryDomainPlan_support_finite
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (values : (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info)) :
    (setup.commitRecoveryDomainPlan finite who values).support.Finite := by
  classical
  change (independentProduct
    (fun site : setup.commitRecoveryDomainSites finite who => values site.val)).support.Finite
  have coordinate (site : setup.commitRecoveryDomainSites finite who) :
      (values site.val).support.Finite := by
    let := setup.commitRecoveryValueChoice_finite finite who site.val
    exact Set.toFinite _
  apply (Set.Finite.pi coordinate).subset
  intro draw supported site _
  exact (independentProduct_support_iff _ draw).mp supported site

/-- Forgetting the domain subtype gives precisely finite predrawing with the
encoded fallback; no unplayed label is silently read as a sampled coordinate. -/
theorem commitRecoveryDomainPlan_policy
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (values : (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info)) :
    (setup.commitRecoveryDomainPlan finite who values).map
        (setup.commitRecoveryDomainPolicy finite who) =
      InformationModel.BehavioralPolicy.toMixedWithin setup.commitRecoveryErasedModel
        (fun info => (values info).map Subtype.val) (setup.commitRecoveryDomainSites finite who)
        (fun info => (setup.commitRecoveryDomainFallback who info).val) := by
  classical
  rw [InformationModel.BehavioralPolicy.toMixedWithin_eq_sampleOn,
    FiniteAssignment.sampleOn, ← independentProduct_map, PMF.map_comp]
  apply congrArg (PMF.map · (setup.commitRecoveryDomainPlan finite who values))
  funext draw info
  change (FiniteAssignment.resolve (setup.commitRecoveryDomainFallback who)
      (setup.commitRecoveryDomainSites finite who) draw info).val =
    FiniteAssignment.resolve (fun point => (setup.commitRecoveryDomainFallback who point).val)
      (setup.commitRecoveryDomainSites finite who) (fun point => (draw point).val) info
  by_cases present : info ∈ setup.commitRecoveryDomainSites finite who
  · simp only [FiniteAssignment.resolve_of_mem _ _ _ present]
  · simp only [FiniteAssignment.resolve_of_not_mem _ _ _ present]

/-- Lifting the original domain tables to the full-information source game
realizes the complete behavioral law of the ordinary domain component. -/
theorem commitRecoveryDomainPlan_run
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info)) (fuel : Nat) :
    setup.commitRecoveryModel.runMixed
        (fun who => (setup.commitRecoveryDomainPlan finite who (values who)).map
          (fun draw => setup.commitRecoveryErasedPolicy who
            (setup.commitRecoveryDomainPolicy finite who draw))) fuel =
      setup.commitRecoveryModel.runBehavioral
        (setup.commitRecoveryErasedProfile fun who info =>
          (values who info).map Subtype.val) fuel := by
  classical
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  have mapped (who : Player) :
      (setup.commitRecoveryDomainPlan finite who (values who)).map
          (fun draw => setup.commitRecoveryErasedPolicy who
            (setup.commitRecoveryDomainPolicy finite who draw)) =
        (InformationModel.BehavioralPolicy.toMixedWithin setup.commitRecoveryErasedModel
          (fun info => (values who info).map Subtype.val)
          (setup.commitRecoveryDomainSites finite who)
          (fun info => (setup.commitRecoveryDomainFallback who info).val)).map
            (setup.commitRecoveryErasedPolicy who) := by
    rw [← setup.commitRecoveryDomainPlan_policy finite who, PMF.map_comp]
    rfl
  simp_rw [mapped]
  rw [InformationModel.runMixed, setup.commitRecoveryErasedMixed_runFrom]
  change setup.commitRecoveryErasedModel.runMixed
    (fun who => InformationModel.BehavioralPolicy.toMixedWithin setup.commitRecoveryErasedModel
      (fun info => (values who info).map Subtype.val) (setup.commitRecoveryDomainSites finite who)
      (fun info => (setup.commitRecoveryDomainFallback who info).val)) fuel = _
  rw [setup.commitRecoveryErasedModel.runMixed_toMixedWithin
    (setup.commitRecoveryErasedModel.actsOnceWhereItMatters_of_actsOnce
      setup.commitRecoveryErasedModel_actsOnce)
    (setup.commitRecoveryDomainSites finite)
    (fun who info => (values who info).map Subtype.val)
    (fun who info => (setup.commitRecoveryDomainFallback who info).val) fuel
    (setup.commitRecoveryErasedModel.coversInformationSites_playedInformation fuel)]
  exact (setup.commitRecoveryErasedProfile_runFrom
    (fun who info => (values who info).map Subtype.val) fuel
    setup.commitRecoveryProtocol.initHistory).symm

/-- A genuine current query is an actual sampled domain coordinate. -/
theorem commitRecoveryDomainSites_current
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (who : Player) (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) :
    setup.commitRecoveryErasedModel.infoOf who history.trace ∈
      setup.commitRecoveryDomainSites finite who := by
  classical
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  exact setup.commitRecoveryErasedModel.mem_playedInformation running

/-- Reading the current domain coordinate retains its complete original law. -/
theorem commitRecoveryDomainPlan_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (values : (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (site : setup.commitRecoveryDomainSites finite who) :
    (setup.commitRecoveryDomainPlan finite who values).map (fun draw => draw site) =
      values site.val :=
  independentProduct_map_eval _ site

/-- At genuine original full information, the lifted policy reads exactly the
sampled ordinary domain law at its derived reduced label. -/
theorem commitRecoveryDomainPlan_source_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (values : (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) :
    (setup.commitRecoveryDomainPlan finite who values).map
        (fun draw => (setup.commitRecoveryErasedPolicy who
          (setup.commitRecoveryDomainPolicy finite who draw)
          (setup.commitRecoveryModel.infoOf who history.trace)).val) =
      (values (setup.commitRecoveryErasedModel.infoOf who history.trace)).map
        (fun choice => choice.val.val) := by
  classical
  have played := setup.commitRecoveryDomainSites_current finite who history running
  let selected : setup.commitRecoveryDomainSites finite who :=
    ⟨setup.commitRecoveryErasedModel.infoOf who history.trace, played⟩
  have read := congrArg (PMF.map (fun choice => choice.val.val))
    (setup.commitRecoveryDomainPlan_readout finite who values selected)
  rw [PMF.map_comp] at read
  convert read using 1
  apply congrArg (PMF.map · (setup.commitRecoveryDomainPlan finite who values))
  funext draw
  change (FiniteAssignment.resolve (setup.commitRecoveryDomainFallback who)
    (setup.commitRecoveryDomainSites finite who) draw
      (setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who history.trace))).val.val = _
  rw [← setup.commitRecoveryErasedModel_infoOf who history.trace,
    FiniteAssignment.resolve_of_mem _ _ _ played]
  rfl

open Classical in
/-- The actual original source own-action record does not inspect the current
domain coordinate. This uses strict chronological lengths, not recall of an
erased representative as though it were a played full information state. -/
theorem commitRecoveryDomainPolicy_consistent_update
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state)
    (draw : setup.CommitRecoveryDomainDraw finite who)
    (value : setup.CommitRecoveryValueChoice who
      (setup.commitRecoveryErasedModel.infoOf who history.trace)) :
    let selected : setup.commitRecoveryDomainSites finite who :=
      ⟨setup.commitRecoveryErasedModel.infoOf who history.trace,
        setup.commitRecoveryDomainSites_current finite who history running⟩
    setup.commitRecoveryErasedPolicy who
        (setup.commitRecoveryDomainPolicy finite who (Function.update draw selected value)) ∈
        setup.commitRecoveryModel.Consistent who
          (setup.commitRecoveryModel.ownPlay who history.trace) ↔
      setup.commitRecoveryErasedPolicy who (setup.commitRecoveryDomainPolicy finite who draw) ∈
        setup.commitRecoveryModel.Consistent who
          (setup.commitRecoveryModel.ownPlay who history.trace) := by
  classical
  intro selected
  rw [← setup.commitRecoveryErasedPolicy_consistent,
    ← setup.commitRecoveryErasedPolicy_consistent]
  have unchanged (record) (recorded : record ∈
      setup.commitRecoveryErasedModel.ownPlay who history.trace) :
      setup.commitRecoveryDomainPolicy finite who (Function.update draw selected value) record.1 =
        setup.commitRecoveryDomainPolicy finite who draw record.1 := by
    apply setup.commitRecoveryDomainPolicy_update_other
    intro same
    have past : record.1 ∈ setup.commitRecoveryErasedModel.actedAt who history.trace := by
      rw [setup.commitRecoveryErasedModel.actedAt_eq_map_ownPlay]
      exact List.mem_map.mpr ⟨record, recorded, rfl⟩
    have shorter := setup.commitRecoveryErasedModel_record_word_length_lt who
      history.trace record.1 past
    have equalLength : record.1.1.2.length = history.trace.length := by
      rw [same]
      exact setup.commitRecoveryErasedModel_word_length who history.trace
    rw [equalLength] at shorter
    exact Nat.lt_irrefl _ shorter
  constructor <;> intro consistent record recorded
  · simpa only [unchanged record recorded] using consistent record recorded
  · simpa only [unchanged record recorded] using consistent record recorded

open Classical in
/-- The native posterior keeps an unread original domain coordinate
independent of every other coordinate and arbitrary extra private memory.
The premise concerns actual recalled response atoms, not a desired posterior. -/
theorem commitRecoveryDomainPlan_posterior_split
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (values : (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    {Principal Other : Type} (app : Interaction.ReactiveApplication Principal)
    (otherLaw : PMF Other)
    (members : setup.CommitRecoveryDomainDraw finite who × Other → app.Policy)
    (selected : setup.commitRecoveryDomainSites finite who) (past : List app.PlayerEntry)
    (unread : ∀ (before : List app.PlayerEntry) (entry : app.PlayerEntry),
      before ++ [entry] <+: past → ∀ plan other part,
        members (Function.update plan selected part, other) before entry.beforeView entry.action =
          members (plan, other) before entry.beforeView entry.action) :
    let original := (setup.commitRecoveryDomainPlan finite who values).bind
      fun plan => otherLaw.map (Prod.mk plan)
    let posterior := (app.policyMixture original members).posterior past
    posterior.map (fun memory => (memory.1 selected,
        (fun site : {site // site ≠ selected} => memory.1 site.val, memory.2))) =
      (values selected.val).bind (fun value =>
        (posterior.map fun memory =>
          (fun site : {site // site ≠ selected} => memory.1 site.val, memory.2)).map
            (Prod.mk value)) := by
  classical
  intro original posterior
  obtain ⟨remainder, split⟩ := app.policyMixture_posterior_coordinate_extra
    (fun site : setup.commitRecoveryDomainSites finite who => values site.val)
    otherLaw members selected past unread
  have marginal := congrArg (PMF.map Prod.snd) split
  change (posterior.map _).map Prod.snd =
    (bindPairLaw (values selected.val) fun _ => remainder).map Prod.snd at marginal
  rw [PMF.map_comp, bindPairLaw_const_map_snd] at marginal
  rw [← marginal] at split
  exact split

/-- The full source perturbation is selected on reduced information. Omission
and accepted failure rates are fixed before choosing the conditional domains. -/
def commitRecoveryTrembledProfile
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info)) :
    ∀ who, setup.commitRecoveryErasedModel.BehavioralPolicy who :=
  fun who info => setup.commitRecoveryValueTremble who info
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded (values who info)

omit [Fintype Player] in
/-- The actual full-information source assessment is fully mixed on every
genuine decision, with accepted failure and omission kept distinct. -/
theorem commitRecoveryTrembledProfile_fullyMixed
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (full : ∀ who info, FullSupport (values who info)) :
    InformationModel.BehavioralAssessment.IsFullyMixed
      (InformationModel.BehavioralAssessment.ofStrategy
        (setup.commitRecoveryErasedProfile (setup.commitRecoveryTrembledProfile
          omission omissionPositive.le omissionSmall.le
          bad badPositive.le badSmall.le values))) := by
  intro who site choice
  change choice ∈ ((setup.commitRecoveryTrembledProfile omission omissionPositive.le
    omissionSmall.le bad badPositive.le badSmall.le values who
      (setup.commitRecoveryErasedInformation who site.val)).map
        (setup.commitRecoveryErasedChoice who site.val).symm).support
  apply (PMF.mem_support_map_iff _ _ _).mpr
  refine ⟨setup.commitRecoveryErasedChoice who site.val choice, ?_,
    (setup.commitRecoveryErasedChoice who site.val).symm_apply_apply choice⟩
  exact setup.commitRecoveryValueTremble_fullSupport who _ omission omissionPositive
    omissionSmall bad badPositive badSmall _ (full who _)
    (setup.commitRecoveryErasedChoice who site.val choice)

/-- One original full-choice plan realizes the entire trembled source runner,
including positive-probability omissions, accepted failures and actual retries.
This is a run-law theorem; it does not equate different private plan joints. -/
theorem commitRecoveryTrembledProfile_plan_run
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info)) (fuel : Nat) :
    let profile := setup.commitRecoveryTrembledProfile omission omissionNonnegative
      omissionBounded bad badNonnegative badBounded values
    setup.commitRecoveryModel.runMixed
        (fun who => (setup.commitRecoveryErasedPolicyPlan finite profile who).map
          (setup.commitRecoveryErasedPolicy who)) fuel =
      setup.commitRecoveryModel.runBehavioral (setup.commitRecoveryErasedProfile profile) fuel :=
  setup.commitRecoveryErasedPolicyPlan_run finite _ fuel

end Vegas.SourceProgram.Setup
