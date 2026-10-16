/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryPolicyPlan
import GameTheory.Math.Probability.ProductConditioning
import GameTheory.Math.Probability.Domination

/-! # Conditioning original recovery policies on genuine own decision words -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- A genuine recovery word, with every old attempt retained, has positive
probability under the original policy prior of a fully mixed assessment. -/
theorem commitRecoveryPolicyPlan_record_present
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (history : setup.commitRecoveryProtocol.History) (who : Player) :
    ∃ member ∈ setup.commitRecoveryModel.Consistent who
        (setup.commitRecoveryModel.ownPlay who history.trace),
      member ∈ (setup.commitRecoveryPolicyPlan finite assessment.strategy who).support := by
  classical
  let model := setup.commitRecoveryModel
  let records := (model.ownPlay who history.trace).filter (fun _ => true)
  have offered (index : Fin records.length) :
      some records[index.val].2 ∈ model.menu who records[index.val].1 := by
    obtain ⟨site, observed, legal⟩ := model.exists_informationSite_of_mem_ownPlay history.trace
      (List.mem_of_mem_filter (List.getElem_mem index.isLt))
    simpa only [observed] using legal
  let choices (index : Fin records.length) :
      setup.commitRecoveryModel.Choice who records[index.val].1 :=
    ⟨some records[index.val].2, offered index⟩
  have coordinate (index : Fin records.length) :
      choices index ∈ (assessment.strategy who records[index.val].1).support := by
    obtain ⟨site, observed, legal⟩ := model.exists_informationSite_of_mem_ownPlay history.trace
      (List.mem_of_mem_filter (List.getElem_mem index.isLt))
    have full : ∀ choice : setup.commitRecoveryModel.Choice who records[index.val].1,
        choice ∈ (assessment.strategy who records[index.val].1).support := by
      rw [← observed]
      exact mixed who site
    exact full (choices index)
  have present := (independentProduct_support_iff
    (fun index : Fin records.length => assessment.strategy who records[index.val].1)
    choices).mpr coordinate
  have readout := setup.commitRecoveryPolicyPlan_record_readout finite assessment.strategy
    history who (fun _ => true)
  change (setup.commitRecoveryPolicyPlan finite assessment.strategy who).map
    (fun member (index : Fin records.length) => member records[index.val].1) =
      independentProduct (fun index : Fin records.length =>
        assessment.strategy who records[index.val].1) at readout
  have readoutPresent : choices ∈ ((setup.commitRecoveryPolicyPlan finite
      assessment.strategy who).map
        (fun member (index : Fin records.length) => member records[index.val].1)).support := by
    exact readout.symm ▸ present
  obtain ⟨member, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp readoutPresent
  refine ⟨member, ?_, supported⟩
  intro record recorded
  have kept : record ∈ records := List.mem_filter.mpr ⟨recorded, rfl⟩
  obtain ⟨index, bounded, equal⟩ := List.mem_iff_getElem.mp kept
  have chosen := congrArg Subtype.val (congrFun same (⟨index, bounded⟩ : Fin records.length))
  change (member records[index].1).val = some records[index].2 at chosen
  cases equal
  exact chosen

/-- Condition each original owner policy on its actual full own word. The
histories supplied for different owners may be different; no common source
entry or independent posterior entry is manufactured by this construction. -/
def commitRecoveryPolicyPosterior
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (who : Player)
    (history : setup.commitRecoveryProtocol.History) :
    setup.commitRecoveryModel.MixedPolicy who :=
  (setup.commitRecoveryPolicyPlan finite assessment.strategy who).filter
    (setup.commitRecoveryModel.Consistent who
      (setup.commitRecoveryModel.ownPlay who history.trace))
    (setup.commitRecoveryPolicyPlan_record_present finite assessment mixed history who)

/-- At a genuine decision, conditioning the original policy on its full own
recovery word leaves the current source choice unchanged. Old failed attempts
are conditioned, not erased, and no policy is redrawn at the current entry. -/
theorem commitRecoveryPolicyPosterior_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state)
    (who : Player) (active : setup.commitRecoveryProtocol.active history.state who) :
    (setup.commitRecoveryPolicyPosterior finite assessment mixed who history).map
        (fun member => member (setup.commitRecoveryModel.infoOf who history.trace)) =
      assessment.strategy who (setup.commitRecoveryModel.infoOf who history.trace) := by
  classical
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  let model := setup.commitRecoveryModel
  let policy := assessment.strategy who
  let sites := model.playedInformation who
  let fallback := policy.supportFallback model
  let laws : ∀ point : sites, PMF (model.Choice who point.val) := fun point => policy point.val
  let resolve := FiniteAssignment.resolve fallback sites
  let records := model.ownPlay who history.trace
  let restriction : ∀ point : sites, Set (model.Choice who point.val) := fun point =>
    {choice | ∀ recorded ∈ records, recorded.1 = point.val → choice.val = some recorded.2}
  let event : Set (∀ point : sites, model.Choice who point.val) :=
    {draw | ∀ point, draw point ∈ restriction point}
  let target := model.Consistent who records
  have played (recorded) (member : recorded ∈ records) : recorded.1 ∈ sites := by
    obtain ⟨site, observed, _⟩ := model.exists_informationSite_of_mem_ownPlay history.trace member
    obtain ⟨prior, nonterminal, _⟩ := site.2
    have present := model.mem_playedInformation (who := who) (history := prior.1) nonterminal
    rw [prior.2, observed] at present
    exact present
  let encoding : (∀ point : sites, model.Choice who point.val) ↪ model.Policy who :=
    ⟨resolve, by
      intro first second same
      funext point
      have projected := congrFun same point.val
      simpa only [resolve, FiniteAssignment.resolve_of_mem fallback sites _ point.property]
        using projected⟩
  have corresponds (draw) : encoding draw ∈ target ↔ draw ∈ event := by
    constructor
    · intro consistent point recorded member same
      have chosen := consistent recorded member
      change (resolve draw recorded.1).val = some recorded.2 at chosen
      rw [same] at chosen
      dsimp only [resolve] at chosen
      rw [FiniteAssignment.resolve_of_mem fallback sites draw point.property] at chosen
      exact chosen
    · intro consistent recorded member
      have chosen := consistent ⟨recorded.1, played recorded member⟩ recorded member rfl
      change (FiniteAssignment.resolve fallback sites draw recorded.1).val = some recorded.2
      rw [FiniteAssignment.resolve_of_mem fallback sites draw (played recorded member)]
      exact chosen
  have original : setup.commitRecoveryPolicyPlan finite assessment.strategy who =
      (independentProduct laws).map encoding := by
    change policy.toMixedWithin model sites fallback = _
    rw [InformationModel.BehavioralPolicy.toMixedWithin_eq_sampleOn]
    rfl
  have positive := setup.commitRecoveryPolicyPlan_record_present finite assessment mixed history who
  change ∃ member ∈ target, member ∈
    (setup.commitRecoveryPolicyPlan finite assessment.strategy who).support at positive
  rw [original] at positive
  have tablePositive : ∃ draw ∈ event, draw ∈ (independentProduct laws).support := by
    obtain ⟨member, consistent, supported⟩ := positive
    obtain ⟨draw, drawSupported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact ⟨draw, (corresponds draw).mp consistent, drawSupported⟩
  have filtered := map_filter_embedding (independentProduct laws) encoding event target
    corresponds tablePositive positive
  have currentPlayed : model.infoOf who history.trace ∈ sites :=
    model.mem_playedInformation running
  let current : sites := ⟨model.infoOf who history.trace, currentPlayed⟩
  have unrestricted : restriction current = Set.univ := by
    ext choice
    simp only [restriction, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    intro recorded member same
    obtain ⟨site, observed⟩ := model.exists_informationSite_of_active who history running active
    have recalled := model.decisionRecall_of_perfectRecall setup.commitRecoveryModel_perfectRecall
    have recordEq := recalled.recordAt_eq_ownPlay who site ⟨history, observed.symm⟩
    have impossible := site.not_mem_recordAt recalled recorded.2
    apply (impossible ?_).elim
    rw [recordEq]
    have equal : (site.val, recorded.2) = recorded := by
      apply Prod.ext
      · exact observed.trans same.symm
      · rfl
    rwa [equal]
  have marginal := map_filter_independentProduct_of_unrestricted laws restriction current
    unrestricted tablePositive
  have posteriorEq : setup.commitRecoveryPolicyPosterior finite assessment mixed who history =
      ((independentProduct laws).filter event tablePositive).map encoding := by
    simpa only [← original, commitRecoveryPolicyPosterior] using filtered.symm
  rw [posteriorEq, PMF.map_comp]
  change ((independentProduct laws).filter event tablePositive).map
    (fun draw => resolve draw (model.infoOf who history.trace)) = _
  have evaluation : (fun draw => resolve draw (model.infoOf who history.trace)) =
      fun draw => draw current := by
    funext draw
    exact FiniteAssignment.resolve_of_mem fallback sites draw currentPlayed
  rw [evaluation]
  exact marginal

/-- Conditioning the once-sampled original profile on genuine complete
owner records factors into the corresponding original owner posteriors.
Retired typed choices and their actual missing flags remain in the records. -/
theorem commitRecoveryPolicyPlan_condition_records
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (history : Player → setup.commitRecoveryProtocol.History) :
    let original := setup.commitRecoveryPolicyPlan finite assessment.strategy
    let event := Set.pi Set.univ fun who => setup.commitRecoveryModel.Consistent who
      (setup.commitRecoveryModel.ownPlay who (history who).trace)
    ∃ present : ∃ profile ∈ event, profile ∈ (independentProduct original).support,
      (independentProduct original).filter event present =
        independentProduct fun who => setup.commitRecoveryPolicyPosterior finite
          assessment mixed who (history who) := by
  classical
  intro original event
  let coordinate := fun who =>
    setup.commitRecoveryPolicyPlan_record_present finite assessment mixed (history who) who
  let chosen := fun who => (coordinate who).choose
  have present : ∃ profile ∈ event, profile ∈ (independentProduct original).support := by
    refine ⟨chosen, ?_, ?_⟩
    · intro who _
      exact (coordinate who).choose_spec.1
    · exact (independentProduct_support_iff _ _).mpr
        (fun who => (coordinate who).choose_spec.2)
  refine ⟨present, ?_⟩
  exact filter_independentProduct original
    (fun who => setup.commitRecoveryModel.Consistent who
      (setup.commitRecoveryModel.ownPlay who (history who).trace)) coordinate

/-- A focal owner's genuine own word does not condition any foreign original
policy. This is a statement about the original profile prior, not a claim that
physical observation or an arbitrary entry event is independent of that word. -/
theorem commitRecoveryPolicyPlan_foreign_of_focal_record
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (history : setup.commitRecoveryProtocol.History) (focal : Player) :
    let original := setup.commitRecoveryPolicyPlan finite assessment.strategy
    let event := {profile : (who : Player) → setup.commitRecoveryModel.Policy who |
      profile focal ∈ setup.commitRecoveryModel.Consistent focal
        (setup.commitRecoveryModel.ownPlay focal history.trace)}
    ∃ present : ∃ profile ∈ event, profile ∈ (independentProduct original).support,
      ((independentProduct original).filter event present).map
          (fun profile (who : {who : Player // who ≠ focal}) => profile who.val) =
        independentProduct (fun who : {who : Player // who ≠ focal} => original who.val) := by
  classical
  intro original event
  let restrictions : (who : Player) → Set (setup.commitRecoveryModel.Policy who) :=
    fun who => if same : who = focal then
      same.symm ▸ setup.commitRecoveryModel.Consistent focal
        (setup.commitRecoveryModel.ownPlay focal history.trace)
      else Set.univ
  have coordinate (who : Player) : ∃ member ∈ restrictions who,
      member ∈ (original who).support := by
    by_cases same : who = focal
    · subst who
      simpa only [restrictions, dite_true] using
        setup.commitRecoveryPolicyPlan_record_present finite assessment mixed history focal
    · obtain ⟨member, supported⟩ := (original who).support_nonempty
      exact ⟨member, by simp only [restrictions, dite_eq_right same, Set.mem_univ], supported⟩
  have eventEq : event = Set.pi Set.univ restrictions := by
    ext profile
    simp only [event, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro observed who
      by_cases same : who = focal
      · subst who
        simpa only [restrictions, dite_true] using observed
      · simp only [restrictions, dite_eq_right same, Set.mem_univ]
    · intro observed
      simpa only [restrictions, dite_true] using observed focal
  let chosen := fun who => (coordinate who).choose
  have present : ∃ profile ∈ event, profile ∈ (independentProduct original).support := by
    refine ⟨chosen, ?_, (independentProduct_support_iff _ _).mpr
      (fun who => (coordinate who).choose_spec.2)⟩
    rw [eventEq]
    exact fun who _ => (coordinate who).choose_spec.1
  refine ⟨present, ?_⟩
  have product := filter_independentProduct original restrictions coordinate
  have factored : (independentProduct original).filter event present =
      independentProduct (fun who => (original who).filter (restrictions who)
        (coordinate who)) := by
    simpa only [← eventEq] using product
  rw [factored]
  let inclusion : {who : Player // who ≠ focal} ↪ Player :=
    ⟨Subtype.val, Subtype.val_injective⟩
  trans independentProduct (fun who : {who : Player // who ≠ focal} =>
    (original who.val).filter (restrictions who.val) (coordinate who.val))
  · exact independentProduct_map_embedding inclusion _
  apply congrArg independentProduct
  funext who
  apply filter_of_support_subset
  simp only [restrictions, dite_eq_right who.property, Set.subset_univ]

end Vegas.SourceProgram.Setup
