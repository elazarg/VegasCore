/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryFlagPlan
import GameTheory.Math.Probability.ProductConditioning
import GameTheory.Math.Probability.ConditionalObservation

/-! # Actual recovery conditioning for shared occurrence flags

The private joint is fixed at initialization. Conditioning uses the original
complete recovery action word, including actions in every retired attempt.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Every genuine own action word has positive mass under the initialized
flag/domain plan when its prescribed domain laws have full support. -/
theorem commitRecoveryFlagPlan_record_present
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (values : (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (full : ∀ info, FullSupport (values info))
    (history : setup.commitRecoveryProtocol.History) :
    ∃ policy ∈ setup.commitRecoveryErasedModel.Consistent who
        (setup.commitRecoveryErasedModel.ownPlay who history.trace),
      policy ∈ ((setup.commitRecoveryFlagPlan finite who
        omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le values).map
          (setup.commitRecoveryFlagPolicy finite who)).support := by
  classical
  let model := setup.commitRecoveryErasedModel
  let records := model.ownPlay who history.trace
  let queries := records.map Prod.fst
  have bounded (index : Fin queries.length) : index.val < records.length := by
    simpa only [queries, List.length_map] using index.isLt
  have queryEq (index : Fin queries.length) :
      queries[index.val] = (records[index.val]'(bounded index)).1 := by
    exact List.getElem_map Prod.fst
  have offered (index : Fin queries.length) :
      some (records[index.val]'(bounded index)).2 ∈ model.menu who queries[index.val] := by
    rw [queryEq index]
    obtain ⟨site, observed, legal⟩ := model.exists_informationSite_of_mem_ownPlay history.trace
      (List.getElem_mem (bounded index))
    simpa only [observed] using legal
  let choices (index : Fin queries.length) : model.Choice who queries[index.val] :=
    ⟨some (records[index.val]'(bounded index)).2, offered index⟩
  have coordinate (index : Fin queries.length) : choices index ∈
      (setup.commitRecoveryValueTremble who queries[index.val]
        omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le
        (values queries[index.val])).support :=
    setup.commitRecoveryValueTremble_fullSupport who _ omission omissionPositive omissionSmall
      bad badPositive badSmall _ (full _) (choices index)
  have present := (independentProduct_support_iff _ choices).mpr coordinate
  have readout := setup.commitRecoveryFlagPlan_record_readout finite who
    omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le values history
  change (setup.commitRecoveryFlagPlan finite who
    omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le values).map
      (fun memory (index : Fin queries.length) =>
        setup.commitRecoveryFlagPolicy finite who memory queries[index.val]) = _ at readout
  have readoutPresent : choices ∈ ((setup.commitRecoveryFlagPlan finite who
      omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le values).map
        (fun memory (index : Fin queries.length) =>
          setup.commitRecoveryFlagPolicy finite who memory queries[index.val])).support :=
    readout.symm ▸ present
  obtain ⟨memory, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp readoutPresent
  refine ⟨setup.commitRecoveryFlagPolicy finite who memory, ?_, ?_⟩
  · intro record recorded
    obtain ⟨index, bounded, equal⟩ := List.mem_iff_getElem.mp recorded
    let selected : Fin queries.length := ⟨index, by
      simpa only [queries, List.length_map] using bounded⟩
    have chosen := congrArg Subtype.val (congrFun same selected)
    change (setup.commitRecoveryFlagPolicy finite who memory queries[selected.val]).val =
      some records[index].2 at chosen
    rw [queryEq selected] at chosen
    cases equal
    exact chosen
  · exact (PMF.mem_support_map_iff _ _ _).mpr ⟨memory, supported, rfl⟩

/-- The present source answer retains its exact three-class law after the
original private plan is conditioned on the entire genuine own action word. -/
theorem commitRecoveryFlagPlan_posterior_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (values : (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (full : ∀ info, FullSupport (values info))
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) :
    let mixed := (setup.commitRecoveryFlagPlan finite who
      omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le values).map
        (setup.commitRecoveryFlagPolicy finite who)
    (mixed.filter (setup.commitRecoveryErasedModel.Consistent who
        (setup.commitRecoveryErasedModel.ownPlay who history.trace))
      (setup.commitRecoveryFlagPlan_record_present finite who omission omissionPositive
        omissionSmall bad badPositive badSmall values full history)).map
          (fun policy => policy (setup.commitRecoveryErasedModel.infoOf who history.trace)) =
      setup.commitRecoveryValueTremble who
        (setup.commitRecoveryErasedModel.infoOf who history.trace)
        omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le
        (values (setup.commitRecoveryErasedModel.infoOf who history.trace)) := by
  classical
  intro mixed
  let model := setup.commitRecoveryErasedModel
  let records := model.ownPlay who history.trace
  let queries := model.infoOf who history.trace :: records.map Prod.fst
  let read (policy : model.Policy who) (index : Fin queries.length) := policy queries[index.val]
  let laws (index : Fin queries.length) := setup.commitRecoveryValueTremble who queries[index.val]
    omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le
    (values queries[index.val])
  have joint : mixed.map read = independentProduct laws := by
    change ((setup.commitRecoveryFlagPlan finite who
      omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le values).map
        (setup.commitRecoveryFlagPolicy finite who)).map read = _
    rw [PMF.map_comp]
    exact setup.commitRecoveryFlagPlan_current_record_readout finite who
      omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le
      values history running
  let restriction (index : Fin queries.length) : Set (model.Choice who queries[index.val]) :=
    {choice | ∀ prior : Fin records.length, index.val = prior.val + 1 →
      choice.val = some records[prior.val].2}
  let event : Set ((index : Fin queries.length) → model.Choice who queries[index.val]) :=
    fun draw => ∀ index, restriction index (draw index)
  let target := model.Consistent who records
  have corresponds (policy : model.Policy who) : read policy ∈ event ↔ policy ∈ target := by
    constructor
    · intro constrained record recorded
      obtain ⟨index, bounded, equal⟩ := List.mem_iff_getElem.mp recorded
      let selected : Fin queries.length := ⟨index + 1, by
        simpa only [queries, List.length_cons, List.length_map] using Nat.succ_lt_succ bounded⟩
      have chosen := constrained selected
        (⟨index, bounded⟩ : Fin records.length) rfl
      have queryEq : queries[selected.val] = records[index].1 := by
        dsimp only [queries, selected]
        rw [List.getElem_cons_succ, List.getElem_map]
      change (policy queries[selected.val]).val = some records[index].2 at chosen
      rw [queryEq] at chosen
      cases equal
      exact chosen
    · intro consistent index prior same
      let selected : Fin queries.length := ⟨prior.val + 1, by
        simpa only [queries, List.length_cons, List.length_map] using
          Nat.succ_lt_succ prior.isLt⟩
      have equal : index = selected := Fin.ext same
      subst index
      have queryEq : queries[selected.val] = records[prior.val].1 := by
        dsimp only [queries, selected]
        rw [List.getElem_cons_succ, List.getElem_map]
      change (policy queries[selected.val]).val = some records[prior.val].2
      rw [queryEq]
      exact consistent _ (List.getElem_mem prior.isLt)
  have positive := setup.commitRecoveryFlagPlan_record_present finite who
    omission omissionPositive omissionSmall bad badPositive badSmall values full history
  have imagePositive : ∃ draw ∈ event, draw ∈ (mixed.map read).support := by
    obtain ⟨policy, consistent, supported⟩ := positive
    exact ⟨read policy, (corresponds policy).mpr consistent,
      (PMF.mem_support_map_iff _ _ _).mpr ⟨policy, supported, rfl⟩⟩
  let observe := fun draw => decide (draw ∈ event)
  have originalEvent : {policy | (observe ∘ read) policy = true} = target := by
    ext policy
    simp only [Set.mem_ofPred_eq, Function.comp_apply, observe, decide_eq_true_eq]
    exact corresponds policy
  have imageEvent : {draw | observe draw = true} = event := by
    ext draw
    simp only [Set.mem_ofPred_eq, observe, decide_eq_true_eq]
  have observed : true ∈ (mixed.map (observe ∘ read)).support := by
    obtain ⟨policy, consistent, supported⟩ := positive
    apply (PMF.mem_support_map_iff _ _ _).mpr
    have contained : policy ∈ {policy | (observe ∘ read) policy = true} :=
      originalEvent.symm ▸ consistent
    exact ⟨policy, supported, contained⟩
  have transfer := map_fiberPosterior_readout mixed read observe true observed
  rw [fiberPosterior_eq_filter _ _ (exists_mem_fiber_of_mem_support_map observed),
    fiberPosterior_eq_filter _ _ (by simpa only [imageEvent] using imagePositive)] at transfer
  simp only [originalEvent, imageEvent] at transfer
  have unrestricted : restriction (0 : Fin queries.length) = Set.univ := by
    ext choice
    simp only [Set.mem_univ, iff_true]
    change ∀ prior : Fin records.length, 0 = prior.val + 1 → _
    intro prior impossible
    omega
  have tablePositive : ∃ draw ∈ event, draw ∈ (independentProduct laws).support :=
    joint ▸ imagePositive
  have marginal := map_filter_independentProduct_of_unrestricted laws restriction
    (0 : Fin queries.length) unrestricted tablePositive
  simp only [← joint] at marginal
  calc
    _ = ((mixed.filter target positive).map read).map
        (fun draw => draw (0 : Fin queries.length)) := by rw [PMF.map_comp]; rfl
    _ = ((mixed.map read).filter event imagePositive).map
        (fun draw => draw (0 : Fin queries.length)) := congrArg (PMF.map _) transfer
    _ = laws 0 := marginal
    _ = _ := rfl

/-- Reading the initialized occurrence-flag plan behaviorally in the ORIGINAL
perfect-recall source game recovers its prescribed legal source law. -/
theorem commitRecoveryFlagPlan_toBehavioralWith
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (values : (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (full : ∀ info, FullSupport (values info))
    (fallback : setup.commitRecoveryModel.Policy who)
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) :
    let mixed := ((setup.commitRecoveryFlagPlan finite who
      omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le values).map
        (setup.commitRecoveryFlagPolicy finite who)).map (setup.commitRecoveryErasedPolicy who)
    InformationModel.MixedPolicy.toBehavioralWith (M := setup.commitRecoveryModel)
        mixed fallback (setup.commitRecoveryModel.infoOf who history.trace) =
      (setup.commitRecoveryValueTremble who
        (setup.commitRecoveryErasedInformation who
          (setup.commitRecoveryModel.infoOf who history.trace))
        omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le
        (values (setup.commitRecoveryErasedInformation who
          (setup.commitRecoveryModel.infoOf who history.trace)))).map
            (setup.commitRecoveryErasedChoice who
              (setup.commitRecoveryModel.infoOf who history.trace)).symm := by
  classical
  intro mixed
  let reduced := (setup.commitRecoveryFlagPlan finite who
    omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le values).map
      (setup.commitRecoveryFlagPolicy finite who)
  let target := setup.commitRecoveryModel.ConsistentAt who
    (setup.commitRecoveryModel.infoOf who history.trace)
  let sourceEvent := setup.commitRecoveryErasedModel.Consistent who
    (setup.commitRecoveryErasedModel.ownPlay who history.trace)
  have corresponds (policy : setup.commitRecoveryErasedModel.Policy who) :
      setup.commitRecoveryErasedPolicy who policy ∈ target ↔ policy ∈ sourceEvent := by
    dsimp only [target, sourceEvent]
    rw [setup.commitRecoveryModel.consistentAt_eq_consistent_ownPlay
      (setup.commitRecoveryModel.constrainsAlike_of_perfectRecall
        setup.commitRecoveryModel_perfectRecall) who history]
    exact (setup.commitRecoveryErasedPolicy_consistent who policy history).symm
  have positive := setup.commitRecoveryFlagPlan_record_present finite who
    omission omissionPositive omissionSmall bad badPositive badSmall values full history
  have imagePositive : ∃ policy ∈ target, policy ∈ mixed.support := by
    obtain ⟨policy, consistent, supported⟩ := positive
    exact ⟨setup.commitRecoveryErasedPolicy who policy, (corresponds policy).mpr consistent,
      (PMF.mem_support_map_iff _ _ _).mpr ⟨policy, supported, rfl⟩⟩
  let observe := fun policy : setup.commitRecoveryModel.Policy who => decide (policy ∈ target)
  have originalEvent : {policy | (observe ∘ setup.commitRecoveryErasedPolicy who) policy = true} =
      sourceEvent := by
    ext policy
    simp only [Set.mem_ofPred_eq, Function.comp_apply, observe, decide_eq_true_eq]
    exact corresponds policy
  have imageEvent : {policy | observe policy = true} = target := by
    ext policy
    simp only [Set.mem_ofPred_eq, observe, decide_eq_true_eq]
  have observed : true ∈ (reduced.map
      (observe ∘ setup.commitRecoveryErasedPolicy who)).support := by
    obtain ⟨policy, consistent, supported⟩ := positive
    have contained : policy ∈
        {policy | (observe ∘ setup.commitRecoveryErasedPolicy who) policy = true} :=
      originalEvent.symm ▸ consistent
    exact (PMF.mem_support_map_iff _ _ _).mpr
      ⟨policy, supported, contained⟩
  have transfer := map_fiberPosterior_readout reduced
    (setup.commitRecoveryErasedPolicy who) observe true observed
  rw [fiberPosterior_eq_filter _ _ (exists_mem_fiber_of_mem_support_map observed),
    fiberPosterior_eq_filter _ _ (by simpa only [imageEvent] using imagePositive)] at transfer
  simp only [originalEvent, imageEvent] at transfer
  rw [InformationModel.MixedPolicy.toBehavioralWith, dite_eq_left imagePositive, ← transfer,
    PMF.map_comp]
  calc
    _ = ((reduced.filter sourceEvent positive).map
        (fun policy => policy (setup.commitRecoveryErasedInformation who
          (setup.commitRecoveryModel.infoOf who history.trace)))).map
            (setup.commitRecoveryErasedChoice who
              (setup.commitRecoveryModel.infoOf who history.trace)).symm := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by
      apply congrArg (PMF.map
        (setup.commitRecoveryErasedChoice who
          (setup.commitRecoveryModel.infoOf who history.trace)).symm)
      have present := setup.commitRecoveryFlagPlan_posterior_readout finite who
        omission omissionPositive omissionSmall bad badPositive badSmall values full history running
      rw [setup.commitRecoveryErasedModel_infoOf who history.trace] at present
      exact present

/-- One initialized occurrence-flag/domain-table draw per owner realizes the
ENTIRE original source history law, with omissions, failures and retries.
This does not identify its private table joint with independent full choices. -/
theorem commitRecoveryFlagPlan_run
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (full : ∀ who info, FullSupport (values who info)) (fuel : Nat) :
    setup.commitRecoveryModel.runMixed
        (fun who => ((setup.commitRecoveryFlagPlan finite who
          omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le
          (values who)).map (setup.commitRecoveryFlagPolicy finite who)).map
            (setup.commitRecoveryErasedPolicy who)) fuel =
      setup.commitRecoveryModel.runBehavioral
        (setup.commitRecoveryErasedProfile (setup.commitRecoveryTrembledProfile
          omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le values))
        fuel := by
  rw [setup.commitRecoveryModel.runMixed_toBehavioral
    (setup.commitRecoveryModel.constrainsAlike_of_perfectRecall
      setup.commitRecoveryModel_perfectRecall)]
  apply setup.commitRecoveryModel.runBehavioralFrom_congr fuel
    setup.commitRecoveryProtocol.initHistory
  intro history _ running who
  exact setup.commitRecoveryFlagPlan_toBehavioralWith finite who
    omission omissionPositive omissionSmall bad badPositive badSmall
    (values who) (full who) _ history running

end Vegas.SourceProgram.Setup
