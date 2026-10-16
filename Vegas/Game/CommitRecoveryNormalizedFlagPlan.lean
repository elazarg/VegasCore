/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryFlagConditioning
import Vegas.Game.CommitRecoveryNoMissContinuation

/-! # One initialized occurrence plan realizes the normalized original source

The domain table is the original table on genuine erased source queries.
Actual full-information policies read that same table at the normalized
query. Logical-clock preservation supplies nonrecurrence; the analytical
erased signal model is not used as a recursive normalized information model.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- The existing original flag/domain table is read at the genuine normalized
query, and its action is transported to the original full source menu. -/
def commitRecoveryNormalizedFlagPolicy (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (who : Player)
    (memory : setup.CommitRecoveryFlagDraw finite who × setup.CommitRecoveryDomainDraw finite who) :
    setup.commitRecoveryModel.Policy who := fun info =>
  (setup.commitRecoveryNoMissErasedChoice who info).symm
    (setup.commitRecoveryFlagPolicy finite who memory
      (setup.commitRecoveryErasedInformation who (setup.commitRecoveryNoMissInformation who info)))

omit [Fintype Player] in
/-- The selected domain prescription and separate source failure rates are
read at the genuine combined query in the ORIGINAL full source game. -/
def commitRecoveryNormalizedTrembledProfile
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (owner : Player) → (info : setup.commitRecoveryErasedModel.InfoState owner) →
      PMF (setup.CommitRecoveryValueChoice owner info)) :
    ∀ owner, setup.commitRecoveryModel.BehavioralPolicy owner :=
  setup.commitRecoveryNoMissErasedProfile (fun owner info =>
    setup.commitRecoveryValueTremble owner info omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded (values owner info))

private theorem normalized_query_played (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (who : Player) (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) :
    setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who
          (setup.commitRecoveryModel.infoOf who history.trace)) ∈
      setup.commitRecoveryDomainSites finite who := by
  obtain ⟨replay, same, staysRunning⟩ :=
    setup.commitRecoveryNoMissInformation_genuine_history who history
  have played := setup.commitRecoveryDomainSites_current finite who replay (staysRunning running)
  rw [setup.commitRecoveryErasedModel_infoOf, same] at played
  exact played

omit [Fintype Player] in
private theorem original_record_clocks (who : Player)
    (history : setup.commitRecoveryProtocol.History) :
    ((setup.commitRecoveryModel.ownPlay who history.trace).map
      (fun record => record.1.1.2.length)).Nodup := by
  have clocks := setup.commitRecoveryErasedModel_record_clock_nodup who history.trace
  rw [setup.commitRecoveryErasedModel_ownPlay, List.map_map] at clocks
  simpa only [commitRecoveryErasedInformation, List.length_map, Function.comp_def] using clocks

omit [Fintype Player] in
private theorem original_current_clock (who : Player)
    (history : setup.commitRecoveryProtocol.History) :
    (setup.commitRecoveryModel.infoOf who history.trace).1.2.length = history.trace.length := by
  have clock := setup.commitRecoveryErasedModel_word_length who history.trace
  rw [setup.commitRecoveryErasedModel_infoOf] at clock
  simpa only [commitRecoveryErasedInformation, List.length_map] using clock

omit [Fintype Player] in
private theorem original_record_clock_lt (who : Player)
    (history : setup.commitRecoveryProtocol.History)
    (record : setup.commitRecoveryModel.InfoState who × CommitRecoveryMove Player L)
    (recorded : record ∈ setup.commitRecoveryModel.ownPlay who history.trace) :
    record.1.1.2.length < history.trace.length := by
  have reduced : (setup.commitRecoveryErasedInformation who record.1, record.2) ∈
      setup.commitRecoveryErasedModel.ownPlay who history.trace := by
    rw [setup.commitRecoveryErasedModel_ownPlay]
    exact List.mem_map.mpr ⟨record, recorded, rfl⟩
  have acted : setup.commitRecoveryErasedInformation who record.1 ∈
      setup.commitRecoveryErasedModel.actedAt who history.trace := by
    rw [setup.commitRecoveryErasedModel.actedAt_eq_map_ownPlay]
    exact List.mem_map.mpr ⟨_, reduced, rfl⟩
  have earlier := setup.commitRecoveryErasedModel_record_word_length_lt who
    history.trace _ acted
  simpa only [commitRecoveryErasedInformation, List.length_map] using earlier

omit [Fintype Player] in
private theorem normalized_tremble_choice
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (who : Player) → (info : setup.commitRecoveryErasedModel.InfoState who) →
      PMF (setup.CommitRecoveryValueChoice who info))
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded values who info =
      (setup.commitRecoveryValueTremble who
        (setup.commitRecoveryErasedInformation who (setup.commitRecoveryNoMissInformation who info))
        omission omissionNonnegative omissionBounded bad badNonnegative badBounded
        (values who (setup.commitRecoveryErasedInformation who
          (setup.commitRecoveryNoMissInformation who info)))).map
            (setup.commitRecoveryNoMissErasedChoice who info).symm := by
  unfold commitRecoveryNormalizedTrembledProfile
  apply pmf_map_injective Subtype.val_injective
  rw [setup.commitRecoveryNoMissErasedProfile_raw, PMF.map_comp]
  rfl

private theorem normalized_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (owner : Player) → (info : setup.commitRecoveryErasedModel.InfoState owner) →
      PMF (setup.CommitRecoveryValueChoice owner info))
    (queries : List (setup.commitRecoveryModel.InfoState who))
    (distinct : (queries.map (fun info => info.1.2.length)).Nodup)
    (played : ∀ info ∈ queries,
      setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryNoMissInformation who info) ∈
          setup.commitRecoveryDomainSites finite who) :
    (setup.commitRecoveryFlagPlan finite who omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded (values who)).map
        (fun memory (index : Fin queries.length) =>
          setup.commitRecoveryNormalizedFlagPolicy finite who memory queries[index.val]) =
      independentProduct (fun index : Fin queries.length =>
        setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded values who queries[index.val]) := by
  let key := fun info => setup.commitRecoveryErasedInformation who
    (setup.commitRecoveryNoMissInformation who info)
  have keyClocks : ((queries.map key).map (fun info => info.1.2.length)).Nodup := by
    simpa only [List.map_map, Function.comp_def, key,
      setup.commitRecoveryNoMissInformation_erased_word_length] using distinct
  have keyPlayed : ∀ info ∈ queries.map key,
      info ∈ setup.commitRecoveryDomainSites finite who := by
    intro info member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact played original present
  have base := setup.commitRecoveryFlagPlan_readout finite who
    omission omissionNonnegative omissionBounded bad badNonnegative badBounded
    (values who) (queries.map key) keyClocks keyPlayed
  let mappedLaws (index : Fin (queries.map key).length) :=
    setup.commitRecoveryValueTremble who (queries.map key)[index.val]
      omission omissionNonnegative omissionBounded bad badNonnegative badBounded
      (values who (queries.map key)[index.val])
  let selected : Fin queries.length ↪ Fin (queries.map key).length :=
    ⟨fun index => ⟨index.val, by simpa only [List.length_map] using index.isLt⟩,
      fun first second same => Fin.ext
        (congrArg (fun index : Fin (queries.map key).length => index.val) same)⟩
  let raw : ((index : Fin (queries.map key).length) →
      setup.commitRecoveryModel.Choice who (queries.map key)[index.val]) →
        (Fin (queries.map key).length → Option (CommitRecoveryMove Player L)) :=
    fun draw index => (draw index).val
  have baseRaw := congrArg (PMF.map raw) base
  rw [PMF.map_comp, independentProduct_map] at baseRaw
  have chosen := congrArg (PMF.map (fun draw index => draw (selected index))) baseRaw
  rw [PMF.map_comp, independentProduct_map_embedding selected] at chosen
  let forget : ((index : Fin queries.length) →
      setup.commitRecoveryModel.Choice who queries[index.val]) →
        (Fin queries.length → Option (CommitRecoveryMove Player L)) :=
    fun draw index => (draw index).val
  have injective : Function.Injective forget := by
    intro first second same
    funext index
    exact Subtype.ext (congrFun same index)
  apply pmf_map_injective injective
  rw [PMF.map_comp, independentProduct_map]
  have queryEq (index : Fin queries.length) :
      (queries.map key)[(selected index).val] = key queries[index.val] := by
    exact List.getElem_map ..
  calc
    _ = (setup.commitRecoveryFlagPlan finite who omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded (values who)).map
        (fun memory index =>
          (setup.commitRecoveryFlagPolicy finite who memory
            (queries.map key)[(selected index).val]).val) := by
      apply congrArg (PMF.map · _)
      funext memory
      funext index
      rw [queryEq]
      rfl
    _ = independentProduct (fun index => (mappedLaws (selected index)).map Subtype.val) := chosen
    _ = _ := by
      apply congrArg independentProduct
      funext index
      rw [setup.normalized_tremble_choice, PMF.map_comp]
      dsimp only [mappedLaws]
      rw [queryEq]
      rfl

/-- Every remembered genuine source action is sampled from the same original
occurrence plan at its normalized query, with an exact product readout law. -/
theorem commitRecoveryNormalizedFlagPlan_record_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (owner : Player) → (info : setup.commitRecoveryErasedModel.InfoState owner) →
      PMF (setup.CommitRecoveryValueChoice owner info))
    (history : setup.commitRecoveryProtocol.History) :
    let queries := (setup.commitRecoveryModel.ownPlay who history.trace).map Prod.fst
    (setup.commitRecoveryFlagPlan finite who omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded (values who)).map
        (fun memory (index : Fin queries.length) =>
          setup.commitRecoveryNormalizedFlagPolicy finite who memory queries[index.val]) =
      independentProduct (fun index : Fin queries.length =>
        setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded values who queries[index.val]) := by
  intro queries
  apply setup.normalized_readout
  · simpa only [queries, List.map_map, Function.comp_def] using
      setup.original_record_clocks who history
  · intro info present
    obtain ⟨record, recorded, rfl⟩ := List.mem_map.mp present
    obtain ⟨site, observed, _legal⟩ :=
      setup.commitRecoveryModel.exists_informationSite_of_mem_ownPlay history.trace recorded
    obtain ⟨prior, running, _⟩ := site.2
    have played := setup.normalized_query_played finite who prior.1 running
    rw [prior.2, observed] at played
    exact played

/-- The original current query is independent of the complete genuine past
record in the initialized flag/domain plan. No conditional prior is reset. -/
theorem commitRecoveryNormalizedFlagPlan_current_record_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (omission : ℝ) (omissionNonnegative : 0 ≤ omission) (omissionBounded : omission ≤ 1)
    (bad : ℝ) (badNonnegative : 0 ≤ bad) (badBounded : bad ≤ 1)
    (values : (owner : Player) → (info : setup.commitRecoveryErasedModel.InfoState owner) →
      PMF (setup.CommitRecoveryValueChoice owner info))
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) :
    let queries := setup.commitRecoveryModel.infoOf who history.trace ::
      (setup.commitRecoveryModel.ownPlay who history.trace).map Prod.fst
    (setup.commitRecoveryFlagPlan finite who omission omissionNonnegative omissionBounded
      bad badNonnegative badBounded (values who)).map
        (fun memory (index : Fin queries.length) =>
          setup.commitRecoveryNormalizedFlagPolicy finite who memory queries[index.val]) =
      independentProduct (fun index : Fin queries.length =>
        setup.commitRecoveryNormalizedTrembledProfile omission omissionNonnegative omissionBounded
        bad badNonnegative badBounded values who queries[index.val]) := by
  intro queries
  apply setup.normalized_readout
  · simp only [queries, List.map_cons, List.map_map, Function.comp_def]
    refine List.nodup_cons.mpr ⟨?_, setup.original_record_clocks who history⟩
    intro member
    obtain ⟨record, recorded, same⟩ := List.mem_map.mp member
    have earlier := setup.original_record_clock_lt who history record recorded
    rw [same, setup.original_current_clock who history] at earlier
    exact Nat.lt_irrefl _ earlier
  · intro info present
    rcases List.mem_cons.mp present with rfl | past
    · exact setup.normalized_query_played finite who history running
    · obtain ⟨record, recorded, rfl⟩ := List.mem_map.mp past
      obtain ⟨site, observed, _legal⟩ :=
        setup.commitRecoveryModel.exists_informationSite_of_mem_ownPlay history.trace recorded
      obtain ⟨prior, priorRunning, _⟩ := site.2
      have played := setup.normalized_query_played finite who prior.1 priorRunning
      rw [prior.2, observed] at played
      exact played

omit [Fintype Player] in
private theorem normalized_tremble_fullSupport
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (values : (owner : Player) → (info : setup.commitRecoveryErasedModel.InfoState owner) →
      PMF (setup.CommitRecoveryValueChoice owner info))
    (full : ∀ owner info, FullSupport (values owner info))
    (who : Player) (info : setup.commitRecoveryModel.InfoState who) :
    FullSupport (setup.commitRecoveryNormalizedTrembledProfile omission
      omissionPositive.le omissionSmall.le
        bad badPositive.le badSmall.le values who info) := by
  rw [setup.normalized_tremble_choice]
  intro choice
  refine (PMF.mem_support_map_iff _ _ _).mpr
    ⟨(setup.commitRecoveryNoMissErasedChoice who info) choice, ?_, ?_⟩
  · exact setup.commitRecoveryValueTremble_fullSupport who _ omission omissionPositive omissionSmall
      bad badPositive badSmall _ (full who _) _
  · exact (setup.commitRecoveryNoMissErasedChoice who info).symm_apply_apply choice

/-- The original initialized plan assigns positive mass to every actual full
source own record, including its retired attempts and failure flags. -/
theorem commitRecoveryNormalizedFlagPlan_record_present
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (values : (owner : Player) → (info : setup.commitRecoveryErasedModel.InfoState owner) →
      PMF (setup.CommitRecoveryValueChoice owner info))
    (full : ∀ owner info, FullSupport (values owner info))
    (history : setup.commitRecoveryProtocol.History) :
    ∃ policy ∈ setup.commitRecoveryModel.Consistent who
        (setup.commitRecoveryModel.ownPlay who history.trace),
      policy ∈ ((setup.commitRecoveryFlagPlan finite who
        omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le
        (values who)).map (setup.commitRecoveryNormalizedFlagPolicy finite who)).support := by
  classical
  let model := setup.commitRecoveryModel
  let records := model.ownPlay who history.trace
  have offered (index : Fin records.length) :
      some records[index.val].2 ∈ model.menu who records[index.val].1 := by
    obtain ⟨site, observed, legal⟩ := model.exists_informationSite_of_mem_ownPlay history.trace
      (List.getElem_mem index.isLt)
    simpa only [observed] using legal
  let queries := records.map Prod.fst
  let selected (index : Fin queries.length) : Fin records.length :=
    ⟨index.val, by simpa only [queries, List.length_map] using index.isLt⟩
  have queryEq (index : Fin queries.length) :
      queries[index.val] = records[(selected index).val].1 := by
    exact List.getElem_map ..
  let choices (index : Fin queries.length) : model.Choice who queries[index.val] :=
    ⟨some records[(selected index).val].2, by
      rw [queryEq]
      exact offered (selected index)⟩
  have coordinate (index : Fin queries.length) : choices index ∈
      (setup.commitRecoveryNormalizedTrembledProfile omission omissionPositive.le omissionSmall.le
        bad badPositive.le badSmall.le values who queries[index.val]).support :=
    setup.normalized_tremble_fullSupport omission omissionPositive omissionSmall
      bad badPositive badSmall values full who _ (choices index)
  have present := (independentProduct_support_iff _ choices).mpr coordinate
  have readout := setup.commitRecoveryNormalizedFlagPlan_record_readout finite who
    omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le values history
  have readoutPresent : choices ∈ ((setup.commitRecoveryFlagPlan finite who
      omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le (values who)).map
        (fun memory (index : Fin queries.length) =>
          setup.commitRecoveryNormalizedFlagPolicy finite who memory queries[index.val])).support :=
    readout.symm ▸ present
  obtain ⟨memory, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp readoutPresent
  refine ⟨setup.commitRecoveryNormalizedFlagPolicy finite who memory, ?_, ?_⟩
  · intro record recorded
    obtain ⟨index, bounded, equal⟩ := List.mem_iff_getElem.mp recorded
    let position : Fin queries.length :=
      ⟨index, by simpa only [queries, List.length_map] using bounded⟩
    have chosen := congrArg Subtype.val (congrFun same position)
    change (setup.commitRecoveryNormalizedFlagPolicy finite who memory queries[position.val]).val =
      some records[(selected position).val].2 at chosen
    rw [queryEq] at chosen
    change (setup.commitRecoveryNormalizedFlagPolicy finite who memory records[index].1).val =
      some records[index].2 at chosen
    cases equal
    exact chosen
  · exact (PMF.mem_support_map_iff _ _ _).mpr ⟨memory, supported, rfl⟩

/-- Conditioning the SAME initialized plan on the ENTIRE actual source own
record leaves the current normalized source prescription unchanged. -/
theorem commitRecoveryNormalizedFlagPlan_posterior_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (values : (owner : Player) → (info : setup.commitRecoveryErasedModel.InfoState owner) →
      PMF (setup.CommitRecoveryValueChoice owner info))
    (full : ∀ owner info, FullSupport (values owner info))
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) :
    let mixed := (setup.commitRecoveryFlagPlan finite who
      omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le (values who)).map
        (setup.commitRecoveryNormalizedFlagPolicy finite who)
    (mixed.filter (setup.commitRecoveryModel.Consistent who
        (setup.commitRecoveryModel.ownPlay who history.trace))
      (setup.commitRecoveryNormalizedFlagPlan_record_present finite who omission omissionPositive
        omissionSmall bad badPositive badSmall values full history)).map
          (fun policy => policy (setup.commitRecoveryModel.infoOf who history.trace)) =
      setup.commitRecoveryNormalizedTrembledProfile omission omissionPositive.le omissionSmall.le
        bad badPositive.le badSmall.le values who
            (setup.commitRecoveryModel.infoOf who history.trace) := by
  classical
  intro mixed
  let model := setup.commitRecoveryModel
  let records := model.ownPlay who history.trace
  let queries := model.infoOf who history.trace :: records.map Prod.fst
  let read (policy : model.Policy who) (index : Fin queries.length) := policy queries[index.val]
  let laws (index : Fin queries.length) := setup.commitRecoveryNormalizedTrembledProfile
    omission omissionPositive.le omissionSmall.le
        bad badPositive.le badSmall.le values who queries[index.val]
  have joint : mixed.map read = independentProduct laws := by
    change ((setup.commitRecoveryFlagPlan finite who
      omission omissionPositive.le omissionSmall.le bad badPositive.le badSmall.le (values who)).map
        (setup.commitRecoveryNormalizedFlagPolicy finite who)).map read = _
    rw [PMF.map_comp]
    exact setup.commitRecoveryNormalizedFlagPlan_current_record_readout finite who
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
      have chosen := constrained selected (⟨index, bounded⟩ : Fin records.length) rfl
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
  have positive := setup.commitRecoveryNormalizedFlagPlan_record_present finite who
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

/-- The original perfect-recall source realization of the SAME initialized
plan has exactly the selected combined-query behavioral policy. -/
theorem commitRecoveryNormalizedFlagPlan_toBehavioralWith
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw] (who : Player)
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (values : (owner : Player) → (info : setup.commitRecoveryErasedModel.InfoState owner) →
      PMF (setup.CommitRecoveryValueChoice owner info))
    (full : ∀ owner info, FullSupport (values owner info))
    (fallback : setup.commitRecoveryModel.Policy who)
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) :
    InformationModel.MixedPolicy.toBehavioralWith (M := setup.commitRecoveryModel)
        ((setup.commitRecoveryFlagPlan finite who omission omissionPositive.le omissionSmall.le
          bad badPositive.le badSmall.le (values who)).map
            (setup.commitRecoveryNormalizedFlagPolicy finite who)) fallback
        (setup.commitRecoveryModel.infoOf who history.trace) =
      setup.commitRecoveryNormalizedTrembledProfile omission omissionPositive.le omissionSmall.le
        bad badPositive.le badSmall.le values who
            (setup.commitRecoveryModel.infoOf who history.trace) := by
  classical
  have records := setup.commitRecoveryModel.consistentAt_eq_consistent_ownPlay
    (setup.commitRecoveryModel.constrainsAlike_of_perfectRecall
      setup.commitRecoveryModel_perfectRecall) who history
  have positive := setup.commitRecoveryNormalizedFlagPlan_record_present finite who
    omission omissionPositive omissionSmall bad badPositive badSmall values full history
  rw [InformationModel.MixedPolicy.toBehavioralWith, records, dite_eq_left positive]
  exact setup.commitRecoveryNormalizedFlagPlan_posterior_readout finite who
    omission omissionPositive omissionSmall bad badPositive badSmall values full history running

/-- One ORIGINAL occurrence-flag/domain-table draw per owner realizes the
ENTIRE original source history law at the genuine combined queries. All
retries, exhausted restores, omissions and accepted failures are retained. -/
theorem commitRecoveryNormalizedFlagPlan_run
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (omission : ℝ) (omissionPositive : 0 < omission) (omissionSmall : omission < 1)
    (bad : ℝ) (badPositive : 0 < bad) (badSmall : bad < 1)
    (values : (owner : Player) → (info : setup.commitRecoveryErasedModel.InfoState owner) →
      PMF (setup.CommitRecoveryValueChoice owner info))
    (full : ∀ owner info, FullSupport (values owner info)) (fuel : Nat) :
    setup.commitRecoveryModel.runMixed
        (fun who => (setup.commitRecoveryFlagPlan finite who omission omissionPositive.le
          omissionSmall.le bad badPositive.le badSmall.le (values who)).map
            (setup.commitRecoveryNormalizedFlagPolicy finite who)) fuel =
      setup.commitRecoveryModel.runBehavioral
        (setup.commitRecoveryNormalizedTrembledProfile omission omissionPositive.le omissionSmall.le
        bad badPositive.le badSmall.le values) fuel := by
  rw [setup.commitRecoveryModel.runMixed_toBehavioral
    (setup.commitRecoveryModel.constrainsAlike_of_perfectRecall
      setup.commitRecoveryModel_perfectRecall)]
  apply setup.commitRecoveryModel.runBehavioralFrom_congr fuel
    setup.commitRecoveryProtocol.initHistory
  intro history _ running who
  exact setup.commitRecoveryNormalizedFlagPlan_toBehavioralWith finite who
    omission omissionPositive omissionSmall bad badPositive badSmall
    values full _ history running

end Vegas.SourceProgram.Setup
