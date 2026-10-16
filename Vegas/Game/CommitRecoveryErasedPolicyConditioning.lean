/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryErasedPolicyPlan
import GameTheory.Math.Probability.ProductConditioning
import GameTheory.Math.Probability.Domination
import GameTheory.Math.Probability.ConditionalObservation

/-! # Conditioning original reduced policies on genuine recovery decision words -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- A genuine recovery word, with every old attempt retained, has positive
probability under the original policy prior of a fully mixed assessment. -/
theorem commitRecoveryErasedPolicyPlan_record_present
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (assessment : setup.commitRecoveryErasedModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (history : setup.commitRecoveryProtocol.History) (who : Player) :
    ∃ member ∈ setup.commitRecoveryErasedModel.Consistent who
        (setup.commitRecoveryErasedModel.ownPlay who history.trace),
      member ∈ (setup.commitRecoveryErasedPolicyPlan finite assessment.strategy who).support := by
  classical
  let model := setup.commitRecoveryErasedModel
  let records := (model.ownPlay who history.trace).filter (fun _ => true)
  have offered (index : Fin records.length) :
      some records[index.val].2 ∈ model.menu who records[index.val].1 := by
    obtain ⟨site, observed, legal⟩ := model.exists_informationSite_of_mem_ownPlay history.trace
      (List.mem_of_mem_filter (List.getElem_mem index.isLt))
    simpa only [observed] using legal
  let choices (index : Fin records.length) :
      setup.commitRecoveryErasedModel.Choice who records[index.val].1 :=
    ⟨some records[index.val].2, offered index⟩
  have coordinate (index : Fin records.length) :
      choices index ∈ (assessment.strategy who records[index.val].1).support := by
    obtain ⟨site, observed, legal⟩ := model.exists_informationSite_of_mem_ownPlay history.trace
      (List.mem_of_mem_filter (List.getElem_mem index.isLt))
    have full : ∀ choice : setup.commitRecoveryErasedModel.Choice who records[index.val].1,
        choice ∈ (assessment.strategy who records[index.val].1).support := by
      rw [← observed]
      exact mixed who site
    exact full (choices index)
  have present := (independentProduct_support_iff
    (fun index : Fin records.length => assessment.strategy who records[index.val].1)
    choices).mpr coordinate
  have readout := setup.commitRecoveryErasedPolicyPlan_record_readout finite assessment.strategy
    history who (fun _ => true)
  change (setup.commitRecoveryErasedPolicyPlan finite assessment.strategy who).map
    (fun member (index : Fin records.length) => member records[index.val].1) =
      independentProduct (fun index : Fin records.length =>
        assessment.strategy who records[index.val].1) at readout
  have readoutPresent : choices ∈ ((setup.commitRecoveryErasedPolicyPlan finite
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

/-- Condition each original owner policy on its actual reduced chronological own word. The
histories supplied for different owners may be different; no common source
entry or independent posterior entry is manufactured by this construction. -/
def commitRecoveryErasedPolicyPosterior
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (assessment : setup.commitRecoveryErasedModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (who : Player)
    (history : setup.commitRecoveryProtocol.History) :
    setup.commitRecoveryErasedModel.MixedPolicy who :=
  (setup.commitRecoveryErasedPolicyPlan finite assessment.strategy who).filter
    (setup.commitRecoveryErasedModel.Consistent who
      (setup.commitRecoveryErasedModel.ownPlay who history.trace))
    (setup.commitRecoveryErasedPolicyPlan_record_present finite assessment mixed history who)

/-- At a genuine decision, conditioning the original policy on its full own
recovery word leaves the current source choice unchanged. Old attempt choices
remain in the conditioning event; their keys erase private retired signals.
No policy is redrawn at the current entry. -/
theorem commitRecoveryErasedPolicyPosterior_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (assessment : setup.commitRecoveryErasedModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state)
    (who : Player) :
    (setup.commitRecoveryErasedPolicyPosterior finite assessment mixed who history).map
        (fun member => member (setup.commitRecoveryErasedModel.infoOf who history.trace)) =
      assessment.strategy who (setup.commitRecoveryErasedModel.infoOf who history.trace) := by
  classical
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  let model := setup.commitRecoveryErasedModel
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
  have original : setup.commitRecoveryErasedPolicyPlan finite assessment.strategy who =
      (independentProduct laws).map encoding := by
    change policy.toMixedWithin model sites fallback = _
    rw [InformationModel.BehavioralPolicy.toMixedWithin_eq_sampleOn]
    rfl
  have positive := setup.commitRecoveryErasedPolicyPlan_record_present finite assessment mixed
    history who
  change ∃ member ∈ target, member ∈
    (setup.commitRecoveryErasedPolicyPlan finite assessment.strategy who).support at positive
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
    have past : recorded.1 ∈ model.actedAt who history.trace := by
      rw [model.actedAt_eq_map_ownPlay]
      exact List.mem_map.mpr ⟨recorded, member, rfl⟩
    have shorter := setup.commitRecoveryErasedModel_record_word_length_lt who
      history.trace recorded.1 past
    have equalLength : recorded.1.1.2.length = history.trace.length := by
      rw [same]
      exact setup.commitRecoveryErasedModel_word_length who history.trace
    rw [equalLength] at shorter
    exact (Nat.lt_irrefl _ shorter).elim
  have marginal := map_filter_independentProduct_of_unrestricted laws restriction current
    unrestricted tablePositive
  have posteriorEq : setup.commitRecoveryErasedPolicyPosterior finite assessment mixed who history =
      ((independentProduct laws).filter event tablePositive).map encoding := by
    simpa only [← original, commitRecoveryErasedPolicyPosterior] using filtered.symm
  rw [posteriorEq, PMF.map_comp]
  change ((independentProduct laws).filter event tablePositive).map
    (fun draw => resolve draw (model.infoOf who history.trace)) = _
  have evaluation : (fun draw => resolve draw (model.infoOf who history.trace)) =
      fun draw => draw current := by
    funext draw
    exact FiniteAssignment.resolve_of_mem fallback sites draw currentPlayed
  rw [evaluation]
  exact marginal

open Classical in
/-- After the owner's genuine full recovery word, its current choice is
independent of every remaining coordinate of its original policy. The remaining
law is the actual conditioned marginal, including all retired decisions. -/
theorem commitRecoveryErasedPolicyPosterior_split
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (assessment : setup.commitRecoveryErasedModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state)
    (who : Player) :
    let current := setup.commitRecoveryErasedModel.infoOf who history.trace
    let choices := fun info => setup.commitRecoveryErasedModel.Choice who info
    let posterior := setup.commitRecoveryErasedPolicyPosterior finite assessment mixed who history
    posterior.map (Equiv.piSplitAt current choices) =
      (assessment.strategy who current).bind (fun choice =>
        (posterior.map fun member =>
          fun other : {other // other ≠ current} => member other.val).map (Prod.mk choice)) := by
  classical
  intro current choices posterior
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  let model := setup.commitRecoveryErasedModel
  let policy := assessment.strategy who
  let sites := model.playedInformation who
  let fallback := policy.supportFallback model
  let laws : ∀ point : sites, PMF (choices point.val) := fun point => policy point.val
  let resolve := FiniteAssignment.resolve fallback sites
  let records := model.ownPlay who history.trace
  let restriction : ∀ point : sites, Set (choices point.val) := fun point =>
    {choice | ∀ recorded ∈ records, recorded.1 = point.val → choice.val = some recorded.2}
  let event : Set (∀ point : sites, choices point.val) :=
    {draw | ∀ point, draw point ∈ restriction point}
  let target := model.Consistent who records
  have played (recorded) (member : recorded ∈ records) : recorded.1 ∈ sites := by
    obtain ⟨site, observed, _⟩ := model.exists_informationSite_of_mem_ownPlay history.trace member
    obtain ⟨prior, nonterminal, _⟩ := site.2
    have present := model.mem_playedInformation (who := who) (history := prior.1) nonterminal
    rw [prior.2, observed] at present
    exact present
  let encoding : (∀ point : sites, choices point.val) ↪ model.Policy who :=
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
  have original : setup.commitRecoveryErasedPolicyPlan finite assessment.strategy who =
      (independentProduct laws).map encoding := by
    change policy.toMixedWithin model sites fallback = _
    rw [InformationModel.BehavioralPolicy.toMixedWithin_eq_sampleOn]
    rfl
  have positive := setup.commitRecoveryErasedPolicyPlan_record_present finite assessment mixed
    history who
  change ∃ member ∈ target, member ∈
    (setup.commitRecoveryErasedPolicyPlan finite assessment.strategy who).support at positive
  rw [original] at positive
  have tablePositive : ∃ draw ∈ event, draw ∈ (independentProduct laws).support := by
    obtain ⟨member, consistent, supported⟩ := positive
    obtain ⟨draw, drawSupported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact ⟨draw, (corresponds draw).mp consistent, drawSupported⟩
  have filtered := map_filter_embedding (independentProduct laws) encoding event target
    corresponds tablePositive positive
  have posteriorEq : posterior =
      ((independentProduct laws).filter event tablePositive).map encoding := by
    simpa only [← original, posterior, commitRecoveryErasedPolicyPosterior] using filtered.symm
  have coordinate (point : sites) : ∃ choice ∈ restriction point,
      choice ∈ (laws point).support := by
    obtain ⟨draw, permitted, supported⟩ := tablePositive
    exact ⟨draw point, permitted point,
      (independentProduct_support_iff laws draw).mp supported point⟩
  let updated := fun point : sites => (laws point).filter (restriction point) (coordinate point)
  have eventEq : event = Set.pi Set.univ restriction := by
    ext draw
    simp only [event, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const]
  have tableLaw : (independentProduct laws).filter event tablePositive =
      independentProduct updated := by
    simpa only [← eventEq, updated] using filter_independentProduct laws restriction coordinate
  have currentPlayed : current ∈ sites := model.mem_playedInformation running
  let selected : sites := ⟨current, currentPlayed⟩
  let wholeSplit := Equiv.piSplitAt current choices
  let finiteSplit := Equiv.piSplitAt selected (fun point : sites => choices point.val)
  let remaining := fun rest =>
    (wholeSplit (resolve (finiteSplit.symm (fallback current, rest)))).2
  let restLaw := (independentProduct (fun point : {point : sites // point ≠ selected} =>
    updated point.val)).map remaining
  have resolved (choice : choices current) (rest) :
      wholeSplit (resolve (finiteSplit.symm (choice, rest))) = (choice, remaining rest) := by
    apply Prod.ext
    · change resolve (finiteSplit.symm (choice, rest)) current = choice
      dsimp only [resolve]
      rw [FiniteAssignment.resolve_of_mem fallback sites _ currentPlayed]
      simp [finiteSplit, selected, Equiv.piSplitAt]
    · funext other
      change resolve (finiteSplit.symm (choice, rest)) other.val =
        resolve (finiteSplit.symm (fallback current, rest)) other.val
      dsimp only [resolve]
      by_cases present : other.val ∈ sites
      · rw [FiniteAssignment.resolve_of_mem fallback sites _ present,
          FiniteAssignment.resolve_of_mem fallback sites _ present]
        have different : (⟨other.val, present⟩ : sites) ≠ selected := by
          intro equal
          exact other.property (congrArg Subtype.val equal)
        simp [finiteSplit, Equiv.piSplitAt, different]
      · rw [FiniteAssignment.resolve_of_not_mem fallback sites _ present,
          FiniteAssignment.resolve_of_not_mem fallback sites _ present]
  have factored : posterior.map wholeSplit =
      (updated selected).bind (fun choice => restLaw.map (Prod.mk choice)) := by
    rw [posteriorEq, tableLaw, independentProduct_splitAt updated selected]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    apply congrArg (PMF.bind (updated selected))
    funext choice
    simp only [restLaw, PMF.map_comp, Function.comp_def]
    exact congrArg (fun encode => PMF.map encode
      (independentProduct fun point : {point : sites // point ≠ selected} => updated point.val))
        (funext fun rest => resolved choice rest)
  have selectedMarginal := congrArg (PMF.map Prod.fst) factored
  change (posterior.map wholeSplit).map Prod.fst =
    (bindPairLaw (updated selected) fun _ => restLaw).map Prod.fst at selectedMarginal
  rw [bindPairLaw_map_fst, PMF.map_comp] at selectedMarginal
  have selectedLaw : updated selected = assessment.strategy who current := by
    exact selectedMarginal.symm.trans
      (setup.commitRecoveryErasedPolicyPosterior_readout finite assessment mixed history
        running who)
  have remainingMarginal := congrArg (PMF.map Prod.snd) factored
  change (posterior.map wholeSplit).map Prod.snd =
    (bindPairLaw (updated selected) fun _ => restLaw).map Prod.snd at remainingMarginal
  rw [bindPairLaw_const_map_snd, PMF.map_comp] at remainingMarginal
  change posterior.map (fun member =>
    fun other : {other // other ≠ current} => member other.val) = restLaw at remainingMarginal
  rw [selectedLaw, ← remainingMarginal] at factored
  exact factored

end Vegas.SourceProgram.Setup
