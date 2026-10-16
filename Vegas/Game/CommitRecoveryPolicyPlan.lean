/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryReference
import GameTheory.Protocol.PolicyRandomization
import GameTheory.Protocol.TremblingPlans
import GameTheory.Analysis.Protocol.ExtensiveFormPerfection
import GameTheoryExtensions.Math.Probability.ProductExpectation

/-! # Original policy draws on complete source recovery information -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Draw one complete recovery policy before initialization. The coordinates
retain the entire source signal and own-action record, including all retries.
The private setup draw remains inside the original execution protocol. -/
def commitRecoveryPolicyPlan (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw]
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (who : Player) :
    setup.commitRecoveryModel.MixedPolicy who := by
  classical
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  exact (profile who).toMixedWithin setup.commitRecoveryModel
    (setup.commitRecoveryModel.playedInformation who)
    ((profile who).supportFallback setup.commitRecoveryModel)

/-- The single original draw realizes the complete recovery history law,
including initialization, omitted bindings, failed openings and retries. -/
theorem commitRecoveryPolicyPlan_run (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw]
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (fuel : Nat) :
    setup.commitRecoveryModel.runMixed
        (setup.commitRecoveryPolicyPlan finite profile) fuel =
      setup.commitRecoveryModel.runBehavioral profile fuel := by
  classical
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  change setup.commitRecoveryModel.runMixed
    (fun who => (profile who).toMixedWithin setup.commitRecoveryModel
      (setup.commitRecoveryModel.playedInformation who)
      ((profile who).supportFallback setup.commitRecoveryModel)) fuel = _
  exact setup.commitRecoveryModel.runMixed_toMixedWithin
    (setup.commitRecoveryModel.decisionRecall_of_perfectRecall
      setup.commitRecoveryModel_perfectRecall).actsOnceWhereItMatters
    setup.commitRecoveryModel.playedInformation profile
    (fun who => (profile who).supportFallback setup.commitRecoveryModel) fuel
    (setup.commitRecoveryModel.coversInformationSites_playedInformation fuel)

/-- Every original recovery policy law has finite support, despite the
ambient full-information carrier containing unrealizable signal words. -/
theorem commitRecoveryPolicyPlan_support_finite
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (who : Player) :
    (setup.commitRecoveryPolicyPlan finite profile who).support.Finite := by
  classical
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  apply InformationModel.BehavioralPolicy.toMixedWithin_support_finite
  intro info _
  let := setup.commitRecovery_finite_choice finite who info
  exact Set.toFinite _

/-- A genuine recovery occurrence reads its own original coordinate, even
when that occurrence follows exclusions or a restored commitment attempt. -/
theorem commitRecoveryPolicyPlan_readout (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw]
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) (who : Player) :
    (setup.commitRecoveryPolicyPlan finite profile who).map
        (fun member => member (setup.commitRecoveryModel.infoOf who history.trace)) =
      profile who (setup.commitRecoveryModel.infoOf who history.trace) := by
  classical
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  change ((profile who).toMixedWithin setup.commitRecoveryModel
    (setup.commitRecoveryModel.playedInformation who)
    ((profile who).supportFallback setup.commitRecoveryModel)).map _ = _
  rw [InformationModel.BehavioralPolicy.toMixedWithin_eq_sampleOn]
  exact FiniteAssignment.sampleOn_map_eval_of_mem _ _ _
    (setup.commitRecoveryModel.mem_playedInformation running)

open Classical in
/-- Read the selected actual decisions of one owner jointly from its single
original policy. Selection does not discard the full query information or
the original missing flag carried by each recorded action. -/
theorem commitRecoveryPolicyPlan_record_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History) (who : Player)
    (keep : setup.commitRecoveryModel.InfoState who × CommitRecoveryMove Player L → Bool) :
    let records := (setup.commitRecoveryModel.ownPlay who history.trace).filter keep
    (setup.commitRecoveryPolicyPlan finite profile who).map
        (fun member (index : Fin records.length) => member records[index.val].1) =
      independentProduct (fun index : Fin records.length => profile who records[index.val].1) := by
  classical
  intro records
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  let model := setup.commitRecoveryModel
  let policy := profile who
  let sites := model.playedInformation who
  let fallback := policy.supportFallback model
  have distinct : ((model.ownPlay who history.trace).map Prod.fst).Nodup := by
    rw [← model.actedAt_eq_map_ownPlay]
    exact (model.decisionRecall_of_perfectRecall
      setup.commitRecoveryModel_perfectRecall).actsOnceAtEachInfoState who history.trace
  have restricted : (records.map Prod.fst).Nodup :=
    distinct.sublist ((List.filter_sublist).map Prod.fst)
  have played (index : Fin records.length) : records[index.val].1 ∈ sites := by
    have recorded : records[index.val] ∈ model.ownPlay who history.trace :=
      List.mem_of_mem_filter (List.getElem_mem index.isLt)
    obtain ⟨site, observed, _⟩ := model.exists_informationSite_of_mem_ownPlay history.trace recorded
    obtain ⟨prior, running, _⟩ := site.2
    have present := model.mem_playedInformation (who := who) (history := prior.1) running
    rw [prior.2, observed] at present
    exact present
  let selected : Fin records.length ↪ sites :=
    ⟨fun index => ⟨records[index.val].1, played index⟩, by
      intro first second same
      apply Fin.ext
      apply (List.Nodup.getElem_inj_iff restricted
        (i := first.val) (hi := by simpa only [List.length_map] using first.isLt)
        (j := second.val) (hj := by simpa only [List.length_map] using second.isLt)).mp
      simp only [List.getElem_map]
      exact congrArg Subtype.val same⟩
  let laws : ∀ point : sites, PMF (model.Choice who point.val) := fun point => policy point.val
  let resolve := FiniteAssignment.resolve fallback sites
  have original : setup.commitRecoveryPolicyPlan finite profile who =
      (independentProduct laws).map resolve := by
    change policy.toMixedWithin model sites fallback = _
    rw [InformationModel.BehavioralPolicy.toMixedWithin_eq_sampleOn]
    rfl
  rw [original, PMF.map_comp]
  have projection : (fun draw (index : Fin records.length) => resolve draw records[index.val].1) =
      (fun draw (index : Fin records.length) => draw (selected index)) := by
    funext draw index
    exact FiniteAssignment.resolve_of_mem fallback sites draw (played index)
  change (independentProduct laws).map
    (fun draw (index : Fin records.length) => resolve draw records[index.val].1) = _
  rw [projection]
  exact independentProduct_map_embedding selected laws

open Classical in
/-- The original policy prior assigns the actual recorded choices exactly
their chronological source likelihood. Accepted failures and omissions are
distinct recorded actions, including in retired attempts. -/
theorem commitRecoveryPolicyPlan_record_likelihood
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History) (who : Player)
    (keep : setup.commitRecoveryModel.InfoState who × CommitRecoveryMove Player L → Bool) :
    let records := (setup.commitRecoveryModel.ownPlay who history.trace).filter keep
    expect (setup.commitRecoveryPolicyPlan finite profile who)
        (fun member => ∏ index : Fin records.length,
          if some records[index.val].2 = (member records[index.val].1).val then 1 else 0) =
      ∏ index : Fin records.length,
        (((profile who records[index.val].1).map Subtype.val)
          (some records[index.val].2)).toReal := by
  classical
  intro records
  let readout := fun (member : setup.commitRecoveryModel.Policy who)
    (index : Fin records.length) => member records[index.val].1
  let payoff := fun (index : Fin records.length)
    (choice : setup.commitRecoveryModel.Choice who records[index.val].1) =>
      if some records[index.val].2 = choice.val then (1 : ℝ) else 0
  have joint := setup.commitRecoveryPolicyPlan_record_readout finite profile history who keep
  change (setup.commitRecoveryPolicyPlan finite profile who).map readout = _ at joint
  calc
    _ = expect ((setup.commitRecoveryPolicyPlan finite profile who).map readout)
        (fun choices => ∏ index, payoff index (choices index)) := (expect_map _ _ _).symm
    _ = expect (independentProduct fun index : Fin records.length =>
        profile who records[index.val].1)
        (fun choices => ∏ index, payoff index (choices index)) := by rw [joint]
    _ = ∏ index : Fin records.length, expect
        (profile who records[index.val].1) (payoff index) :=
      expect_independentProduct_prod _ payoff
        (fun _ _ => by dsimp only [payoff]; split <;> norm_num)
        (fun _ _ => by dsimp only [payoff]; split <;> norm_num)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro index _
      have same : payoff index = fun choice : setup.commitRecoveryModel.Choice who
          records[index.val].1 =>
            @ite ℝ (some records[index.val].2 = choice.val) (Classical.propDecidable _) 1 0 := by
        funext choice
        by_cases equal : some records[index.val].2 = choice.val <;>
          simp only [payoff, equal, ite_true, ite_false]
      rw [same]
      exact (toReal_map_apply Subtype.val _ (some records[index.val].2)).symm

end Vegas.SourceProgram.Setup
