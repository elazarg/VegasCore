/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryErasedModel
import Vegas.Game.CommitRecoveryReference
import GameTheory.Protocol.PolicyRandomization
import GameTheory.Protocol.TremblingPlans
import GameTheory.Analysis.Protocol.ExtensiveFormPerfection

/-! # One original policy table on reduced source occurrences -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
/-- Reading reduced coordinates drives the same underlying source protocol
as their full-information lift, from any genuine starting history. -/
theorem commitRecoveryErasedPolicy_runFrom
    (policies : ∀ who, setup.commitRecoveryErasedModel.Policy who)
    (fuel : Nat) (history : setup.commitRecoveryProtocol.History) :
    setup.commitRecoveryModel.runFrom
        (fun who => setup.commitRecoveryErasedPolicy who (policies who)) fuel history =
      setup.commitRecoveryErasedModel.runFrom policies fuel history := by
  have chooser : setup.commitRecoveryModel.historyChooser
        (fun who => setup.commitRecoveryErasedPolicy who (policies who)) =
      setup.commitRecoveryErasedModel.historyChooser policies := by
    funext current running
    apply Subtype.ext
    funext who
    change (policies who (setup.commitRecoveryErasedInformation who
      (setup.commitRecoveryModel.infoOf who current.trace))).val =
        (policies who (setup.commitRecoveryErasedModel.infoOf who current.trace)).val
    rw [setup.commitRecoveryErasedModel_infoOf]
  unfold InformationModel.runFrom
  rw [chooser]

theorem commitRecoveryErasedProfile_runFrom
    (profile : ∀ who, setup.commitRecoveryErasedModel.BehavioralPolicy who)
    (fuel : Nat) (history : setup.commitRecoveryProtocol.History) :
    setup.commitRecoveryModel.runBehavioralFrom
        (setup.commitRecoveryErasedProfile profile) fuel history =
      setup.commitRecoveryErasedModel.runBehavioralFrom profile fuel history := by
  have chooser : setup.commitRecoveryModel.randomizedChooser
        (setup.commitRecoveryErasedProfile profile) =
      setup.commitRecoveryErasedModel.randomizedChooser profile := by
    funext current running
    apply pmf_map_injective Subtype.val_injective
    rw [InformationModel.randomizedChooser, InformationModel.randomizedChooser,
      InformationModel.behavioralJoint_map_val, InformationModel.behavioralJoint_map_val]
    apply congrArg independentProduct
    funext who
    rw [setup.commitRecoveryErasedProfile_raw, setup.commitRecoveryErasedModel_infoOf]
  unfold InformationModel.runBehavioralFrom
  rw [chooser]

/-- The actual full-information mixed policies are the lifts of the same
original reduced tables, rather than fresh draws at later entries. -/
theorem commitRecoveryErasedMixed_runFrom
    (mixed : ∀ who, setup.commitRecoveryErasedModel.MixedPolicy who)
    (fuel : Nat) (history : setup.commitRecoveryProtocol.History) :
    setup.commitRecoveryModel.runMixedFrom
        (fun who => (mixed who).map (setup.commitRecoveryErasedPolicy who)) fuel history =
      setup.commitRecoveryErasedModel.runMixedFrom mixed fuel history := by
  unfold InformationModel.runMixedFrom
  rw [← independentProduct_map, PMF.bind_map]
  apply congrArg (PMF.bind (independentProduct mixed))
  funext policies
  exact setup.commitRecoveryErasedPolicy_runFrom policies fuel history

omit [Fintype Player] in
/-- Filtering the reduced table by its actual decisions is exactly filtering
its full-information lift by the owner's ORIGINAL complete action record. -/
theorem commitRecoveryErasedPolicy_consistent (who : Player)
    (policy : setup.commitRecoveryErasedModel.Policy who)
    (history : setup.commitRecoveryProtocol.History) :
    policy ∈ setup.commitRecoveryErasedModel.Consistent who
        (setup.commitRecoveryErasedModel.ownPlay who history.trace) ↔
      setup.commitRecoveryErasedPolicy who policy ∈ setup.commitRecoveryModel.Consistent who
        (setup.commitRecoveryModel.ownPlay who history.trace) := by
  rw [setup.commitRecoveryErasedModel_ownPlay]
  constructor
  · intro reduced record member
    exact reduced _ (List.mem_map.mpr ⟨record, member, rfl⟩)
  · intro full record member
    obtain ⟨original, recorded, rfl⟩ := List.mem_map.mp member
    exact full original recorded

/-- One table is sampled over reduced coordinates actually occurring in legal
source histories. Unplayed ambient labels are not sampled as though genuine. -/
def commitRecoveryErasedPolicyPlan (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw]
    (profile : ∀ who, setup.commitRecoveryErasedModel.BehavioralPolicy who) (who : Player) :
    setup.commitRecoveryErasedModel.MixedPolicy who := by
  classical
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  exact (profile who).toMixedWithin setup.commitRecoveryErasedModel
    (setup.commitRecoveryErasedModel.playedInformation who)
    ((profile who).supportFallback setup.commitRecoveryErasedModel)

/-- The original reduced-coordinate draw realizes the complete behavioral
history law of the ORIGINAL full-information source game, including resets. -/
theorem commitRecoveryErasedPolicyPlan_run (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw]
    (profile : ∀ who, setup.commitRecoveryErasedModel.BehavioralPolicy who) (fuel : Nat) :
    setup.commitRecoveryModel.runMixed
        (fun who => (setup.commitRecoveryErasedPolicyPlan finite profile who).map
          (setup.commitRecoveryErasedPolicy who)) fuel =
      setup.commitRecoveryModel.runBehavioral (setup.commitRecoveryErasedProfile profile) fuel := by
  classical
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  rw [InformationModel.runMixed, setup.commitRecoveryErasedMixed_runFrom]
  change setup.commitRecoveryErasedModel.runMixed
    (fun who => (profile who).toMixedWithin setup.commitRecoveryErasedModel
      (setup.commitRecoveryErasedModel.playedInformation who)
      ((profile who).supportFallback setup.commitRecoveryErasedModel)) fuel = _
  rw [setup.commitRecoveryErasedModel.runMixed_toMixedWithin
    (setup.commitRecoveryErasedModel.actsOnceWhereItMatters_of_actsOnce
      setup.commitRecoveryErasedModel_actsOnce)
    setup.commitRecoveryErasedModel.playedInformation profile
    (fun who => (profile who).supportFallback setup.commitRecoveryErasedModel) fuel
    (setup.commitRecoveryErasedModel.coversInformationSites_playedInformation fuel)]
  exact (setup.commitRecoveryErasedProfile_runFrom profile fuel
    setup.commitRecoveryProtocol.initHistory).symm

theorem commitRecoveryErasedPolicyPlan_support_finite
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (profile : ∀ who, setup.commitRecoveryErasedModel.BehavioralPolicy who) (who : Player) :
    (setup.commitRecoveryErasedPolicyPlan finite profile who).support.Finite := by
  classical
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  apply InformationModel.BehavioralPolicy.toMixedWithin_support_finite
  intro info _
  let : Finite (setup.commitRecoveryErasedModel.Choice who info) :=
    setup.commitRecovery_finite_choice finite who info
  exact Set.toFinite _

/-- A real source query reads its original reduced coordinate with the chosen
law. Menu transport preserves accepted failure and omission as distinct atoms. -/
theorem commitRecoveryErasedPolicyPlan_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (profile : ∀ who, setup.commitRecoveryErasedModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) (who : Player) :
    (setup.commitRecoveryErasedPolicyPlan finite profile who).map
        (fun policy => (setup.commitRecoveryErasedPolicy who policy
          (setup.commitRecoveryModel.infoOf who history.trace)).val) =
      (setup.commitRecoveryErasedProfile profile who
        (setup.commitRecoveryModel.infoOf who history.trace)).map Subtype.val := by
  classical
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  rw [setup.commitRecoveryErasedProfile_raw]
  change ((profile who).toMixedWithin setup.commitRecoveryErasedModel
    (setup.commitRecoveryErasedModel.playedInformation who)
    ((profile who).supportFallback setup.commitRecoveryErasedModel)).map
      (fun policy => (policy (setup.commitRecoveryErasedInformation who
        (setup.commitRecoveryModel.infoOf who history.trace))).val) = _
  rw [InformationModel.BehavioralPolicy.toMixedWithin_eq_sampleOn,
    ← setup.commitRecoveryErasedModel_infoOf who history.trace]
  have marginal := FiniteAssignment.sampleOn_map_eval_of_mem (profile who)
    (setup.commitRecoveryErasedModel.playedInformation who)
    ((profile who).supportFallback setup.commitRecoveryErasedModel)
    (setup.commitRecoveryErasedModel.mem_playedInformation running)
  simpa only [PMF.map_comp, Function.comp_def] using
    congrArg (fun law => law.map Subtype.val) marginal

open Classical in
/-- Chronological reduced queries have the independent joint law of their
original table coordinates, including every old attempt and accepted failure. -/
theorem commitRecoveryErasedPolicyPlan_record_readout
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (profile : ∀ who, setup.commitRecoveryErasedModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History) (who : Player)
    (keep : setup.commitRecoveryErasedModel.InfoState who × CommitRecoveryMove Player L → Bool) :
    let records := (setup.commitRecoveryErasedModel.ownPlay who history.trace).filter keep
    (setup.commitRecoveryErasedPolicyPlan finite profile who).map
        (fun member (index : Fin records.length) => member records[index.val].1) =
      independentProduct (fun index : Fin records.length => profile who records[index.val].1) := by
  classical
  intro records
  let := setup.commitRecovery_finite_history finite
  let := Fintype.ofFinite setup.commitRecoveryProtocol.History
  let model := setup.commitRecoveryErasedModel
  let policy := profile who
  let sites := model.playedInformation who
  let fallback := policy.supportFallback model
  have distinct : ((model.ownPlay who history.trace).map Prod.fst).Nodup := by
    rw [← model.actedAt_eq_map_ownPlay]
    exact setup.commitRecoveryErasedModel_actsOnce who history.trace
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
  have original : setup.commitRecoveryErasedPolicyPlan finite profile who =
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

end Vegas.SourceProgram.Setup
