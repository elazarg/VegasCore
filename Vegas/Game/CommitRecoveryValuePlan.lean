/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryValuePolicy
import GameTheory.Protocol.PolicyRandomization
import GameTheory.Protocol.TremblingPlans
import GameTheory.Analysis.Protocol.ExtensiveFormPerfection
import GameTheoryExtensions.Analysis.Protocol.Bayes
import GameTheoryExtensions.Math.Probability.ProductExpectation

/-! # One original ordinary source policy predrawn across all source sites -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
private theorem ordinary_history_finite [Finite Player]
    (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] :
    Finite (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).History := by
  classical
  let model := setup.informationModel (CommitmentInterface.forfeiture setup.program)
  let reference : model.BehavioralAssessment := .ofStrategy fun who info =>
    let := setup.finite_choice finite (CommitmentInterface.forfeiture setup.program) who info
    let := Fintype.ofFinite (model.Choice who info)
    let := setup.choice_nonempty (CommitmentInterface.forfeiture setup.program) who info
    PMF.uniformOfFintype _
  have mixed : reference.IsFullyMixed := by
    intro who site choice
    let := setup.finite_choice finite (CommitmentInterface.forfeiture setup.program) who site.1
    let := Fintype.ofFinite (model.Choice who site.1)
    let := setup.choice_nonempty (CommitmentInterface.forfeiture setup.program) who site.1
    exact PMF.mem_support_uniformOfFintype choice
  exact mixed.finite_history (setup.protocol_bounded _)
    (fun who info => by
      let := setup.finite_choice finite (CommitmentInterface.forfeiture setup.program) who info
      exact Set.toFinite _)
    (fun {state} draw => setup.protocolStep_support_finite state draw.1)

/-- Predraw one complete ordinary source policy at every played source site.
This is the existing finite-site sampling construction, shared across all
later physical blocks; it never resamples the private initial draw. -/
def commitRecoveryValuePlan (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (who : Player) :
    PMF ((setup.informationModel (CommitmentInterface.forfeiture setup.program)).Policy who) := by
  classical
  let := ordinary_history_finite setup finite
  let := Fintype.ofFinite
    (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).History
  let model := setup.informationModel (CommitmentInterface.forfeiture setup.program)
  let policy := setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who
  exact policy.toMixedWithin model (model.playedInformation who) (policy.supportFallback model)

/-- The original global policy draw has the exact conditional ordinary action
law at every genuine clear source input, including inputs outside intended play. -/
theorem commitRecoveryValuePlan_clear_readout (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History)
    (clear : setup.CommitRecoveryClear history.state)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) (who : Player) :
    (setup.commitRecoveryValuePlan finite wellFormed profile who).map
        (fun member => member (setup.commitRecoveryPrivate who history.state)) =
      setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who
        (setup.commitRecoveryPrivate who history.state) := by
  classical
  let := ordinary_history_finite setup finite
  let := Fintype.ofFinite
    (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).History
  let model := setup.informationModel (CommitmentInterface.forfeiture setup.program)
  let policy := setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who
  have sourceRunning : ¬ (setup.executionProtocol
      (CommitmentInterface.forfeiture setup.program)).terminal
        (setup.commitRecoverySourceState history.state) := by
    cases state : history.state with
    | none => exact id
    | some current =>
        rw [state] at running
        exact running
  have played := model.mem_playedInformation (who := who)
    (history := ⟨_, setup.commitRecoveryClearTrace history.trace clear⟩) sourceRunning
  rw [setup.commitRecoveryClearTrace_observe] at played
  change (policy.toMixedWithin model (model.playedInformation who)
    (policy.supportFallback model)).map _ = _
  rw [InformationModel.BehavioralPolicy.toMixedWithin_eq_sampleOn]
  exact FiniteAssignment.sampleOn_map_eval_of_mem policy (model.playedInformation who)
    (policy.supportFallback model) played

/-- The SAME original global source-policy draw reconstructs every actual
clear auxiliary local law when combined with its original fresh omission draw.
This is an unconditioned prior identity; own-recall conditioning remains explicit. -/
theorem commitRecoveryValuePlan_clear_law (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (history : setup.commitRecoveryProtocol.History)
    (clear : setup.CommitRecoveryClear history.state)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) (who : Player) :
    (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).bind
        (fun member => setup.commitRecoveryValuePolicy wellFormed assessment.strategy who member
          (setup.commitRecoveryClearInformation wellFormed who
            (setup.commitRecoveryPrivate who history.state))) =
      assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (setup.commitRecoveryPrivate who history.state)) :=
  setup.commitRecoveryValuePolicy_clear_mixture wellFormed assessment mixed history clear running
    who _ (setup.commitRecoveryValuePlan_clear_readout finite wellFormed assessment.strategy
      history clear running who)


/-- One immutable original source-policy profile realizes the entire ordinary
chronological history law. The original private draw is still inside that
history; no independent source entry is selected at later physical blocks. -/
theorem commitRecoveryValuePlan_source_run
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who) (fuel : Nat) :
    (setup.informationModel (CommitmentInterface.forfeiture setup.program)).runMixed
        (fun who => setup.commitRecoveryValuePlan finite wellFormed profile who) fuel =
      (setup.informationModel (CommitmentInterface.forfeiture setup.program)).runBehavioral
        (fun who => setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who) fuel := by
  classical
  let := ordinary_history_finite setup finite
  let := Fintype.ofFinite
    (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).History
  let model := setup.informationModel (CommitmentInterface.forfeiture setup.program)
  let policy := fun who => setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who
  change model.runMixed (fun who => (policy who).toMixedWithin model
    (model.playedInformation who) ((policy who).supportFallback model)) fuel = _
  exact model.runMixed_toMixedWithin
    (setup.protocol_decisionRecall _).actsOnceWhereItMatters model.playedInformation policy
    (fun who => (policy who).supportFallback model) fuel
    (model.coversInformationSites_playedInformation fuel)

open Classical in
/-- The current source choice is independent of the complete remaining
ORIGINAL source policy. The right marginal retains every earlier and future
coordinate; it is not a new policy drawn at a later physical entry. -/
theorem commitRecoveryValuePlan_split (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : setup.commitRecoveryProtocol.History)
    (clear : setup.CommitRecoveryClear history.state)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state) (who : Player) :
    let view := setup.commitRecoveryPrivate who history.state
    let choices := fun point : setup.ProtocolView who => (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Choice who point
    let original := setup.commitRecoveryValuePlan finite wellFormed profile who
    original.map (Equiv.piSplitAt view choices) =
      (setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who view).bind
        (fun choice => (original.map fun member =>
          fun other : {other // other ≠ view} => member other.val).map (Prod.mk choice)) := by
  classical
  intro view choices original
  let := ordinary_history_finite setup finite
  let := Fintype.ofFinite
    (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).History
  let model := setup.informationModel (CommitmentInterface.forfeiture setup.program)
  let policy := setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who
  let sites : Finset (setup.ProtocolView who) := model.playedInformation who
  let fallback : ∀ point, choices point := policy.supportFallback model
  have sourceRunning : ¬ (setup.executionProtocol
      (CommitmentInterface.forfeiture setup.program)).terminal
        (setup.commitRecoverySourceState history.state) := by
    cases state : history.state with
    | none => exact id
    | some current => rw [state] at running; exact running
  have played := model.mem_playedInformation (who := who)
    (history := ⟨_, setup.commitRecoveryClearTrace history.trace clear⟩) sourceRunning
  rw [setup.commitRecoveryClearTrace_observe] at played
  let selected : sites := ⟨view, played⟩
  let laws : ∀ info : sites, PMF (choices info.val) := fun info => policy info.val
  let resolve : ((info : sites) → choices info.val) → ∀ point, choices point :=
    FiniteAssignment.resolve fallback sites
  let wholeSplit := Equiv.piSplitAt view choices
  let finiteSplit := Equiv.piSplitAt selected (fun info : sites => choices info.val)
  let remaining := fun rest =>
    (wholeSplit (resolve (finiteSplit.symm (fallback view, rest)))).2
  let restLaw := (independentProduct (fun info : {info : sites // info ≠ selected} =>
    laws info.val)).map remaining
  have resolved (choice : choices view) (rest) :
      wholeSplit (resolve (finiteSplit.symm (choice, rest))) = (choice, remaining rest) := by
    apply Prod.ext
    · change resolve (finiteSplit.symm (choice, rest)) view = choice
      dsimp only [resolve]
      rw [FiniteAssignment.resolve_of_mem fallback sites _ played]
      simp [finiteSplit, selected, Equiv.piSplitAt, view]
    · funext other
      change resolve (finiteSplit.symm (choice, rest)) other.val =
        resolve (finiteSplit.symm (fallback view, rest)) other.val
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
  have originalLaw : original = (independentProduct laws).map resolve := by
    change policy.toMixedWithin model sites fallback = _
    rw [InformationModel.BehavioralPolicy.toMixedWithin_eq_sampleOn]
    unfold FiniteAssignment.sampleOn
    congr 1
    funext draw point
    by_cases present : point ∈ sites
    · simp only [resolve, FiniteAssignment.resolve, dite_eq_left present]
    · simp only [resolve, FiniteAssignment.resolve, dite_eq_right present]
  have factored : original.map wholeSplit =
      (policy view).bind (fun choice => restLaw.map (Prod.mk choice)) := by
    rw [originalLaw, independentProduct_splitAt laws selected]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
    change (policy view).bind _ = _
    apply congrArg (PMF.bind (policy view))
    funext choice
    simp only [restLaw, PMF.map_comp, Function.comp_def]
    exact congrArg (fun encode => PMF.map encode
      (independentProduct fun info : {info : sites // info ≠ selected} => laws info.val))
        (funext fun rest => resolved choice rest)
  have marginal : original.map (fun member =>
      fun other : {other // other ≠ view} => member other.val) = restLaw := by
    have projected := congrArg (PMF.map Prod.snd) factored
    change (original.map wholeSplit).map Prod.snd =
      (bindPairLaw (policy view) fun _ => restLaw).map Prod.snd at projected
    rw [bindPairLaw_const_map_snd, PMF.map_comp] at projected
    exact projected
  rw [marginal]
  exact factored

open Classical in
/-- Read ALL binding decisions on one genuine source history from the SAME
original global policy. Repeated owners retain their distinct full source
views; their coordinates are not resampled at physical block boundaries. -/
theorem commitRecoveryValuePlan_binding_readout (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).History)
    (who : Player) :
    let model := setup.informationModel (CommitmentInterface.forfeiture setup.program)
    let records := (model.ownPlay who history.trace).filter fun record =>
      match record.2 with
      | .commit _ _ _ _ => true
      | .reveal _ _ _ => false
    (setup.commitRecoveryValuePlan finite wellFormed profile who).map
        (fun member (index : Fin records.length) => member records[index.val].1) =
      independentProduct (fun index : Fin records.length =>
        setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who
          records[index.val].1) := by
  classical
  intro model records
  let := ordinary_history_finite setup finite
  let := Fintype.ofFinite
    (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).History
  let policy := setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who
  let sites := model.playedInformation who
  let fallback := policy.supportFallback model
  have distinct : ((model.ownPlay who history.trace).map Prod.fst).Nodup := by
    rw [← model.actedAt_eq_map_ownPlay]
    exact (setup.protocol_decisionRecall _).actsOnceAtEachInfoState who history.trace
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
  have original : setup.commitRecoveryValuePlan finite wellFormed profile who =
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
/-- Averaging the complete binding-content constraints of a genuine source
history under the ORIGINAL global policy prior gives precisely the source
binding atom product. Failed typed binding choices are retained. -/
theorem commitRecoveryValuePlan_binding_likelihood (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (history : (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).History)
    (who : Player) :
    let model := setup.informationModel (CommitmentInterface.forfeiture setup.program)
    let records := (model.ownPlay who history.trace).filter fun record =>
      match record.2 with
      | .commit _ _ _ _ => true
      | .reveal _ _ _ => false
    expect (setup.commitRecoveryValuePlan finite wellFormed profile who)
        (fun member => ∏ index : Fin records.length,
          if some records[index.val].2 = (member records[index.val].1).val then 1 else 0) =
      ∏ index : Fin records.length,
        (((setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who
          records[index.val].1).map Subtype.val) (some records[index.val].2)).toReal := by
  classical
  intro model records
  let readout := fun (member : model.Policy who) (index : Fin records.length) =>
    member records[index.val].1
  let payoff := fun (index : Fin records.length) (choice : model.Choice who records[index.val].1) =>
    if some records[index.val].2 = choice.val then (1 : ℝ) else 0
  have joint := setup.commitRecoveryValuePlan_binding_readout finite wellFormed profile history who
  change (setup.commitRecoveryValuePlan finite wellFormed profile who).map readout = _ at joint
  calc
    _ = expect ((setup.commitRecoveryValuePlan finite wellFormed profile who).map readout)
        (fun choices => ∏ index, payoff index (choices index)) := (expect_map _ _ _).symm
    _ = expect (independentProduct fun index : Fin records.length =>
        setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who records[index.val].1)
        (fun choices => ∏ index, payoff index (choices index)) := by rw [joint]
    _ = ∏ index : Fin records.length, expect
        (setup.commitRecoveryNonmissingSourcePolicy wellFormed profile who records[index.val].1)
        (payoff index) := expect_independentProduct_prod _ payoff
          (fun _ _ => by dsimp only [payoff]; split <;> norm_num)
          (fun _ _ => by dsimp only [payoff]; split <;> norm_num)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro index _
      have same : payoff index = fun choice : model.Choice who records[index.val].1 =>
          @ite ℝ (some records[index.val].2 = choice.val) (Classical.propDecidable _) 1 0 := by
        funext choice
        by_cases equal : some records[index.val].2 = choice.val <;>
          simp only [payoff, equal, ite_true, ite_false]
      rw [same]
      exact (toReal_map_apply Subtype.val _ (some records[index.val].2)).symm

end Vegas.SourceProgram.Setup
