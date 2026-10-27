/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ConditionedSourceReach
import GameTheoryExtensions.Analysis.Protocol.ProportionalBeliefTransport

/-! # Exact Bayes beliefs on actual conditional source components

The selected information fiber must determine the initial component. This is
an information hypothesis on the actual source views, not an added public
observation. All likelihood accounting uses the original source protocols.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open scoped ENNReal

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  {Signal : Type*} (signal : State L setup.context → Signal) (value : Signal)
  (supported : value ∈ (setup.initialLaw.map signal).support)

/-- The same genuine decision view in the original source protocol. -/
def conditionInitial_informationSite {who : Player}
    (site : (setup.conditionInitial signal value).intendedModel.InformationSite who) :
    setup.intendedModel.InformationSite who := by
  refine ⟨site.1, ?_⟩
  obtain ⟨history, running, action, permitted⟩ := site.2
  refine ⟨setup.conditionInitial_informationHistory signal value supported who site.1 history,
    running, action, ?_⟩
  change some action ∈ setup.intendedMenu who site.1
  rw [← setup.conditionInitial_intendedMenu signal value who site.1]
  exact permitted

open Classical in
private theorem conditionInitial_information_reach_fiber
    (supported : value ∈ (setup.initialLaw.map signal).support)
    (policies : ∀ who, setup.intendedModel.BehavioralPolicy who) {who : Player}
    (site : (setup.conditionInitial signal value).intendedModel.InformationSite who)
    (inside : ∀ history : setup.intendedModel.InformationHistory who site.1,
      setup.initialComponent signal value history.1.state)
    (history : setup.intendedModel.InformationHistory who site.1) :
    ((setup.initialLaw.map signal) value)⁻¹ *
        setup.intendedModel.historyReachWeight policies history.1 =
      ∑' original : (setup.conditionInitial signal value).intendedModel.InformationHistory
        who site.1,
        if setup.conditionInitial_history signal value supported original.1 = history.1 then
          (setup.conditionInitial signal value).intendedModel.historyReachWeight
            (fun who => setup.conditionInitial_policy signal value who (policies who)) original.1
        else 0 := by
  obtain ⟨original, same⟩ := setup.conditionInitial_informationHistory_surjective signal value
    supported who site.1 inside history
  subst history
  have notRoot : original.1.state ≠ none := by
    intro root
    have active := InformationModel.InformationSite.active
      (M := (setup.conditionInitial signal value).intendedModel) site original
    rw [root] at active
    exact active
  have positive := (setup.conditionInitial signal value).intended_trace_positive
    original.1.trace notRoot
  have scaled := setup.conditionInitial_historyReachWeight_scale signal value supported policies
    original.1.trace positive
  rw [tsum_eq_single original]
  · simp only [conditionInitial_informationHistory, ↓reduceIte]
    change ((setup.initialLaw.map signal) value)⁻¹ *
      setup.intendedModel.historyReachWeight policies
        ⟨original.1.state, setup.conditionInitial_trace signal value supported original.1.trace⟩ = _
    rw [scaled, ← mul_assoc, ENNReal.inv_mul_cancel
      ((PMF.mem_support_iff _ _).mp supported) (PMF.apply_ne_top _ _), one_mul]
  · intro other different
    rw [ite_eq_right]
    intro same
    apply different
    apply Subtype.ext
    exact setup.conditionInitial_history_injective signal value supported same

/-- The actual conditional information mass differs only by the initial
component's scalar. In particular positive global mass gives positive
conditional mass. -/
theorem conditionInitial_informationMass
    (policies : ∀ who, setup.intendedModel.BehavioralPolicy who) {who : Player}
    (site : (setup.conditionInitial signal value).intendedModel.InformationSite who)
    (inside : ∀ history : setup.intendedModel.InformationHistory who site.1,
      setup.initialComponent signal value history.1.state) :
    (setup.conditionInitial signal value).intendedModel.informationMass
        (fun who => setup.conditionInitial_policy signal value who (policies who)) who site =
      ((setup.initialLaw.map signal) value)⁻¹ *
        setup.intendedModel.informationMass policies who
          (setup.conditionInitial_informationSite signal value supported site) := by
  classical
  exact InformationModel.informationMass_projection_of_proportional_reach
    (setup.conditionInitial signal value).intendedModel setup.intendedModel
    (fun who => setup.conditionInitial_policy signal value who (policies who)) policies
    (setup.conditionInitial_history signal value supported) who site
    (setup.conditionInitial_informationSite signal value supported site)
    (fun history member =>
      (setup.conditionInitial_history_observed signal value supported history who).trans member)
    _ (setup.conditionInitial_information_reach_fiber signal value supported policies site inside)

/-- Exact Bayes beliefs transport through the genuine source-history map.
The two positivity arguments are normalization certificates; the preceding
mass identity derives the conditional one from the global one. -/
theorem conditionInitial_bayesBelief
    (policies : ∀ who, setup.intendedModel.BehavioralPolicy who) {who : Player}
    (site : (setup.conditionInitial signal value).intendedModel.InformationSite who)
    (inside : ∀ history : setup.intendedModel.InformationHistory who site.1,
      setup.initialComponent signal value history.1.state)
    (conditionalAntichain : site.IsHistoryAntichain)
    (globalAntichain : (setup.conditionInitial_informationSite signal value supported
      site).IsHistoryAntichain)
    (conditionalPositive : 0 < (setup.conditionInitial signal value).intendedModel.informationMass
      (fun who => setup.conditionInitial_policy signal value who (policies who)) who site)
    (globalPositive : 0 < setup.intendedModel.informationMass policies who
      (setup.conditionInitial_informationSite signal value supported site)) :
    ((setup.conditionInitial signal value).intendedModel.bayesBelief
      (fun who => setup.conditionInitial_policy signal value who (policies who)) who site
        conditionalAntichain conditionalPositive).map
          (setup.conditionInitial_informationHistory signal value supported who site.1) =
      setup.intendedModel.bayesBelief policies who
        (setup.conditionInitial_informationSite signal value supported site)
          globalAntichain globalPositive := by
  classical
  exact InformationModel.bayesBelief_projection_of_proportional_reach
    (setup.conditionInitial signal value).intendedModel setup.intendedModel
    (fun who => setup.conditionInitial_policy signal value who (policies who)) policies
    (setup.conditionInitial_history signal value supported) who site
    (setup.conditionInitial_informationSite signal value supported site)
    (fun history member =>
      (setup.conditionInitial_history_observed signal value supported history who).trans member)
    _ (setup.conditionInitial_information_reach_fiber signal value supported policies site inside)
    (ENNReal.inv_ne_zero.mpr (PMF.apply_ne_top _ _)) conditionalAntichain globalAntichain
    globalPositive

end Vegas.SourceProgram.Setup
