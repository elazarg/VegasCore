module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ConditionedSourceBayes

@[expose] public section

/-! # Continuation play on a component of the source initial law -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open scoped ENNReal

variable {Player : Type} [DecidableEq Player] [Finite Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  {Signal : Type*} (signal : State L setup.context → Signal) (value : Signal)
  (supported : value ∈ (setup.initialDistribution.map signal).support)

/-- After initialization, restricting to a supported component preserves the full
history law of every continuation, for every behavioral profile and fuel. -/
theorem conditionInitial_runBehavioralFrom
    (policies : ∀ who, setup.intendedModel.BehavioralPolicy who) (fuel : Nat)
    (history : (setup.conditionInitial signal value).intendedProtocol.History)
    (started : history.state ≠ none) :
    (((setup.conditionInitial signal value).intendedModel.runBehavioralFrom
      (fun who => setup.conditionInitial_policy signal value who (policies who)) fuel history).map
        (setup.conditionInitial_history signal value supported)) =
      setup.intendedModel.runBehavioralFrom policies fuel
        (setup.conditionInitial_history signal value supported history) := by
  classical
  induction fuel generalizing history with
  | zero => exact PMF.pure_map _ _
  | succ fuel ih =>
    obtain ⟨_ | point, trace⟩ := history
    · exact (started rfl).elim
    let h : (setup.conditionInitial signal value).intendedProtocol.History := ⟨some point, trace⟩
    by_cases terminal : (setup.conditionInitial signal value).intendedProtocol.terminal h.state
    · rw [InformationModel.runBehavioralFrom_of_terminal _ _ _ terminal,
        setup.intendedModel.runBehavioralFrom_of_terminal policies _
          (h := setup.conditionInitial_history signal value supported h) terminal, PMF.pure_map]
    rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ _ terminal,
      setup.intendedModel.runBehavioralFrom_succ_of_not_terminal policies _
        (h := setup.conditionInitial_history signal value supported h) terminal, PMF.map_bind]
    have jointEq :
        (setup.conditionInitial signal value).intendedModel.behavioralJoint
          (fun who => setup.conditionInitial_policy signal value who (policies who))
          trace terminal =
        setup.intendedModel.behavioralJoint policies
          (setup.conditionInitial_trace signal value supported trace) terminal := by
      ext joint
      apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
      exact (setup.conditionInitial_behavioralJoint_probability signal value supported policies
        trace joint.1 joint.2).symm
    rw [jointEq]
    apply congrArg
    funext draw
    rw [map_bindOnSupport]
    apply bindOnSupport_congr
    intro after realized
    apply ih
    intro root
    change after = none at root
    exact (setup.conditionInitial signal value).protocolStep_not_none h.state draw.1
      (root ▸ realized)

end Vegas.SourceProgram.Setup
