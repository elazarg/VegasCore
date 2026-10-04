/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceSourceSites
import Vegas.Game.SourceServiceCleanPrefixLaw

/-! # Clean-prefix laws after completing source-compatible prescriptions

A risk-menu behavioral profile may differ from prescribed turn-counted play
outside source-compatible information. Its exact initialized clean-prefix
probabilities still agree with the prescription. Positive prescribed actor
prefixes supply compatibility through actual initialized physical support;
zero-mass predecessors cannot acquire a clean branch under the completion.
The endpoint may be a late opportunity before any response has latched risk.
No posterior, rationality or source-equilibrium assumption enters this law.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

/-- Every positive prescribed clean actor prefix with a protected current
input is classified by its actual initialized physical execution. Timing may
include earlier deferrals; no agreement at other hidden histories is needed. -/
theorem turnPolicy_sourceCompatibleInfo_of_clean_support
    (turns : Nat) (timing : TurnTiming service.setup turns)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (fuel : Nat)
    (history : ((service.bounds.riskMenu (runtime service.setup) service.leaks
      service.bound).protocol (initialLaw service.setup) service.horizon service.scheduler).History)
    (reached : history ∈
      (((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).runBehavioral
          (fun who => (service.bounds.riskMenu (runtime service.setup) service.leaks
            service.bound).restrictPolicy (initialLaw service.setup) service.horizon
              service.scheduler who (sourceServiceTurnPolicy service.setup service.leaks
                service.bound turns timing profile who)) fuel).support)
    (clear : (runtime service.setup).AllPersistentServiceRiskClear service.leaks service.bound
      history.state)
    (who : Player)
    (active : ((service.bounds.riskMenu (runtime service.setup) service.leaks
      service.bound).protocol (initialLaw service.setup) service.horizon service.scheduler).active
        history.state who)
    (inputClear : ∀ control, history.state = some control →
      (runtime service.setup).serviceRisk service.leaks service.bound who
        (control.execution.recall who)
        (control.execution.observe (application service.setup service.leaks) who) = false) :
    service.sourceCompatibleInfo who
      (((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).infoOf who
          history.trace) := by
  let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
  let raw := (application service.setup service.leaks).information (initialLaw service.setup)
    service.horizon service.scheduler
  let players := sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing
    profile
  let rawHistory := menu.toRawHistory (initialLaw service.setup) service.horizon service.scheduler
    history
  have mappedPositive :
      (((menu.information (initialLaw service.setup) service.horizon
        service.scheduler).runBehavioral
        (fun owner => menu.restrictPolicy (initialLaw service.setup) service.horizon
          service.scheduler owner (players owner)) fuel).map
        (menu.toRawHistory (initialLaw service.setup) service.horizon service.scheduler))
          rawHistory ≠ 0 := by
    rw [pmf_map_apply_of_injective _ (menu.toRawHistory_injective _ _ _)]
    exact (PMF.mem_support_iff _ _).mp reached
  have physicalMass := sourceServiceTurnPolicy_cleanPrefix_probability service.bounds service.values
    service.initialValues service.capacity service.bound turns timing profile permitted
      service.horizon service.scheduler fuel rawHistory clear
  have physicallyReached : rawHistory ∈
      (raw.runBehavioral (fun owner =>
        (application service.setup service.leaks).encodePolicy (players owner)) fuel).support := by
    apply (PMF.mem_support_iff _ _).mpr
    exact physicalMass ▸ mappedPositive
  have stateReached : history.state ∈ ((raw.runBehavioral (fun owner =>
      (application service.setup service.leaks).encodePolicy (players owner)) fuel).map
        History.state).support := PMF.support_map .. ▸ ⟨rawHistory, physicallyReached, rfl⟩
  change history.state ∈ ((raw.runBehavioralFrom (fun owner =>
      (application service.setup service.leaks).encodePolicy (players owner)) fuel
      ((application service.setup service.leaks).protocol (initialLaw service.setup) service.horizon
        service.scheduler).initHistory).map History.state).support at stateReached
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom raw
      ((application service.setup service.leaks).singleMover (initialLaw service.setup)
        service.horizon service.scheduler),
    (application service.setup service.leaks).run_map_state] at stateReached
  have actual := (application service.setup service.leaks).roundSupported_iterate_controlStep
    (initialLaw service.setup) service.horizon service.scheduler players fuel history.state
      stateReached
  have atState :
      (menu.information (initialLaw service.setup) service.horizon service.scheduler).infoOf who
        history.trace = (application service.setup service.leaks).observe who history.state :=
    menu.info (initialLaw service.setup) service.horizon service.scheduler who history.trace
  suffices service.sourceCompatibleInfo who
      ((application service.setup service.leaks).observe who history.state) from atState.symm ▸ this
  cases current : history.state with
  | none => rw [current] at active; cases active
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      rw [current] at active
      change actor = some who at active
      subst actor
      refine ⟨profile, turns, timing, permitted, effective, history, remaining, execution, current,
        ?_, actual, ?_, inputClear _ current⟩
      · exact atState.trans
          (congrArg ((application service.setup service.leaks).observe who) current)
      · intro owner
        exact clear _ current owner

omit [DecidableEq Player] in
private theorem pointMass_eq_of_reachWeight_eq
    {E : ExecutionProtocol Player} (model : InformationModel E)
    (first second : ∀ who, model.BehavioralPolicy who) (history : E.History)
    (same : model.historyReachWeight first history = model.historyReachWeight second history)
    (fuel : Nat) : model.runBehavioral first fuel history =
      model.runBehavioral second fuel history := by
  change E.runRandomizedFor (model.randomizedChooser first) fuel E.initHistory history =
    E.runRandomizedFor (model.randomizedChooser second) fuel E.initHistory history
  rcases lt_trichotomy fuel history.trace.length with short | exactDepth | long
  · rw [E.runRandomizedFor_apply_eq_zero_of_length_gt _ fuel _ history
      (by simpa [ExecutionProtocol.initHistory, Trace.length] using short),
      E.runRandomizedFor_apply_eq_zero_of_length_gt _ fuel _ history
        (by simpa [ExecutionProtocol.initHistory, Trace.length] using short)]
  · rw [exactDepth]
    exact same
  · by_cases stopped : E.terminal history.state
    · obtain ⟨extra, sameFuel⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt long)
      conv_lhs =>
        rw [sameFuel, E.runRandomizedFor_apply_terminal_add _ history.trace.length extra
          _ history (by simp [ExecutionProtocol.initHistory, Trace.length]) stopped]
      conv_rhs =>
        rw [sameFuel, E.runRandomizedFor_apply_terminal_add _ history.trace.length extra
          _ history (by simp [ExecutionProtocol.initHistory, Trace.length]) stopped]
      exact same
    · rw [E.runRandomizedFor_apply_eq_zero_of_length_lt_of_not_terminal _ fuel _ history
        (by simpa [ExecutionProtocol.initHistory, Trace.length] using long) stopped,
        E.runRandomizedFor_apply_eq_zero_of_length_lt_of_not_terminal _ fuel _ history
          (by simpa [ExecutionProtocol.initHistory, Trace.length] using long) stopped]

/-- Completing behavior away from compatible information cannot change the
exact clean-prefix reach weights. In particular, a zero prescribed prefix
cannot acquire positive mass through an unrestricted completion elsewhere. -/
theorem cleanCompletion_reachWeight
    (turns : Nat) (timing : TurnTiming service.setup turns)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (continuation : ∀ who,
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).BehavioralPolicy who)
    (agrees : ∀ who info, service.sourceCompatibleInfo who info →
      continuation who info =
        (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).restrictPolicy
          (initialLaw service.setup) service.horizon service.scheduler who
            (sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing profile
              who) info) :
    ∀ {state} (trace : ((service.bounds.riskMenu (runtime service.setup) service.leaks
      service.bound).protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
        state),
      (runtime service.setup).AllPersistentServiceRiskClear service.leaks service.bound state →
      let model := (service.bounds.riskMenu (runtime service.setup) service.leaks
        service.bound).information (initialLaw service.setup) service.horizon service.scheduler
      model.historyReachWeight continuation ⟨state, trace⟩ =
        model.historyReachWeight (fun who =>
          (service.bounds.riskMenu (runtime service.setup) service.leaks
            service.bound).restrictPolicy (initialLaw service.setup) service.horizon
              service.scheduler who (sourceServiceTurnPolicy service.setup service.leaks
                service.bound turns timing profile who)) ⟨state, trace⟩
  | _, .start, _ => rfl
  | _, .extend prior joint legal realized, clear => by
      intro model
      let protocol := (service.bounds.riskMenu (runtime service.setup) service.leaks
        service.bound).protocol (initialLaw service.setup) service.horizon service.scheduler
      let baseline := fun who => (service.bounds.riskMenu (runtime service.setup) service.leaks
        service.bound).restrictPolicy (initialLaw service.setup) service.horizon service.scheduler
          who (sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing
            profile who)
      obtain ⟨priorClear, actingClear⟩ :=
        (runtime service.setup).allPersistentServiceRiskClear_before_transition service.leaks
          service.bound (initialLaw service.setup) service.horizon service.scheduler _ _ joint
            realized clear
      have earlier := cleanCompletion_reachWeight turns timing profile permitted effective
        continuation agrees prior priorClear
      change model.runBehavioral continuation (prior.length + 1)
          ⟨_, .extend prior joint legal realized⟩ =
        model.runBehavioral baseline (prior.length + 1) ⟨_, .extend prior joint legal realized⟩
      unfold InformationModel.runBehavioral InformationModel.runBehavioralFrom
      conv_lhs =>
        rw [ExecutionProtocol.runRandomizedFor_apply_of_trace_succ _ _ _ _
          (by simp [ExecutionProtocol.initHistory, Trace.length])]
      conv_rhs =>
        rw [ExecutionProtocol.runRandomizedFor_apply_of_trace_succ _ _ _ _
          (by simp [ExecutionProtocol.initHistory, Trace.length])]
      by_cases absent : model.historyReachWeight baseline ⟨_, prior⟩ = 0
      · have completedAbsent : model.historyReachWeight continuation ⟨_, prior⟩ = 0 :=
          earlier.trans absent
        change model.historyReachWeight continuation ⟨_, prior⟩ * _ =
          model.historyReachWeight baseline ⟨_, prior⟩ * _
        rw [completedAbsent, absent, zero_mul, zero_mul]
      · have supported : (History.mk _ prior) ∈
            (model.runBehavioral baseline prior.length).support :=
          (PMF.mem_support_iff _ _).mpr absent
        have one : model.runBehavioralFrom continuation 1 ⟨_, prior⟩ =
            model.runBehavioralFrom baseline 1 ⟨_, prior⟩ := by
          apply ExecutionProtocol.runRandomizedFor_one_congr_at_start
          intro running
          apply InformationModel.behavioralJoint_congr
          intro who
          by_cases active : protocol.active (History.mk _ prior).state who
          · exact agrees who _ (service.turnPolicy_sourceCompatibleInfo_of_clean_support turns
              timing profile permitted effective prior.length ⟨_, prior⟩ supported priorClear who
                active (fun control same => by
                  have atControl := active
                  rw [same] at atControl
                  exact actingClear control same who atControl))
          · exact model.behavioral_eq_of_not_active _ _ prior active
        exact congrArg₂ (fun first second : ENNReal => first * second) earlier
          (congrArg (fun law => law ⟨_, .extend prior joint legal realized⟩) one)

/-- Exact clean-prefix probabilities are preserved at every initialized
finite cutoff, including terminal absorption and late pre-response endpoints. -/
theorem cleanCompletion_probability
    (turns : Nat) (timing : TurnTiming service.setup turns)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (continuation : ∀ who,
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).BehavioralPolicy who)
    (agrees : ∀ who info, service.sourceCompatibleInfo who info →
      continuation who info =
        (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).restrictPolicy
          (initialLaw service.setup) service.horizon service.scheduler who
            (sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing profile
              who) info)
    (fuel : Nat)
    (history : ((service.bounds.riskMenu (runtime service.setup) service.leaks
      service.bound).protocol (initialLaw service.setup) service.horizon service.scheduler).History)
    (clear : (runtime service.setup).AllPersistentServiceRiskClear service.leaks service.bound
      history.state) :
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let model := menu.information (initialLaw service.setup) service.horizon service.scheduler
    let baseline := fun who => menu.restrictPolicy (initialLaw service.setup) service.horizon
      service.scheduler who (sourceServiceTurnPolicy service.setup service.leaks service.bound
        turns timing profile who)
    model.runBehavioral continuation fuel history = model.runBehavioral baseline fuel history := by
  intro menu model baseline
  apply pointMass_eq_of_reachWeight_eq model continuation baseline history _ fuel
  exact service.cleanCompletion_reachWeight turns timing profile permitted effective continuation
    agrees history.trace clear

/-- Every clean prefix event keeps its unnormalized prescribed probability;
the completion can behave arbitrarily at all other information values. -/
theorem cleanCompletion_event_probability
    (turns : Nat) (timing : TurnTiming service.setup turns)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (continuation : ∀ who,
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).BehavioralPolicy who)
    (agrees : ∀ who info, service.sourceCompatibleInfo who info →
      continuation who info =
        (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).restrictPolicy
          (initialLaw service.setup) service.horizon service.scheduler who
            (sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing profile
              who) info)
    (fuel : Nat)
    (event : Set ((service.bounds.riskMenu (runtime service.setup) service.leaks
      service.bound).protocol (initialLaw service.setup) service.horizon service.scheduler).History)
    (clear : ∀ history ∈ event,
      (runtime service.setup).AllPersistentServiceRiskClear service.leaks service.bound
        history.state) :
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let model := menu.information (initialLaw service.setup) service.horizon service.scheduler
    let baseline := fun who => menu.restrictPolicy (initialLaw service.setup) service.horizon
      service.scheduler who (sourceServiceTurnPolicy service.setup service.leaks service.bound
        turns timing profile who)
    (model.runBehavioral continuation fuel).toOuterMeasure event =
      (model.runBehavioral baseline fuel).toOuterMeasure event := by
  classical
  intro menu model baseline
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro history
  by_cases present : history ∈ event
  · rw [Set.indicator_of_mem present, Set.indicator_of_mem present]
    exact service.cleanCompletion_probability turns timing profile permitted effective continuation
      agrees fuel history (clear history present)
  · simp only [Set.indicator, ite_eq_right present]

/-- A compatible-site completion has the actual physical prescribed law on
all clean raw-prefix events, with complete traffic and private recall retained. -/
theorem cleanCompletion_physical_event_probability
    (turns : Nat) (timing : TurnTiming service.setup turns)
    (profile : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (continuation : ∀ who,
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).BehavioralPolicy who)
    (agrees : ∀ who info, service.sourceCompatibleInfo who info →
      continuation who info =
        (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).restrictPolicy
          (initialLaw service.setup) service.horizon service.scheduler who
            (sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing profile
              who) info)
    (fuel : Nat)
    (event : Set ((application service.setup service.leaks).protocol (initialLaw service.setup)
      service.horizon service.scheduler).History)
    (clear : ∀ history ∈ event,
      (runtime service.setup).AllPersistentServiceRiskClear service.leaks service.bound
        history.state) :
    let menu := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
    let players := sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing
      profile
    (((menu.information (initialLaw service.setup) service.horizon service.scheduler).runBehavioral
      continuation fuel).map
        (menu.toRawHistory (initialLaw service.setup) service.horizon
          service.scheduler)).toOuterMeasure event =
      (((application service.setup service.leaks).information (initialLaw service.setup)
        service.horizon service.scheduler).runBehavioral
          (fun who => (application service.setup service.leaks).encodePolicy (players who))
            fuel).toOuterMeasure event := by
  intro menu players
  have completed := service.cleanCompletion_event_probability turns timing profile permitted
    effective continuation agrees fuel
      ((menu.toRawHistory (initialLaw service.setup) service.horizon service.scheduler) ⁻¹' event)
      (fun history present => clear _ present)
  have actual := sourceServiceTurnPolicy_cleanPrefix_event_probability service.bounds service.values
    service.initialValues service.capacity service.bound turns timing profile permitted
      service.horizon service.scheduler fuel event clear
  dsimp only at actual
  rw [PMF.toOuterMeasure_map_apply] at actual ⊢
  exact completed.trans actual

end Vegas.AsyncServiceSpec
