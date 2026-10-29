/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ConditionedInitialFiber
import Vegas.Source.ConditionedInitialPolicy
import GameTheory.Analysis.Protocol.CounterfactualReach

/-! # Behavioral source reach under initial-law conditioning -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability
open scoped ENNReal

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  {Signal : Type*} (signal : State L setup.context → Signal) (value : Signal)
  (supported : value ∈ (setup.initialLaw.map signal).support)

/-- Conditioning the initializer retains the probability of every legal local
joint action after transporting the actual source policies. -/
theorem conditionInitial_behavioralJoint_probability
    (policies : ∀ who, setup.intendedModel.BehavioralPolicy who)
    {state : setup.ProtocolState}
    (trace : (setup.conditionInitial signal value).intendedProtocol.Trace state)
    (joint : Player → Option (OwnAction Player L))
    (legal : (setup.conditionInitial signal value).intendedProtocol.Legal state joint) :
    ((setup.intendedModel.behavioralJoint policies
        (setup.conditionInitial_trace signal value supported trace) legal.1)
          ⟨joint, legal⟩).toReal =
      (((setup.conditionInitial signal value).intendedModel.behavioralJoint
        (fun who => setup.conditionInitial_policy signal value who (policies who)) trace
          legal.1) ⟨joint, legal⟩).toReal := by
  rw [InformationModel.behavioralJoint_prob_eq_prod,
    InformationModel.behavioralJoint_prob_eq_prod]
  apply Finset.prod_congr rfl
  intro who _
  have observed := setup.conditionInitial_history_observed signal value supported
    ⟨state, trace⟩ who
  change setup.intendedModel.infoOf who
      (setup.conditionInitial_trace signal value supported trace) =
    (setup.conditionInitial signal value).intendedModel.infoOf who trace at observed
  let first := setup.intendedModel.choicesOfLegal
    (setup.conditionInitial_trace signal value supported trace) ⟨joint, legal⟩ who
  let second := (setup.conditionInitial signal value).intendedModel.choicesOfLegal trace
    ⟨joint, legal⟩ who
  have firstMass := pmf_map_apply_of_injective
    (policies who (setup.intendedModel.infoOf who
      (setup.conditionInitial_trace signal value supported trace))) Subtype.val_injective first
  have secondMass := pmf_map_apply_of_injective
    (setup.conditionInitial_policy signal value who (policies who)
      ((setup.conditionInitial signal value).intendedModel.infoOf who trace))
      Subtype.val_injective second
  calc
    _ = (((policies who (setup.intendedModel.infoOf who
          (setup.conditionInitial_trace signal value supported trace))).map Subtype.val)
        (joint who)).toReal := congrArg ENNReal.toReal firstMass.symm
    _ = (((setup.conditionInitial_policy signal value who (policies who)
          ((setup.conditionInitial signal value).intendedModel.infoOf who trace)).map
            Subtype.val) (joint who)).toReal := by
      rw [setup.conditionInitial_policy_map_val]
      exact congrArg (fun view : setup.ProtocolView who =>
        (((policies who view).map Subtype.val) (joint who)).toReal) observed
    _ = _ := congrArg ENNReal.toReal secondMass

omit [Fintype Player] in
private theorem initialEntry_injective :
    Function.Injective (fun initial : State L setup.context =>
      some (ProtocolState.entry setup.program (Config.initial initial))) := by
  intro first second same
  have bases := congrArg (fun point => point.map (ProtocolState.base setup.program)) same
  simpa only [Option.map_some, ProtocolState.base_entry, Option.some.injEq, Config.initial]
    using bases

omit [Fintype Player] in
/-- The actual initialization kernel has the same proportional atom law as
the conditional initial state, before any strategic action is taken. -/
theorem conditionInitial_protocolStep_initial_scale
    (supported : value ∈ (setup.initialLaw.map signal).support)
    (initial : State L setup.context) (same : signal initial = value)
    (joint : Player → Option (OwnAction Player L)) :
    (setup.initialLaw.map signal) value *
        (setup.conditionInitial signal value).protocolStep none joint
          (some (ProtocolState.entry setup.program (Config.initial initial))) =
      setup.protocolStep none joint
        (some (ProtocolState.entry setup.program (Config.initial initial))) := by
  change (setup.initialLaw.map signal) value *
    ((fiberPosterior setup.initialLaw signal value).map
      (fun initial => some (ProtocolState.entry setup.program (Config.initial initial))))
        (some (ProtocolState.entry setup.program (Config.initial initial))) = _
  rw [pmf_map_apply_of_injective _ (initialEntry_injective setup),
    show setup.protocolStep none joint = setup.initialLaw.map
      (fun initial => some (ProtocolState.entry setup.program (Config.initial initial)))
        from rfl,
    pmf_map_apply_of_injective _ (initialEntry_injective setup)]
  exact setup.conditionInitial_initialLaw_scale signal value supported initial same

/-- All post-initial joint/transition coefficients agree after transporting
the source policies and the actual source trace. -/
theorem conditionInitial_stepProb_some
    (policies : ∀ who, setup.intendedModel.BehavioralPolicy who)
    {before : SourceProgram.ProtocolState setup.program}
    (trace : (setup.conditionInitial signal value).intendedProtocol.Trace (some before))
    (joint : Player → Option (OwnAction Player L))
    (legal : (setup.conditionInitial signal value).intendedProtocol.Legal (some before) joint)
    (after : setup.ProtocolState) :
    InformationModel.stepProb setup.intendedModel policies
        (setup.conditionInitial_trace signal value supported trace) ⟨joint, legal⟩ after =
      InformationModel.stepProb (setup.conditionInitial signal value).intendedModel
        (fun who => setup.conditionInitial_policy signal value who (policies who)) trace
          ⟨joint, legal⟩ after := by
  unfold InformationModel.stepProb
  rw [setup.conditionInitial_behavioralJoint_probability signal value supported policies
    trace joint legal]
  rfl

/-- The first coefficient has the sole prior factor. The coefficient's joint
action probability is unchanged; its chance mass is scaled by the signal mass. -/
theorem conditionInitial_stepProb_initial
    (policies : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (trace : (setup.conditionInitial signal value).intendedProtocol.Trace none)
    (joint : Player → Option (OwnAction Player L))
    (legal : (setup.conditionInitial signal value).intendedProtocol.Legal none joint)
    {after : setup.ProtocolState}
    (realized : after ∈
      ((setup.conditionInitial signal value).intendedProtocol.step none ⟨joint, legal⟩).support) :
    InformationModel.stepProb setup.intendedModel policies
        (setup.conditionInitial_trace signal value supported trace) ⟨joint, legal⟩ after =
      ((setup.initialLaw.map signal) value).toReal *
        InformationModel.stepProb (setup.conditionInitial signal value).intendedModel
          (fun who => setup.conditionInitial_policy signal value who (policies who)) trace
            ⟨joint, legal⟩ after := by
  change after ∈ ((fiberPosterior setup.initialLaw signal value).map
    (fun initial => some (ProtocolState.entry setup.program (Config.initial initial)))).support
      at realized
  obtain ⟨initial, present, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
  have same := (mem_support_fiberPosterior supported present).1
  have kernel := congrArg ENNReal.toReal
    (setup.conditionInitial_protocolStep_initial_scale signal value supported initial same joint)
  rw [ENNReal.toReal_mul] at kernel
  unfold InformationModel.stepProb
  rw [setup.conditionInitial_behavioralJoint_probability signal value supported policies
    trace joint legal]
  change _ * (setup.protocolStep none joint _).toReal =
    ((setup.initialLaw.map signal) value).toReal *
      (_ * ((setup.conditionInitial signal value).protocolStep none joint _).toReal)
  rw [← kernel]
  ring

private theorem intended_historyReachWeight_root
    (setup : Setup (Player := Player) (L := L))
    (policies : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    (setup.intendedModel.historyReachWeight policies ⟨none, .start⟩).toReal = 1 := by
  change ((PMF.pure setup.intendedProtocol.initHistory)
    setup.intendedProtocol.initHistory).toReal = 1
  simp

/-- Every genuine nonempty intended source history changes reach by exactly
the initial signal mass. The empty unsampled root is deliberately excluded. -/
theorem conditionInitial_historyReachWeight_toReal
    (setup : Setup (Player := Player) (L := L)) {Signal : Type*}
    (signal : State L setup.context → Signal) (value : Signal)
    (supported : value ∈ (setup.initialLaw.map signal).support)
    (policies : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    ∀ {state : setup.ProtocolState}
      (trace : (setup.conditionInitial signal value).intendedProtocol.Trace state),
      0 < trace.length →
      (setup.intendedModel.historyReachWeight policies
        ⟨state, setup.conditionInitial_trace signal value supported trace⟩).toReal =
        ((setup.initialLaw.map signal) value).toReal *
          ((setup.conditionInitial signal value).intendedModel.historyReachWeight
            (fun who => setup.conditionInitial_policy signal value who (policies who))
            ⟨state, trace⟩).toReal
  | _, .start, positive => by cases positive
  | _, .extend (source := none) prior joint legal realized, _ => by
      have root := (setup.conditionInitial signal value).intended_trace_none prior
      subst prior
      simp only [conditionInitial_trace]
      rw [InformationModel.historyReachProbability_extend,
        InformationModel.historyReachProbability_extend]
      have coefficient := setup.conditionInitial_stepProb_initial signal value supported policies
        .start joint legal realized
      simp only [conditionInitial_trace] at coefficient
      rw [coefficient]
      rw [intended_historyReachWeight_root,
        intended_historyReachWeight_root]
      ring
  | _, .extend (source := some before) prior joint legal realized, _ => by
      have positive := intended_trace_positive (setup.conditionInitial signal value) prior
        (by simp)
      have scaled := setup.conditionInitial_historyReachWeight_toReal signal value supported
        policies prior positive
      simp only [conditionInitial_trace]
      rw [InformationModel.historyReachProbability_extend,
        InformationModel.historyReachProbability_extend,
        setup.conditionInitial_stepProb_some signal value supported policies prior joint legal]
      rw [scaled]
      ring

/-- Unnormalized reach scales by the initial signal mass on every nonempty
actual intended history, for every transported source behavioral profile. -/
theorem conditionInitial_historyReachWeight_scale
    (policies : ∀ who, setup.intendedModel.BehavioralPolicy who)
    {state : setup.ProtocolState}
    (trace : (setup.conditionInitial signal value).intendedProtocol.Trace state)
    (positive : 0 < trace.length) :
    setup.intendedModel.historyReachWeight policies
        ⟨state, setup.conditionInitial_trace signal value supported trace⟩ =
      (setup.initialLaw.map signal) value *
        (setup.conditionInitial signal value).intendedModel.historyReachWeight
          (fun who => setup.conditionInitial_policy signal value who (policies who))
          ⟨state, trace⟩ := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))).mp
  rw [ENNReal.toReal_mul]
  exact setup.conditionInitial_historyReachWeight_toReal signal value supported policies trace
    positive

end Vegas.SourceProgram.Setup
