/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNativeStrategy

/-! # Actual recovery decisions over clear native prefixes

Every active publicly clear native prefix has an actual finite recovery
decision at the lifted complete input. No reach or policy support is required.
-/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler runtime leaks scheduler
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  (NativeScheduler)
local notation "RMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NMenu" => bounds.onePacketMenu runtime leaks

/-- Every active clear native trace has a genuine recovery decision at the
lift of its full information input. -/
theorem recoveryDecision_of_nativeClearTrace
    {before : (application setup runtime leaks).ProtocolState}
    (prior : ((NMenu).protocol (initialLaw setup) horizon (NativeScheduler)).Trace before)
    (valid : ∀ current, before = some current →
      ExclusionEvidence 0 ∅ (RecoveryState.mk current.execution.application ∅))
    (who : Player) (active : (application setup runtime leaks).actor before = some who)
    (running : ¬ (application setup runtime leaks).terminal before) :
    (R).IsDecisionInfo who (liftInformation runtime leaks ((N).infoOf who prior)) := by
  let genericPrior : ((NMenu).protocol ((Initial).map RecoveryState.native) horizon
      (NativeScheduler)).Trace before :=
    Eq.mpr (congrArg (fun law : PMF (EventGraphRuntime.State (graph setup)) =>
      ((NMenu).protocol law horizon (NativeScheduler)).Trace before)
      (initialLaw_native setup)) prior
  obtain ⟨history, same⟩ := exists_recoveryBoundedHistory runtime leaks bounds Initial
    (initialLaw_initialized setup) horizon scheduler ⟨before, genericPrior⟩ valid
  have states := congrArg ExecutionProtocol.History.state same
  change history.state = liftProtocolState runtime leaks before at states
  have recoveryActive : ((RMenu).protocol Initial horizon scheduler).active history.state who := by
    change (recoveryApplication runtime leaks).actor history.state = some who
    rw [states, actor_liftProtocolState]
    exact active
  have recoveryRunning : ¬ ((RMenu).protocol Initial horizon scheduler).terminal
      history.state := by
    change ¬ (recoveryApplication runtime leaks).terminal history.state
    rw [states]
    exact fun ended => running ((terminal_liftProtocolState runtime leaks before).mp ended)
  have observed : (R).infoOf who history.trace =
      liftInformation runtime leaks ((N).infoOf who prior) := by
    exact ((RMenu).info Initial horizon scheduler who history.trace).trans
      ((congrArg ((recoveryApplication runtime leaks).observe who) states).trans
        ((observe_lift runtime leaks who before).trans
          (congrArg (liftInformation runtime leaks)
            ((NMenu).info (initialLaw setup) horizon (NativeScheduler) who prior).symm)))
  obtain ⟨site, seen⟩ := (R).exists_informationSite_of_active who history recoveryRunning
    recoveryActive
  exact (seen.trans observed) ▸ site.2

omit [Fintype Player] in
private theorem native_initialLaw_initialized (native : EventGraphRuntime.State (graph setup))
    (supported : native ∈ (initialLaw setup).support) :
    ∃ inputs, native = State.initial inputs := by
  change native ∈ (setup.initialLaw.map
    (fun draw => State.initial (graph := graph setup) (setup.eventInputs draw))).support
    at supported
  obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact ⟨setup.eventInputs draw, rfl⟩

/-- The two native behavioral step coefficients agree on every actual clear
prefix of the original bounded source game. -/
theorem nativeComparison_stepProb_of_clear [Fintype ((RMenu).protocol Initial horizon
      scheduler).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
    (n : ℕ) (fallback : ∀ who, (R).Policy who)
    (strategy : ∀ who, (R).BehavioralPolicy who)
    (assembled : strategy = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights n (pool setup runtime leaks bounds Initial horizon scheduler
        agent)).bind
        (component setup runtime leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    {before : (application setup runtime leaks).ProtocolState}
    (prior : ((NMenu).protocol (initialLaw setup) horizon (NativeScheduler)).Trace before)
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : ((NMenu).protocol (initialLaw setup) horizon (NativeScheduler)).Legal before joint)
    (valid : ∀ current, before = some current →
      ExclusionEvidence 0 ∅ (RecoveryState.mk current.execution.application ∅))
    (target : (application setup runtime leaks).ProtocolState) :
    (N).stepProb (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence
      scale
      positive le_one weights n) prior ⟨joint, legal⟩ target =
      (N).stepProb (sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy) prior
        ⟨joint, legal⟩ target := by
  rw [InformationModel.stepProb, InformationModel.stepProb,
    InformationModel.behavioralJoint_prob_eq_prod,
    InformationModel.behavioralJoint_prob_eq_prod]
  apply congrArg (fun weight : ℝ => weight * _)
  apply Finset.prod_congr rfl
  intro who _member
  have same : nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale
      positive le_one weights n who ((N).infoOf who prior) =
      sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy who ((N).infoOf who
        prior) := by
    by_cases active : ((NMenu).protocol (initialLaw setup) horizon (NativeScheduler)).active
        before who
    · obtain ⟨site, seen⟩ := (N).exists_informationSite_of_active who ⟨before, prior⟩ legal.1
        active
      have recoveryDecision := recoveryDecision_of_nativeClearTrace setup runtime leaks bounds
        horizon
        scheduler prior valid who active legal.1
      have represented : (R).IsDecisionInfo who (liftInformation runtime leaks site.1) :=
        Eq.mpr (congrArg (fun input => (R).IsDecisionInfo who
          (liftInformation runtime leaks input)) seen) recoveryDecision
      have localLaw : nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence
          scale positive le_one weights n who site.1 =
          sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy who site.1 := by
        apply pmf_map_injective Subtype.val_injective
        rw [sourceNativeProfile_map_val]
        exact nativeComparisonStrategy_at_clear setup runtime leaks bounds horizon scheduler
          sequence scale
          positive le_one weights n fallback strategy assembled site represented
      exact Eq.mp (congrArg (fun input => nativeComparisonStrategy setup runtime leaks bounds
        horizon
        scheduler sequence scale positive le_one weights n who input =
          sourceNativeProfile setup runtime leaks bounds horizon scheduler strategy who input) seen)
            localLaw
    · exact (N).behavioral_eq_of_not_active _ _ prior active
  exact congrArg (fun law => (law ((N).choicesOfLegal prior ⟨joint, legal⟩ who)).toReal) same

/-- The same recovery completion weights give exactly the canonical projected
reach weight on every complete publicly clear native history. -/
theorem historyReachWeight_nativeComparison_of_clear [Fintype ((RMenu).protocol Initial horizon
      scheduler).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
    (n : ℕ) (fallback : ∀ who, (R).Policy who)
    (strategy : ∀ who, (R).BehavioralPolicy who)
    (assembled : strategy = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights n (pool setup runtime leaks bounds Initial horizon scheduler
        agent)).bind
        (component setup runtime leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent))) :
    ∀ {state} (trace : ((NMenu).protocol (initialLaw setup) horizon (NativeScheduler)).Trace state)
      (_valid : ∀ current, state = some current →
        ExclusionEvidence 0 ∅ (RecoveryState.mk current.execution.application ∅)),
      (N).historyReachWeight (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler
        sequence scale positive le_one weights n) ⟨state, trace⟩ =
        (N).historyReachWeight (sourceNativeProfile setup runtime leaks bounds horizon scheduler
          strategy)
          ⟨state, trace⟩ := by
  intro state trace
  have realEquality :
      ∀ (clear : ∀ current, state = some current →
          ExclusionEvidence 0 ∅ (RecoveryState.mk current.execution.application ∅)),
        ((N).historyReachWeight (nativeComparisonStrategy setup runtime leaks bounds horizon
          scheduler
          sequence scale positive le_one weights n) ⟨state, trace⟩).toReal =
          ((N).historyReachWeight (sourceNativeProfile setup runtime leaks bounds horizon scheduler
            strategy) ⟨state, trace⟩).toReal := by
    induction trace with
    | start =>
      intro _clear
      exact congrArg ENNReal.toReal
        (((N).historyReachWeight_initHistory (nativeComparisonStrategy setup runtime leaks bounds
          horizon
          scheduler sequence scale positive le_one weights n)).trans
            ((N).historyReachWeight_initHistory (sourceNativeProfile setup runtime leaks bounds
              horizon
              scheduler strategy)).symm)
    | @extend before after prior joint legal realized ih =>
      intro clear
      have valid := native_clear_before_transition runtime leaks (initialLaw setup)
        (native_initialLaw_initialized setup) horizon (NativeScheduler)
        ((NMenu).toRawTrace (initialLaw setup) horizon (NativeScheduler) prior) joint realized clear
      rw [InformationModel.historyReachProbability_extend,
        InformationModel.historyReachProbability_extend,
        nativeComparison_stepProb_of_clear setup runtime leaks bounds horizon scheduler sequence
          scale
          positive le_one weights n fallback strategy assembled prior joint legal valid after,
        ih valid]
  intro valid
  exact (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    (realEquality valid)

end Vegas.RecoveryOnePacket
