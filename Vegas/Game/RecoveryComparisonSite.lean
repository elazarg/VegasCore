/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryComparisonInformation
import Vegas.Game.RecoveryNativeDebt

/-! # Complete comparison information fibers at clear recovery decisions -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

private theorem belief_repackage {Player : Type} {T : ExecutionProtocol Player}
    (M : InformationModel T) (assessment : M.BehavioralAssessment) (who : Player)
    (first second : M.InformationSite who) (same : first.1 = second.1) :
    (assessment.belief who first).map
      (fun history => (⟨history.1, history.2.trans same⟩ :
        M.InformationHistory who second.1)) = assessment.belief who second := by
  have equal : first = second := Subtype.ext same
  subst second
  exact PMF.map_id _

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks

private theorem exists_clearReference [Fintype (RP).History]
    [∀ player, DecidableEq ((R).InfoState player)]
    {who : Player} (site : (R).InformationSite who)
    (forced : ForcedAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site)) :
    ∃ reference : (application setup leaks).Control,
      reference.actor = some who ∧
      ExclusionEvidence 0 ∅ (RecoveryState.mk reference.execution.application ∅) ∧
      site.1 = liftInformation (runtime setup) leaks
        ((application setup leaks).observe who (some reference)) := by
  obtain ⟨history, _running, _choice, _legal⟩ := site.2
  have active := InformationSite.active (R) site history
  obtain ⟨current, state, actor⟩ := (recoveryApplication (runtime setup) leaks).control_of_active
    Initial horizon scheduler ((RMenu).toRawHistory Initial horizon scheduler history.1) who active
  change history.1.state = some current at state
  have observed := ((RMenu).info Initial horizon scheduler who history.1.trace).symm.trans history.2
  rw [state] at observed
  let reference := RecoveryProjection.control (runtime setup) leaks current
  have referenceActor : reference.actor = some who := actor
  have projection := observe_projection (runtime setup) leaks who (some current)
  change (application setup leaks).observe who (some reference) =
    RecoveryProjection.information (runtime setup) leaks
      ((recoveryApplication (runtime setup) leaks).observe who (some current)) at projection
  rw [observed] at projection
  have atSite : site.1 = liftInformation (runtime setup) leaks
      ((application setup leaks).observe who (some reference)) := by
    rw [projection]
    exact forced.1.symm
  have clear := informationFiber_clear (runtime setup) leaks who reference referenceActor
    history.1.state (((RMenu).info Initial horizon scheduler who history.1.trace).symm.trans
      (history.2.trans atSite))
  have nativeState : protocolState (runtime setup) leaks history.1.state = some reference := by
    rw [state]
    rfl
  have valid := nativeHistory_record (runtime setup) leaks Initial (initialLaw_initialized setup)
    horizon scheduler ((RMenu).toRawTrace Initial horizon scheduler history.1.trace) clear
      reference nativeState
  exact ⟨reference, referenceActor, valid, atSite⟩

open Classical in
/-- Any actual clear forced, debt-free recovery decision has a complete finite
native information-fiber projection with exactly the common comparison belief.
This construction includes late inputs and histories of zero belief mass. -/
theorem exists_comparisonInformationHistory [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ player, DecidableEq ((R).InfoState player)]
    [∀ player, DecidableEq ((N).InfoState player)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p))
    (assessments : ℕ → (R).BehavioralAssessment)
    (fallback : ℕ → ∀ player, (R).Policy player)
    (assembled : ∀ n, (assessments n).strategy = (R).agentBehavior (R).playedInformation
      (fallback n)
      (fun agent => (weights n (pool setup leaks bounds Initial horizon scheduler agent)).bind
        (component setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (R) (assessments n)
      ((RMenu).decisionInformationAntichain Initial horizon scheduler))
    (n : ℕ) (who : Player) (site : (R).InformationSite who)
    (notFree : ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site))
    (notOwing : ¬ OwingAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site)) :
    ∃ (nativeSite : (N).InformationSite who)
      (project : (R).InformationHistory who site.1 → (N).InformationHistory who nativeSite.1),
      nativeSite.1 = RecoveryProjection.information (runtime setup) leaks site.1 ∧
      ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt nativeSite) ∧
      ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt nativeSite) ∧
      (∀ history : (R).InformationHistory who site.1, ∃ clear :
          ∀ current, history.1.state = some current →
            current.execution.application.excluded = ∅,
        (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler) (project history).1 =
          Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
            ((application setup leaks).protocol initial horizon (NativeScheduler)).History)
              (initialLaw_native setup))
            (nativeHistory (runtime setup) leaks Initial horizon scheduler
              ((RMenu).toRawHistory Initial horizon scheduler history.1) clear)) ∧
      (∀ history, (project history).1.state =
        protocolState (runtime setup) leaks history.1.state) ∧
      ((assessments n).belief who site).map project =
        (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
          le_one weights n).belief who nativeSite := by
  have forced : ForcedAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) :=
    Classical.not_not.mp notFree
  obtain ⟨genericSite, seen, _forcedIff⟩ := exists_nativeInformationSite_of_clear setup leaks bounds
    Initial (initialLaw_initialized setup) horizon scheduler site forced.1
  have genericDecision :
      ((NMenu).information ((Initial).map RecoveryState.native) horizon
        (NativeScheduler)).IsDecisionInfo who
          (RecoveryProjection.information (runtime setup) leaks site.1) :=
    seen ▸ genericSite.2
  have nativeDecision : (N).IsDecisionInfo who
      (RecoveryProjection.information (runtime setup) leaks site.1) :=
    Eq.mp (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
      ((NMenu).information initial horizon (NativeScheduler)).IsDecisionInfo who
        (RecoveryProjection.information (runtime setup) leaks site.1))
          (initialLaw_native setup)) genericDecision
  let nativeSite : (N).InformationSite who :=
    ⟨RecoveryProjection.information (runtime setup) leaks site.1, nativeDecision⟩
  have nativeInput : nativeSite.1 = RecoveryProjection.information (runtime setup) leaks site.1 :=
    rfl
  have lifted : liftInformation (runtime setup) leaks nativeSite.1 = site.1 := forced.1
  have recoveryDecision : (R).IsDecisionInfo who
      (liftInformation (runtime setup) leaks nativeSite.1) := lifted.symm ▸ site.2
  have sites :
      (⟨liftInformation (runtime setup) leaks nativeSite.1, recoveryDecision⟩ :
        (R).InformationSite who) = site := Subtype.ext lifted
  have nativeNotFree : ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler)
      ((N).agentAt nativeSite) := by
    intro free
    apply notFree
    have recovered := freeAgent_of_nativeFree setup leaks bounds horizon scheduler
      ((N).agentAt nativeSite) free recoveryDecision
    exact Eq.mp (congrArg (fun current : (R).InformationSite who =>
      FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt current)) sites) recovered
  have nativeNotOwing : ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler)
      ((N).agentAt nativeSite) := by
    intro owing
    apply notOwing
    have recovered := owingAgent_of_nativeOwing_at_liftedSite setup leaks bounds horizon scheduler
      nativeSite recoveryDecision owing
    exact Eq.mp (congrArg (fun current : (R).InformationSite who =>
      OwingAgent setup leaks bounds Initial horizon scheduler ((R).agentAt current)) sites)
        recovered
  obtain ⟨reference, active, valid, seen⟩ := exists_clearReference setup leaks bounds horizon
    scheduler site (Classical.not_not.mp notFree)
  have nativeSeen : nativeSite.1 = (application setup leaks).observe who (some reference) :=
    nativeInput.trans ((congrArg (RecoveryProjection.information (runtime setup) leaks) seen).trans
      (information_liftInformation (runtime setup) leaks _))
  let nativeDecision : (N).IsDecisionInfo who
      ((application setup leaks).observe who (some reference)) := nativeSeen ▸ nativeSite.2
  let recoveryDecision : (R).IsDecisionInfo who (liftInformation (runtime setup) leaks
      ((application setup leaks).observe who (some reference))) := seen ▸ site.2
  let normalizedNative : (N).InformationSite who :=
    ⟨(application setup leaks).observe who (some reference), nativeDecision⟩
  let normalizedRecovery : (R).InformationSite who :=
    ⟨liftInformation (runtime setup) leaks
      ((application setup leaks).observe who (some reference)), recoveryDecision⟩
  let repackage : (R).InformationHistory who site.1 →
      (R).InformationHistory who normalizedRecovery.1 := fun history =>
    ⟨history.1, history.2.trans seen⟩
  let unpackage : (N).InformationHistory who normalizedNative.1 →
      (N).InformationHistory who nativeSite.1 := fun history =>
    ⟨history.1, history.2.trans nativeSeen.symm⟩
  let middle := comparisonInformationHistory setup leaks bounds horizon scheduler who reference
    active valid nativeDecision recoveryDecision
  let project := unpackage ∘ middle ∘ repackage
  have states (history : (R).InformationHistory who site.1) :
      (project history).1.state = protocolState (runtime setup) leaks history.1.state :=
    comparisonInformationHistory_state setup leaks bounds horizon scheduler who reference active
      valid nativeDecision recoveryDecision (repackage history)
  have rawProjection (history : (R).InformationHistory who site.1) :
      ∃ clear : ∀ current, history.1.state = some current →
          current.execution.application.excluded = ∅,
        (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler) (project history).1 =
          Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
            ((application setup leaks).protocol initial horizon (NativeScheduler)).History)
              (initialLaw_native setup))
            (nativeHistory (runtime setup) leaks Initial horizon scheduler
              ((RMenu).toRawHistory Initial horizon scheduler history.1) clear) := by
    have observed := ((RMenu).info Initial horizon scheduler who history.1.trace).symm.trans
      (history.2.trans seen)
    have clear := informationFiber_clear (runtime setup) leaks who reference active history.1.state
      observed
    refine ⟨clear, ?_⟩
    exact comparisonInformationHistory_raw setup leaks bounds horizon scheduler who reference
      active valid nativeDecision recoveryDecision (repackage history)
  have law : ((assessments n).belief who site).map project =
      (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
        le_one weights n).belief who nativeSite := by
    have first := belief_repackage (R) (assessments n) who site normalizedRecovery seen
    have last := belief_repackage (N) (nativeComparisonSequence setup leaks bounds horizon scheduler
      sequence scale positive le_one weights n) who normalizedNative nativeSite nativeSeen.symm
    have main := recovery_belief_eq_comparisonInformationHistory setup leaks bounds horizon
      scheduler who reference active valid nativeDecision recoveryDecision sequence scale positive
        le_one weights n (fallback n) (assessments n) (assembled n) (bayes n)
    calc
      _ = ((((assessments n).belief who site).map repackage).map middle).map unpackage := by
        rw [PMF.map_comp, PMF.map_comp]
        rfl
      _ = _ := by rw [first, main, last]
  exact ⟨nativeSite, project, nativeInput, nativeNotFree, nativeNotOwing, rawProjection,
    states, law⟩

end Vegas.RecoveryOnePacket
