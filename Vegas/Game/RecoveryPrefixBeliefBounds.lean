/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryNativePrefixSites
import Vegas.Game.RecoveryNativePrefixBounds
import Vegas.Game.RecoveryComparisonInformation

/-! # Posterior prefix estimates at actual recovery decisions

The existing native prefix certificate applies with the unchanged recovery
completion weights. Exact complete-history belief transport then gives actual
recovery unforced-mass and record/decode decorrelation bounds.
-/

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
      PublicExclusionRecord (RecoveryState.mk reference.execution.application ∅) ∧
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
/-- Actual forced, debt-free nonlate recovery decisions inherit the original
uniform prefix estimates, with a genuine finite history projection of their
entire posterior fiber. -/
theorem recovery_prefix_bounds [Fintype (RP).History]
    [(recoveryApplication (runtime setup) leaks).FiniteNature Initial scheduler]
    [Finite setup.intendedProtocol.History]
    [∀ player, DecidableEq ((R).InfoState player)]
    [∀ player, DecidableEq ((N).InfoState player)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependent)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slots_pos : 0 < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p))
    (assessments : ℕ → (R).BehavioralAssessment)
    (fallback : ℕ → ∀ player, (R).Policy player)
    (assembled : ∀ n, (assessments n).strategy = (R).agentBehavior (R).playedInformation
      (fallback n)
      (fun agent => (weights n (pool setup leaks bounds Initial horizon scheduler agent)).bind
        (component setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (R) (assessments n)
      ((RMenu).decisionInformationAntichain Initial horizon scheduler)) :
    ∃ drift error : ℕ → ℝ,
      Tendsto drift atTop (nhds 0) ∧ Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (R).InformationSite who),
        ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ¬ OwingAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ¬ ownedKeyed (FreeAgent setup leaks bounds Initial horizon scheduler)
          (KeyedAgent setup leaks bounds Initial horizon scheduler) ((R).agentAt site) →
        ∀ {past : List (recoveryApplication (runtime setup) leaks).PlayerEntry}
          {view : (recoveryApplication (runtime setup) leaks).PlayerView},
        site.1 = some (past, view) →
        ∀ {event : (graph setup).EventId},
        view.application.1.publicView.ownTurn? who = some event →
        (∀ entry ∈ past, (runtime setup).submittedEvent? leaks
          (RecoveryProjection.action (runtime setup) leaks entry.action) ≠ some event) →
        ∃ (nativeSite : (N).InformationSite who)
          (project : (R).InformationHistory who site.1 →
            (N).InformationHistory who nativeSite.1),
          nativeSite.1 = RecoveryProjection.information (runtime setup) leaks site.1 ∧
          (∀ history : (R).InformationHistory who site.1, ∃ clear :
              ∀ current, history.1.state = some current →
                current.execution.application.excluded = ∅,
            (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler) (project history).1 =
              Equiv.cast (congrArg (fun initial :
                PMF (EventGraphRuntime.State (graph setup)) =>
                  ((application setup leaks).protocol initial horizon (NativeScheduler)).History)
                    (initialLaw_native setup))
                (nativeHistory (runtime setup) leaks Initial horizon scheduler
                  ((RMenu).toRawHistory Initial horizon scheduler history.1) clear)) ∧
          (∀ history, (project history).1.state =
            protocolState (runtime setup) leaks history.1.state) ∧
          ((assessments n).belief who site).map project =
            (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
              le_one weights n).belief who nativeSite ∧
          expect ((assessments n).belief who site) (fun history =>
            if Vegas.ForcedState setup leaks who
              (protocolState (runtime setup) leaks history.1.state) then (0 : ℝ) else 1) ≤
                drift n ∧
          BeliefDecorrelated ((assessments n).belief who site)
            (fun history => operationalRecord setup leaks bounds horizon (NativeScheduler)
              (project history).1.trace)
            (fun history => Vegas.nativeDecodedState setup leaks
              (protocolState (runtime setup) leaks history.1.state)) (error n) := by
  obtain ⟨drift, error, driftLimit, errorLimit, estimates⟩ :=
    nativeComparison_prefix_bounds setup leaks bounds horizon scheduler wellFormed independent
      sequence sourceMixed scale positive le_one scaleEq covers coversInputs capacity slots_pos
        weights
  refine ⟨drift, error, driftLimit, errorLimit, ?_⟩
  intro n who site notFree notOwing notKeyed past view atSite event turn unsent
  have nonlate : ¬ KeyedAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) :=
    fun keyed => notKeyed ⟨keyed, notFree⟩
  obtain ⟨nativeSite, nativeInput, _lifted, nativeNotFree, nativeNotOwing, nativeNotKeyed⟩ :=
    exists_nativePrefixSite setup leaks bounds horizon scheduler site notFree notOwing nonlate
  have pending : pendingEvent setup leaks who nativeSite.1 ≠ none := by
    rw [nativeInput, atSite, pendingEvent_of_recoveryRecall setup leaks turn unsent]
    exact Option.some_ne_none _
  obtain ⟨unforced, decorrelated⟩ :=
    estimates n who nativeSite nativeNotFree nativeNotOwing nativeNotKeyed pending
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
  refine ⟨nativeSite, project, nativeInput, rawProjection, states, law, ?_, ?_⟩
  · rw [← law, expect_map] at unforced
    simpa only [Function.comp_def, states] using unforced
  · intro first second firstBounded secondBounded
    have bound := decorrelated first second firstBounded secondBounded
    rw [← law, expect_map, expect_map, expect_map] at bound
    simpa only [Function.comp_def, states] using bound

end Vegas.RecoveryOnePacket
