/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryNativePrefixSites
import Vegas.Game.RecoveryNativePrefixBounds
import Vegas.Game.RecoveryComparisonSite

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
  obtain ⟨nativeSite, project, nativeInput, nativeNotFree, nativeNotOwing, rawProjection,
    states, law⟩ := exists_comparisonInformationHistory setup leaks bounds horizon scheduler
      sequence scale positive le_one weights assessments fallback assembled bayes n who site
        notFree notOwing
  have nativeNotKeyed : ¬ ownedKeyed
      (Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler))
      (LateDeliveryAgent setup leaks bounds (initialLaw setup) horizon (NativeScheduler))
      ((N).agentAt nativeSite) := by
    intro keyed
    apply notKeyed
    refine ⟨?_, notFree⟩
    change LateDelivery setup leaks who
      (RecoveryProjection.information (runtime setup) leaks site.1)
    rw [← nativeInput]
    exact keyed.1
  have pending : pendingEvent setup leaks who nativeSite.1 ≠ none := by
    rw [nativeInput, atSite, pendingEvent_of_recoveryRecall setup leaks turn unsent]
    exact Option.some_ne_none _
  obtain ⟨unforced, decorrelated⟩ :=
    estimates n who nativeSite nativeNotFree nativeNotOwing nativeNotKeyed pending
  refine ⟨nativeSite, project, nativeInput, rawProjection, states, law, ?_, ?_⟩
  · rw [← law, expect_map] at unforced
    simpa only [Function.comp_def, states] using unforced
  · intro first second firstBounded secondBounded
    have bound := decorrelated first second firstBounded secondBounded
    rw [← law, expect_map, expect_map, expect_map] at bound
    simpa only [Function.comp_def, states] using bound

end Vegas.RecoveryOnePacket
