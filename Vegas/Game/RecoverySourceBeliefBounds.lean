/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryComparisonSite
import Vegas.Game.RecoveryNativePrefixBounds

/-! # Source replay posterior bounds for the common recovery assessment -/

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
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks

open Classical in
/-- The same comparison weights give uniform source replay posterior convergence
at all forced debt-free own-turn sites, including keyed deliveries. -/
theorem nativeComparison_source_belief_bounds [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [Finite setup.intendedProtocol.History]
    [∀ player, DecidableEq ((N).InfoState player)]
    [∀ player, DecidableEq ((R).InfoState player)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependent)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p)) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ∀ {past : List (application setup leaks).PlayerEntry}
          {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view)),
        ∀ {event : (graph setup).EventId},
          view.application.publicView.ownTurn? who = some event →
        ∀ decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1),
        ∑' point,
          |((((nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
              positive le_one weights n).belief who site).map
                (replayProjection setup leaks bounds horizon (NativeScheduler)
                  (projectedSite setup leaks decision) site atSite rfl)) point).toReal -
            ((sequence n).belief who (projectedSite setup leaks decision) point).toReal| ≤
              error n :=
    by
  let target := nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale
    positive le_one weights
  let nativeWeights := fun n => nativeComparisonWeights setup leaks bounds horizon scheduler
    (weights n)
  have assembled : OnePacketAssembled setup leaks bounds horizon (NativeScheduler) sequence scale
      positive le_one nativeWeights target :=
    nativeComparisonSequence_assembled setup leaks bounds horizon scheduler sequence scale
      positive le_one weights
  have mixed : ∀ n, (target n).IsFullyMixed :=
    nativeComparisonSequence_fullyMixed setup leaks bounds horizon scheduler sequence scale
      positive le_one weights
  have bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (target n)
      ((NMenu).decisionRecall (initialLaw setup) horizon
        (NativeScheduler)).decisionInformationAntichain :=
    nativeComparisonSequence_bayes setup leaks bounds horizon scheduler sequence scale positive
      le_one weights
  let eligible := fun who (site : (N).InformationSite who) =>
    ¬ Vegas.FreeAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) ∧
      ¬ Vegas.OwingAgent setup leaks bounds horizon (NativeScheduler) ((N).agentAt site) ∧
      ∃ (past : List (application setup leaks).PlayerEntry)
        (view : (application setup leaks).PlayerView) (event : (graph setup).EventId),
        site.1 = some (past, view) ∧ view.application.publicView.ownTurn? who = some event
  let estimate := fun n who (site : (N).InformationSite who) error =>
    ∀ (past : List (application setup leaks).PlayerEntry)
      (view : (application setup leaks).PlayerView) (atSite : site.1 = some (past, view))
      (event : (graph setup).EventId), view.application.publicView.ownTurn? who = some event →
      ∀ decision : setup.intendedModel.IsDecisionInfo who (projectView setup leaks who site.1),
      ∑' point,
        |((((target n).belief who site).map (replayProjection setup leaks bounds horizon
            (NativeScheduler) (projectedSite setup leaks decision) site atSite rfl)) point).toReal -
          ((sequence n).belief who (projectedSite setup leaks decision) point).toReal| ≤ error
  obtain ⟨error, limit, uniform⟩ := exists_uniform_of_sites setup leaks bounds horizon
    (NativeScheduler) estimate
    (fun _ _ _ _ _ grows holds past view atSite event turn decision =>
      (holds past view atSite event turn decision).trans grows) eligible
    (fun who site good => by
      obtain ⟨notFree, notOwing, past, view, event, atSite, turn⟩ := good
      have forced := forcedAgent_of_not_free setup leaks bounds horizon (NativeScheduler) notFree
      have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon (NativeScheduler)
        notOwing
      have decision := projectedDecision_of_forcedAgent wellFormed forced atSite turn debtFree
      let inputs : OnePacketBeliefInputs setup leaks bounds horizon (NativeScheduler) sequence
          target site (projectedSite setup leaks decision) atSite rfl :=
        { toOnePacketCounterpartInputs := OnePacketCounterpartInputs.ofBindingRepairs wellFormed
            independent sourceMixed positive le_one scaleEq covers coversInputs capacity
            nativeWeights assembled mixed notFree notOwing atSite turn
          toOnePacketOwnInputs := OnePacketOwnInputs.ofAssembled wellFormed sourceMixed
            (2 * horizon + 2) scaleEq covers coversInputs capacity assembled notFree notOwing
            atSite rfl turn }
      have convergence := onePacket_beliefConverges setup leaks bounds horizon (NativeScheduler)
        wellFormed sourceMixed sourceBayes mixed bayes atSite rfl forced turn inputs
      refine ⟨_, convergence, ?_⟩
      intro n otherPast otherView otherAt otherEvent _otherTurn otherDecision
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (atSite.symm.trans otherAt))
      exact le_rfl)
  exact ⟨error, limit, fun n who site notFree notOwing past view atSite event turn decision =>
    uniform n who site ⟨notFree, notOwing, past, view, event, atSite, turn⟩ past view atSite event
      turn decision⟩

open Classical in
/-- The original recovery posterior, projected through its complete clear
history and then replayed at the source, approaches the original source posterior. -/
theorem recovery_source_belief_bounds [Fintype (RP).History]
    [(application setup leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [Finite setup.intendedProtocol.History]
    [∀ player, DecidableEq ((N).InfoState player)]
    [∀ player, DecidableEq ((R).InfoState player)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependent)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
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
      ((Recovery.onePacketMenu (runtime setup) leaks bounds).decisionInformationAntichain
        Initial horizon scheduler)) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (R).InformationSite who),
        ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ¬ OwingAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ∀ {past : List (recoveryApplication (runtime setup) leaks).PlayerEntry}
          {view : (recoveryApplication (runtime setup) leaks).PlayerView},
        site.1 = some (past, view) → ∀ {event : (graph setup).EventId},
        view.application.1.publicView.ownTurn? who = some event →
        ∃ (nativeSite : (N).InformationSite who)
          (project : (R).InformationHistory who site.1 → (N).InformationHistory who nativeSite.1)
          (atNative : nativeSite.1 = some
            (past.map (RecoveryProjection.playerEntry (runtime setup) leaks),
              RecoveryProjection.playerView (runtime setup) leaks view))
          (decision : setup.intendedModel.IsDecisionInfo who
            (projectView setup leaks who nativeSite.1)),
          nativeSite.1 = RecoveryProjection.information (runtime setup) leaks site.1 ∧
          (∀ history, (project history).1.state =
            protocolState (runtime setup) leaks history.1.state) ∧
          ((assessments n).belief who site).map project =
            (nativeComparisonSequence setup leaks bounds horizon scheduler sequence scale positive
              le_one weights n).belief who nativeSite ∧
          ∑' point,
            |((((assessments n).belief who site).map (fun history =>
                replayProjection setup leaks bounds horizon (NativeScheduler)
                  (projectedSite setup leaks decision) nativeSite atNative rfl
                  (project history))) point).toReal -
              ((sequence n).belief who (projectedSite setup leaks decision) point).toReal| ≤
              error n := by
  obtain ⟨error, limit, estimates⟩ := nativeComparison_source_belief_bounds setup leaks bounds
    horizon scheduler wellFormed independent sequence sourceMixed sourceBayes scale positive le_one
    scaleEq covers coversInputs capacity weights
  refine ⟨error, limit, ?_⟩
  intro n who site notFree notOwing past view atSite event turn
  obtain ⟨nativeSite, project, nativeInput, nativeNotFree, nativeNotOwing, _raw, states, law⟩ :=
    exists_comparisonInformationHistory setup leaks bounds horizon scheduler sequence scale positive
      le_one weights assessments fallback assembled bayes n who site notFree notOwing
  let nativePast := past.map (RecoveryProjection.playerEntry (runtime setup) leaks)
  let nativeView := RecoveryProjection.playerView (runtime setup) leaks view
  have nativeAt : nativeSite.1 = some (nativePast, nativeView) := by
    rw [nativeInput, atSite]
    rfl
  have nativeTurn : nativeView.application.publicView.ownTurn? who = some event := turn
  have forced := forcedAgent_of_not_free setup leaks bounds horizon (NativeScheduler) nativeNotFree
  have debtFree := siteDebtFree_of_not_owing setup leaks bounds horizon (NativeScheduler)
    nativeNotOwing
  have decision := projectedDecision_of_forcedAgent wellFormed forced nativeAt nativeTurn debtFree
  have bound := estimates n who nativeSite nativeNotFree nativeNotOwing nativeAt nativeTurn decision
  rw [← law, PMF.map_comp] at bound
  exact ⟨nativeSite, project, nativeAt, decision, nativeInput, states, law, bound⟩
end Vegas.RecoveryOnePacket
