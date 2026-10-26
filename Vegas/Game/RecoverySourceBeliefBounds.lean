/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryNativePrefixBounds
import Vegas.Game.OnePacketLateCommitBlind

/-! # Source replay posterior bounds for the common recovery assessment -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

variable {Public : Type*} {signal : State L setup.context → Public}

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler runtime leaks scheduler
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler
local notation "NMenu" => bounds.onePacketMenu runtime leaks

open Classical in
/-- The same comparison weights give uniform source replay posterior convergence
at all forced debt-free own-turn sites, including keyed deliveries. -/
theorem nativeComparison_source_belief_bounds [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [Finite setup.intendedProtocol.History]
    [∀ player, DecidableEq ((N).InfoState player)]
    [∀ player, DecidableEq ((R).InfoState player)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup runtime leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup runtime leaks bounds Initial horizon scheduler bounds.candidateCount p)) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ Vegas.FreeAgent setup runtime leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup runtime leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ∀ {past : List (application setup runtime leaks).PlayerEntry}
          {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past,
            view)),
        ∀ {event : (graph setup).EventId},
          view.application.publicView.ownTurn? who = some event →
        ∀ decision : setup.intendedModel.IsDecisionInfo who (projectView setup runtime leaks who
          site.1),
        ∑' point,
          |((((nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale
              positive le_one weights n).belief who site).map
                (replayProjection setup runtime leaks bounds horizon (NativeScheduler)
                  (projectedSite setup runtime leaks decision) site atSite rfl)) point).toReal -
            ((sequence n).belief who (projectedSite setup runtime leaks decision) point).toReal| ≤
              error n :=
    by
  let target := nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale
    positive le_one weights
  let nativeWeights := fun n => nativeComparisonWeights setup runtime leaks bounds horizon scheduler
    (weights n)
  have assembled : OnePacketAssembled setup runtime leaks bounds horizon (NativeScheduler)
    sequence scale
      positive le_one nativeWeights target :=
    nativeComparisonSequence_assembled setup runtime leaks bounds horizon scheduler sequence scale
      positive le_one weights
  have mixed : ∀ n, (target n).IsFullyMixed :=
    nativeComparisonSequence_fullyMixed setup runtime leaks bounds horizon scheduler sequence scale
      positive le_one weights
  have bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (target n)
      ((NMenu).decisionRecall (initialLaw setup) horizon
        (NativeScheduler)).decisionInformationAntichain :=
    nativeComparisonSequence_bayes setup runtime leaks bounds horizon scheduler sequence scale
      positive
      le_one weights
  let eligible := fun who (site : (N).InformationSite who) =>
    ¬ Vegas.FreeAgent setup runtime leaks bounds horizon (NativeScheduler) ((N).agentAt site) ∧
      ¬ Vegas.OwingAgent setup runtime leaks bounds horizon (NativeScheduler) ((N).agentAt site) ∧
      ∃ (past : List (application setup runtime leaks).PlayerEntry)
        (view : (application setup runtime leaks).PlayerView) (event : (graph setup).EventId),
        site.1 = some (past, view) ∧ view.application.publicView.ownTurn? who = some event
  let estimate := fun n who (site : (N).InformationSite who) error =>
    ∀ (past : List (application setup runtime leaks).PlayerEntry)
      (view : (application setup runtime leaks).PlayerView) (atSite : site.1 = some (past, view))
      (event : (graph setup).EventId), view.application.publicView.ownTurn? who = some event →
      ∀ decision : setup.intendedModel.IsDecisionInfo who (projectView setup runtime leaks who
        site.1),
      ∑' point,
        |((((target n).belief who site).map (replayProjection setup runtime leaks bounds horizon
            (NativeScheduler) (projectedSite setup runtime leaks decision) site atSite rfl))
              point).toReal -
          ((sequence n).belief who (projectedSite setup runtime leaks decision) point).toReal| ≤
            error
  obtain ⟨error, limit, uniform⟩ := exists_uniform_of_sites setup runtime leaks bounds horizon
    (NativeScheduler) estimate
    (fun _ _ _ _ _ grows holds past view atSite event turn decision =>
      (holds past view atSite event turn decision).trans grows) eligible
    (fun who site good => by
      obtain ⟨notFree, notOwing, past, view, event, atSite, turn⟩ := good
      have forced := forcedAgent_of_not_free setup runtime leaks bounds horizon (NativeScheduler)
        notFree
      have debtFree := siteDebtFree_of_not_owing setup runtime leaks bounds horizon
        (NativeScheduler)
        notOwing
      have decision := projectedDecision_of_forcedAgent (runtime := runtime) wellFormed forced
        atSite turn debtFree
      let inputs : OnePacketBeliefInputs setup runtime leaks bounds horizon (NativeScheduler)
        sequence
          target site (projectedSite setup runtime leaks decision) atSite rfl :=
        { toOnePacketCounterpartInputs :=
          OnePacketCounterpartInputs.ofBindingRepairs (runtime := runtime) wellFormed
            independent observable sourceMixed positive le_one scaleEq covers coversInputs capacity
            nativeWeights assembled mixed notFree notOwing atSite turn
          toOnePacketOwnInputs := OnePacketOwnInputs.ofAssembled (runtime :=
            runtime) wellFormed sourceMixed
            (2 * horizon + 2) scaleEq covers coversInputs capacity assembled notFree notOwing
            atSite rfl turn }
      have convergence := onePacket_beliefConverges setup runtime leaks bounds horizon
        (NativeScheduler)
        wellFormed sourceMixed sourceBayes mixed bayes atSite rfl forced turn inputs
      refine ⟨_, convergence, ?_⟩
      intro n otherPast otherView otherAt otherEvent _otherTurn otherDecision
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (atSite.symm.trans otherAt))
      exact le_rfl)
  exact ⟨error, limit, fun n who site notFree notOwing past view atSite event turn decision =>
    uniform n who site ⟨notFree, notOwing, past, view, event, atSite, turn⟩ past view atSite event
      turn decision⟩

end Vegas.RecoveryOnePacket
