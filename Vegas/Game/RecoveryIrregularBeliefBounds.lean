/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryComparisonSite
import Vegas.Game.RecoveryNativePrefixBounds
import Vegas.Game.OnePacketLateCommitBlind

/-! # Irregular-history posterior bounds for the common recovery assessment

Directed counterparts control complete trace irregularity before the endpoint
forced-region estimate is taken. The exact posterior history projection carries
that stronger estimate to actual clear recovery information fibers.
-/

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
local notation "RMenu" => Recovery.onePacketMenu runtime leaks bounds
local notation "NMenu" => bounds.onePacketMenu runtime leaks

open Classical in
/-- Concrete directed binding counterparts make complete trace irregularity
vanish uniformly at native forced debt-free own-turn sites. The comparison
sequence retains the original recovery completion weights. -/
theorem nativeComparison_irregular_bounds [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [Finite setup.intendedProtocol.History]
    [∀ player, DecidableEq ((N).InfoState player)]
    [∀ player, DecidableEq ((R).InfoState player)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup runtime leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup runtime leaks bounds Initial horizon scheduler bounds.candidateCount p)) :
    ∃ drift : ℕ → ℝ, Tendsto drift atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ Vegas.FreeAgent setup runtime leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup runtime leaks bounds horizon (NativeScheduler) ((N).agentAt site) →
        ∀ {past : List (application setup runtime leaks).PlayerEntry}
          {view : (application setup runtime leaks).PlayerView}, site.1 = some (past, view) →
        ∀ {event : (graph setup).EventId},
          view.application.publicView.ownTurn? who = some event →
        expect ((nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence
          scale
          positive le_one weights n).belief who site) (fun history =>
          if RegularTrace setup runtime leaks bounds horizon (NativeScheduler) (sequence n) who
            history.1.trace then (0 : ℝ) else 1) ≤ drift n := by
  classical
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
  let good := fun who (site : (N).InformationSite who) =>
    ¬ Vegas.FreeAgent setup runtime leaks bounds horizon (NativeScheduler) ((N).agentAt site) ∧
      ¬ Vegas.OwingAgent setup runtime leaks bounds horizon (NativeScheduler) ((N).agentAt site) ∧
      ∃ (past : List (application setup runtime leaks).PlayerEntry)
        (view : (application setup runtime leaks).PlayerView) (event : (graph setup).EventId),
        site.1 = some (past, view) ∧ view.application.publicView.ownTurn? who = some event
  obtain ⟨drift, limit, uniform⟩ := exists_uniform_of_sites setup runtime leaks bounds horizon
    (NativeScheduler)
    (fun n who site error => expect ((target n).belief who site) (fun history =>
      if RegularTrace setup runtime leaks bounds horizon (NativeScheduler) (sequence n) who
        history.1.trace
        then (0 : ℝ) else 1) ≤ error)
    (fun _ _ _ _ _ le bound => bound.trans le) good (fun who site eligible => by
      obtain ⟨notFree, notOwing, past, view, event, atSite, turn⟩ := eligible
      have inputs := OnePacketCounterpartInputs.ofBindingRepairs (runtime := runtime) wellFormed
        independent
        observable sourceMixed
        positive le_one scaleEq covers coversInputs capacity nativeWeights assembled mixed notFree
        notOwing atSite turn
      exact ⟨_, onePacket_irregularVanishes setup runtime leaks bounds horizon (NativeScheduler)
        mixed bayes
        inputs, fun _ => le_rfl⟩)
  exact ⟨drift, limit, fun n who site notFree notOwing past view atSite event turn =>
    uniform n who site ⟨notFree, notOwing, past, view, event, atSite, turn⟩⟩


open Classical in
/-- The complete actual recovery posterior has vanishing irregular-trace mass
after its genuine history projection, for the unchanged common assessment.
No endpoint forcedness implication is used to infer trace regularity. -/
theorem recovery_irregular_belief_bounds [Fintype (RP).History]
    [(recoveryApplication runtime leaks).FiniteNature Initial scheduler]
    [Finite setup.intendedProtocol.History]
    [∀ player, DecidableEq ((R).InfoState player)]
    [∀ player, DecidableEq ((N).InfoState player)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup runtime leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup runtime leaks bounds Initial horizon scheduler bounds.candidateCount p))
    (assessments : ℕ → (R).BehavioralAssessment)
    (fallback : ℕ → ∀ player, (R).Policy player)
    (assembled : ∀ n, (assessments n).strategy = (R).agentBehavior (R).playedInformation
      (fallback n)
      (fun agent => (weights n (pool setup runtime leaks bounds Initial horizon scheduler
        agent)).bind
        (component setup runtime leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (R) (assessments n)
      ((RMenu).decisionInformationAntichain Initial horizon scheduler)) :
    ∃ drift : ℕ → ℝ, Tendsto drift atTop (nhds 0) ∧
      ∀ n who (site : (R).InformationSite who),
        ¬ FreeAgent setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ¬ OwingAgent setup runtime leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ∀ {past : List (recoveryApplication runtime leaks).PlayerEntry}
          {view : (recoveryApplication runtime leaks).PlayerView},
        site.1 = some (past, view) →
        ∀ {event : (graph setup).EventId},
        view.application.1.publicView.ownTurn? who = some event →
        ∃ (nativeSite : (N).InformationSite who)
          (project : (R).InformationHistory who site.1 →
            (N).InformationHistory who nativeSite.1),
          nativeSite.1 = RecoveryProjection.information runtime leaks site.1 ∧
          (∀ history : (R).InformationHistory who site.1, ∃ clear :
              ∀ current, history.1.state = some current →
                current.execution.application.excluded = ∅,
            (NMenu).toRawHistory (initialLaw setup) horizon (NativeScheduler) (project history).1 =
              Equiv.cast (congrArg (fun initial : PMF (EventGraphRuntime.State (graph setup)) =>
                ((application setup runtime leaks).protocol initial horizon
                  (NativeScheduler)).History)
                  (initialLaw_native setup))
                (nativeHistory runtime leaks Initial horizon scheduler
                  ((RMenu).toRawHistory Initial horizon scheduler history.1) clear)) ∧
          (∀ history, (project history).1.state =
            protocolState runtime leaks history.1.state) ∧
          ((assessments n).belief who site).map project =
            (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale
              positive
              le_one weights n).belief who nativeSite ∧
          ((((assessments n).belief who site).map
              (fun history => (project history).1)).toOuterMeasure
            {history | ¬ RegularTrace setup runtime leaks bounds horizon (NativeScheduler)
              (sequence n) who history.trace}).toReal ≤ drift n := by
  obtain ⟨drift, limit, estimates⟩ := nativeComparison_irregular_bounds setup runtime leaks bounds
    horizon
    scheduler wellFormed independent observable sequence sourceMixed scale positive le_one
    scaleEq covers
    coversInputs capacity weights
  refine ⟨drift, limit, ?_⟩
  intro n who site notFree notOwing past view atSite event turn
  obtain ⟨nativeSite, project, nativeInput, nativeNotFree, nativeNotOwing, raw, states, law⟩ :=
    exists_comparisonInformationHistory setup runtime leaks bounds horizon scheduler sequence
      scale positive
      le_one weights assessments fallback assembled bayes n who site notFree notOwing
  let nativePast := past.map (RecoveryProjection.playerEntry runtime leaks)
  let nativeView := RecoveryProjection.playerView runtime leaks view
  have nativeAt : nativeSite.1 = some (nativePast, nativeView) := by
    rw [nativeInput, atSite]
    rfl
  have nativeTurn : nativeView.application.publicView.ownTurn? who = some event := turn
  have bound := estimates n who nativeSite nativeNotFree nativeNotOwing nativeAt nativeTurn
  rw [← law, expect_map] at bound
  refine ⟨nativeSite, project, nativeInput, raw, states, law, ?_⟩
  let posterior := (assessments n).belief who site
  let forget := fun history : (R).InformationHistory who site.1 => (project history).1
  let bad := {history : (onePacketProtocol setup runtime leaks bounds horizon
    (NativeScheduler)).History |
    ¬ RegularTrace setup runtime leaks bounds horizon (NativeScheduler) (sequence n) who
      history.trace}
  let indicator := fun history => @ite ℝ (history ∈ bad) (Classical.propDecidable _) 1 0
  have payoffEq : indicator ∘ forget = (fun history =>
      if RegularTrace setup runtime leaks bounds horizon (NativeScheduler) (sequence n) who
        (project history).1.trace then (0 : ℝ) else 1) := by
    funext history
    by_cases regular : RegularTrace setup runtime leaks bounds horizon (NativeScheduler) (sequence
      n) who
        (project history).1.trace <;> simp [indicator, forget, bad, regular]
  calc
    _ = expect (posterior.map forget) indicator := (expect_indicator (posterior.map forget)
      bad).symm
    _ = expect posterior (indicator ∘ forget) := expect_map forget posterior indicator
    _ = _ := congrArg (expect posterior) payoffEq
    _ ≤ _ := bound

end Vegas.RecoveryOnePacket
