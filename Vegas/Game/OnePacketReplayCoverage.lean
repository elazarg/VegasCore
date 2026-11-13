module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketDecisionCoverage
public import Vegas.Game.OnePacketBeliefFidelity
public import Vegas.Game.OnePacketCommonCompletion

@[expose] public section

/-! # Every legal source history has an exact native replay preimage -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  {Public : Type*} {signal : State L setup.context → Public}

local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler

local instance exactReplayHistoryFintype : Fintype
    ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon scheduler).History :=
  (bounds.onePacketMenu timeouts leaks).historyFintype (initialLaw setup) horizon scheduler

/-- Every intended history in a realized source decision fiber has an actual native replay
preimage, whether or not the preserved equilibrium assigns that history positive probability. -/
theorem exists_native_replay_at_sourceDecision
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (reference : setup.intendedModel.BehavioralAssessment) (full : reference.IsFullyMixed)
    (referenceBayes : BehavioralAssessment.IsBayesConsistent setup.intendedModel reference
      setup.intended_decision_antichain)
    {who : Player} (sourceSite : setup.intendedModel.InformationSite who)
    (nativeSite : (N).InformationSite who)
    (realization : SourceDecisionRealization setup timeouts leaks bounds horizon scheduler
      sourceSite nativeSite)
    (sourceHistory : setup.intendedModel.InformationHistory who sourceSite.1) :
    ∃ history : (N).InformationHistory who nativeSite.1,
      intendedHistory? setup timeouts leaks bounds horizon scheduler history.1.trace =
        some sourceHistory.1 := by
  classical
  let sources : ℕ → setup.intendedModel.BehavioralAssessment := fun _ => reference
  let floors := fun n => combinedFloor setup timeouts leaks bounds horizon scheduler (sources n)
  let scale := fun n => trembleScale (floors n) (2 * horizon + 2) n
  have floorPositive := fun n =>
    combinedFloor_pos setup timeouts leaks bounds horizon scheduler (sources n)
  have floorLeOne := fun n =>
    combinedFloor_le_one setup timeouts leaks bounds horizon scheduler (sources n)
  have positive : ∀ n, 0 < scale n := fun n => trembleScale_pos (floorPositive n)
  have le_one : ∀ n, scale n ≤ 1 := fun n =>
    trembleScale_le_one (floorPositive n).le (floorLeOne n)
  have vanishes : Tendsto scale atTop (nhds 0) :=
    tendsto_trembleScale floors floorPositive floorLeOne
  obtain ⟨weights, sequence, limit, index, assembled, mixed, bayes, increasing, converges,
      _consistent, _pooled, _limits, _freeOptimal, _publicOptimal⟩ :=
    setup.exists_onePacket_consistent_completion timeouts leaks bounds (initialLaw setup) horizon
      scheduler (fun _ => ()) (fun _ _ => (0 : ℝ)) (fun _ => 0) sources bounds.candidateCount
      scale positive le_one vanishes
  have assembledNative : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sources
      scale positive le_one weights sequence := assembled
  have clear := clearInput_of_projected_intended_site wellFormed sourceSite nativeSite
    realization.projected
  have debtFree := siteDebtFree_of_projected_intended_site wellFormed sourceSite nativeSite
    realization.projected
  have notFree : ¬ FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt nativeSite) := not_not.mpr ⟨clear, realization.forced⟩
  have notOwing : ¬ OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt nativeSite) := by
    rintro ⟨history, point, decoded, owes⟩
    exact debtFree history point decoded owes
  obtain ⟨past, view, event, atSite, pending, _first⟩ := realization.first
  have turn := (pendingEvent_spec (by simpa only [atSite] using pending)).1
  have decision : setup.intendedModel.IsDecisionInfo who
      (projectView setup timeouts leaks who nativeSite.1) := realization.projected ▸ sourceSite.2
  have canonicalEq : projectedSite setup timeouts leaks decision = sourceSite :=
    Subtype.ext realization.projected.symm
  have replayLaw := assembled_limit_belief_replay_law setup timeouts leaks bounds horizon scheduler
    wellFormed independent observable sources (fun _ => full) (fun _ => referenceBayes) scale
    positive le_one (fun _ => rfl) covers coversInputs capacity weights sequence assembledNative
    mixed bayes reference limit (behavioralAssessmentConvergesPointwise_const reference) index
    increasing converges nativeSite notFree notOwing atSite turn decision
  let sourceReplayLaw := fun site : setup.intendedModel.InformationSite who =>
    (reference.belief who site).map (fun history => some history.1)
  have displayedReplayLaw :
      (limit.belief who nativeSite).map (fun history =>
        intendedHistory? setup timeouts leaks bounds horizon scheduler history.1.trace) =
      (reference.belief who sourceSite).map (fun history => some history.1) :=
    replayLaw.trans (congrArg sourceReplayLaw canonicalEq)
  have sourceMass := setup.intendedModel.informationMass_pos_of_fullSupport reference.strategy
    full who sourceSite
  have sourcePositive := setup.intendedModel.historyReachWeight_pos_of_fullSupport
    reference.strategy full sourceHistory.1
  have sourceFinite := ne_top_of_le_ne_top ENNReal.one_ne_top
    (setup.intendedModel.informationMass_le_one reference.strategy who sourceSite
      (setup.intended_decision_antichain who sourceSite))
  have supported : sourceHistory ∈ (reference.belief who sourceSite).support := by
    apply (reference.belief who sourceSite).mem_support_iff sourceHistory |>.mpr
    rw [referenceBayes who sourceSite sourceMass sourceHistory]
    exact ENNReal.div_ne_zero.mpr ⟨sourcePositive.ne', sourceFinite⟩
  have replaySupported : some sourceHistory.1 ∈
      ((limit.belief who nativeSite).map (fun history =>
        intendedHistory? setup timeouts leaks bounds horizon scheduler
          history.1.trace)).support := by
    rw [displayedReplayLaw, PMF.support_map]
    exact ⟨sourceHistory, supported, rfl⟩
  rw [PMF.support_map] at replaySupported
  obtain ⟨history, _supportedHistory, replayed⟩ := replaySupported
  exact ⟨history, replayed⟩

end Vegas
