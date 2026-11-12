module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketAssessmentFidelity
public import Vegas.Game.OnePacketDecisionCoverage

@[expose] public section

/-! # Simultaneous assessment fidelity of the common native completion -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  {Public : Type*} {signal : State L setup.context → Public}

local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler
local notation "menu" => bounds.onePacketMenu timeouts leaks
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) (initialLaw setup) horizon scheduler

local instance fidelityAssemblyHistoryFintype : Fintype (E).History :=
  (menu).historyFintype (initialLaw setup) horizon scheduler

/-- The common assessment limit simultaneously retains intended strategies, actual replay
posteriors and complete clean-boundary continuations. -/
theorem onePacketAssembled_limit_fidelity
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (vanishes : Tendsto scale atTop (nhds 0))
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler bounds.candidateCount p))
    (target : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence
      scale positive le_one weights target)
    (mixed : ∀ n, (target n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (target n)
      ((bounds.onePacketMenu timeouts leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    (intended : setup.intendedModel.BehavioralAssessment)
    (native : (N).BehavioralAssessment)
    (sourceConverges : BehavioralAssessmentConvergesPointwise sequence intended)
    (index : ℕ → ℕ) (increasing : StrictMono index)
    (nativeConverges : BehavioralAssessmentConvergesPointwise (fun n => target (index n)) native)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Opportunity timeouts leaks (initialLaw setup) horizon scheduler delay)
    (inclusion : ProtectedInclusion timeouts leaks (initialLaw setup) horizon scheduler bound)
    (completes : CompletesPlay timeouts leaks (initialLaw setup) horizon scheduler)
    (timely : (AsyncTimely timeouts) delay bound) :
    OnePacketAssessmentFidelity setup timeouts leaks bounds horizon scheduler intended native := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro who sourceSite site realization
    exact onePacketAssembled_limit_strategy_of_firstActivation setup timeouts leaks bounds horizon
      scheduler sequence scale positive le_one vanishes weights target assembled index increasing
      sourceConverges nativeConverges site sourceSite realization.projected realization.first
      realization.forced realization.clear
  · intro who site clear forced debtFree past view atSite event turn decision
    have notFree : ¬ FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
        ((N).agentAt site) := not_not.mpr ⟨clear, forced⟩
    have notOwing : ¬ OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
        ((N).agentAt site) := by
      rintro ⟨history, point, decoded, owes⟩
      exact debtFree history point decoded owes
    exact assembled_limit_belief_replay_law setup timeouts leaks bounds horizon scheduler wellFormed
      independent observable sequence sourceMixed sourceBayes scale positive le_one scaleEq covers
      coversInputs capacity weights target assembled mixed bayes intended native sourceConverges
      index increasing nativeConverges site notFree notOwing atSite turn decision
  · intro rank start anchor state boundary point decoded pointIntended
    rw [ReactiveApplication.ResponseMenu.runFrom_eq_terminal]
    exact OnePacketComparison.assembled_boundary_readout_law_of_converges wellFormed covers
      capacity sequence intended sourceConverges scale positive le_one vanishes weights target
      assembled native index increasing nativeConverges
      (fun control trace _ => opportunity control
        ((menu).toRawTrace (initialLaw setup) horizon scheduler trace))
      (fun control trace _ => inclusion control
        ((menu).toRawTrace (initialLaw setup) horizon scheduler trace)) timely
      (fun control trace _ ended => completes control
        ((menu).toRawTrace (initialLaw setup) horizon scheduler trace) ended)
      ((menu).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories rank start anchor
      state boundary point decoded pointIntended
  · intro who sourceSite sourceHistory
    exact exists_sourceDecisionRealization_of_intended_history wellFormed
      (fun control trace _ => opportunity control
        ((menu).toRawTrace (initialLaw setup) horizon scheduler trace))
      (fun control trace _ => inclusion control
        ((menu).toRawTrace (initialLaw setup) horizon scheduler trace)) timely
      (fun control trace _ ended => completes control
        ((menu).toRawTrace (initialLaw setup) horizon scheduler trace) ended)
      covers capacity ((menu).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
      (sequence 0) (sourceMixed 0) sourceSite sourceHistory

omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- At a realized source decision, the native actual-replay posterior is exactly the posterior of
the displayed source site. -/
theorem OnePacketAssessmentFidelity.belief_of_realization
    {intended : setup.intendedModel.BehavioralAssessment} {native : (N).BehavioralAssessment}
    (fidelity : OnePacketAssessmentFidelity setup timeouts leaks bounds horizon scheduler
      intended native)
    {who : Player} (sourceSite : setup.intendedModel.InformationSite who)
    (site : (N).InformationSite who)
    (realization : SourceDecisionRealization setup timeouts leaks bounds horizon scheduler
      sourceSite site) :
    (native.belief who site).map (fun history =>
      intendedHistory? setup timeouts leaks bounds horizon scheduler history.1.trace) =
    (intended.belief who sourceSite).map (fun history => some history.1) := by
  obtain ⟨past, view, event, atSite, pending, _first⟩ := realization.first
  have turn := (pendingEvent_spec (by simpa only [atSite] using pending)).1
  have decision : setup.intendedModel.IsDecisionInfo who
      (projectView setup timeouts leaks who site.1) := realization.projected ▸ sourceSite.2
  have sourceEq : projectedSite setup timeouts leaks decision = sourceSite :=
    Subtype.ext realization.projected.symm
  let replayLaw := fun source : setup.intendedModel.InformationSite who =>
    (intended.belief who source).map (fun history => some history.1)
  exact (fidelity.belief site realization.clear realization.forced realization.debtFree atSite
    turn decision).trans (congrArg replayLaw sourceEq)

omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- Every posterior-supported native history at a realized decision replays to an actually
supported history of the displayed intended source posterior. -/
theorem OnePacketAssessmentFidelity.supported_replay_of_realization
    {intended : setup.intendedModel.BehavioralAssessment} {native : (N).BehavioralAssessment}
    (fidelity : OnePacketAssessmentFidelity setup timeouts leaks bounds horizon scheduler
      intended native)
    {who : Player} (sourceSite : setup.intendedModel.InformationSite who)
    (site : (N).InformationSite who)
    (realization : SourceDecisionRealization setup timeouts leaks bounds horizon scheduler
      sourceSite site)
    (history : (N).InformationHistory who site.1)
    (supported : history ∈ (native.belief who site).support) :
    ∃ replay : setup.intendedModel.InformationHistory who sourceSite.1,
      replay ∈ (intended.belief who sourceSite).support ∧
      intendedHistory? setup timeouts leaks bounds horizon scheduler history.1.trace =
        some replay.1 := by
  have law := OnePacketAssessmentFidelity.belief_of_realization setup timeouts leaks bounds horizon
    scheduler fidelity sourceSite site realization
  have member : intendedHistory? setup timeouts leaks bounds horizon scheduler history.1.trace ∈
      ((intended.belief who sourceSite).map (fun replay => some replay.1)).support := by
    rw [← law, PMF.support_map]
    exact ⟨history, supported, rfl⟩
  rw [PMF.support_map] at member
  obtain ⟨replay, supportedReplay, same⟩ := member
  exact ⟨replay, supportedReplay, same.symm⟩

end Vegas
