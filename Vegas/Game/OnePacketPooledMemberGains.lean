/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketKeyedValueBounds
import Vegas.Game.OnePacketStoppedValueComparison
import Vegas.Game.OnePacketPooledGains

/-! # Individual component gains under the common native completion

The actual native terminal values have a common affine operational score.
The original pooled continuation witness therefore bounds every member's
component-mixture gain without changing its assessment or pool weights.
-/

noncomputable section

namespace Vegas.OnePacketComparison

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
  {Public : Type*} {signal : State L setup.context → Public}

local notation "Initial" => initialLaw setup
local notation "Menu" => bounds.onePacketMenu timeouts leaks
local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu timeouts leaks) (initialLaw setup) horizon scheduler

local instance pooledNativeHistoryFintype : Fintype (E).History :=
  (Menu).historyFintype Initial horizon scheduler

open Classical in
/-- Actual native keyed component values have one common success score and
a continuation value above the declared exit payoff, up to a vanishing error. -/
theorem assembled_keyed_component_value_bounds
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slotsPositive : 0 < bounds.candidateCount)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds Initial
      horizon scheduler bounds.candidateCount p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (targetSequence n)
      ((Menu).decisionRecall Initial horizon scheduler).decisionInformationAntichain)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Opportunity timeouts leaks Initial horizon scheduler delay)
    (inclusion : ProtectedInclusion timeouts leaks Initial horizon scheduler bound)
    (timely : (AsyncTimely timeouts) delay bound)
    (completes : CompletesPlay timeouts leaks Initial horizon scheduler)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (payoffBound : ℝ) (nonnegative : 0 ≤ payoffBound)
    (payoffBounded : ∀ who (final : (E).History),
      |exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state who| ≤
        payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (upper : Player → ℝ) (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who) :
    ∃ (continuation : ℕ → (N).InformationAgent (N).playedInformation → ℝ)
      (score : ℕ → Option (LateKey setup timeouts leaks) → LateOption bounds.candidateCount → ℝ)
      (error : ℕ → ℝ), Tendsto error atTop (nhds 0) ∧
      (∀ n key option, 0 ≤ score n key option ∧ score n key option ≤ 1) ∧
      ∀ n (agent : (N).InformationAgent (N).playedInformation),
        ownedKeyed (Vegas.FreeAgent setup timeouts leaks bounds Initial horizon scheduler)
          (LateDeliveryAgent setup timeouts leaks bounds Initial horizon scheduler) agent →
        ¬ OwingAgent setup timeouts leaks bounds Initial horizon scheduler agent →
        ∀ decision : (N).IsDecisionInfo agent.1 agent.2.1,
          excludedPayoff agent.1 ≤ continuation n agent ∧ ∀ option,
          |localValue (2 * horizon + 1) (fun final => final.state)
              (exclusionBase setup timeouts parameter utility excludedPayoff leaks)
                (targetSequence n) (who := agent.1) ⟨agent.2.1, decision⟩
              (lateComponent setup timeouts leaks bounds Initial horizon scheduler (sequence n)
                (scale n) (positive n).le (le_one n) agent.1 agent.2.1 option) -
            (excludedPayoff agent.1 + score n
              (agentLateKey setup timeouts leaks bounds Initial horizon scheduler agent) option *
                (continuation n agent - excludedPayoff agent.1))| ≤ error n := by
  obtain ⟨failureScore, stoppedError, stoppedLimit, scoreUnit, stoppedValues⟩ :=
    Vegas.assembled_keyed_value_bounds setup timeouts leaks bounds horizon scheduler wellFormed
      independent observable sequence sourceMixed scale positive le_one scaleEq covers coversInputs
      capacity slotsPositive weights targetSequence assembled mixed bayes
      (fun control trace _ => opportunity control
        ((Menu).toRawTrace Initial horizon scheduler trace))
      (fun control trace _ => inclusion control ((Menu).toRawTrace Initial horizon scheduler trace))
      timely (fun control trace _ ended => completes control
        ((Menu).toRawTrace Initial horizon scheduler trace) ended)
      parameter utility excludedPayoff payoffBound nonnegative readoutBounded excludedBounded
  obtain ⟨terminalError, terminalLimit, terminalValues⟩ :=
    assembled_terminal_stopped_comparison_bounds setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff wellFormed independent observable sequence sourceMixed
      scale positive le_one scaleEq covers coversInputs capacity weights targetSequence assembled
      mixed bayes opportunity inclusion timely completes nonnegative payoffBounded excludedBounded
  let continuation := fun n (agent : (N).InformationAgent (N).playedInformation) =>
    if decision : (N).IsDecisionInfo agent.1 agent.2.1 then
      siteValue setup timeouts leaks bounds horizon scheduler parameter utility excludedPayoff
        (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy)
        ⟨agent.2.1, decision⟩
    else excludedPayoff agent.1
  let score := fun n (key : Option (LateKey setup timeouts leaks)) option =>
    key.elim 0 (fun key => 1 - failureScore n key option)
  let error := fun n => |terminalError n| + |stoppedError n|
  refine ⟨continuation, score, error, ?_, ?_, ?_⟩
  · simpa only [error, abs_zero, add_zero] using terminalLimit.abs.add stoppedLimit.abs
  · intro n key option
    cases key with
    | none => exact ⟨le_rfl, zero_le_one⟩
    | some key =>
        obtain ⟨lower, higher⟩ := scoreUnit n key option
        change 0 ≤ 1 - failureScore n key option ∧ 1 - failureScore n key option ≤ 1
        constructor <;> linarith
  intro n agent keyed notOwing decision
  let site : (N).InformationSite agent.1 := ⟨agent.2.1, decision⟩
  have agentEq : (N).agentAt site = agent := by cases agent; rfl
  have keyedSite : ownedKeyed (Vegas.FreeAgent setup timeouts leaks bounds Initial horizon
    scheduler)
      (LateDeliveryAgent setup timeouts leaks bounds Initial horizon scheduler)
      ((N).agentAt site) := by simpa only [agentEq] using keyed
  have debtFree : ¬ OwingAgent setup timeouts leaks bounds Initial horizon scheduler
      ((N).agentAt site) := by simpa only [agentEq] using notOwing
  obtain ⟨past, view, event, atSite, pending, _activated⟩ := keyedSite.1
  have pendingAt := pending
  rw [atSite] at pendingAt
  have turn := (pendingEvent_spec (timeouts := timeouts) pendingAt).1
  let key := LateKey.ofView setup timeouts leaks agent.1 past view
  have siteKey : lateKey setup timeouts leaks agent.1 site.1 = some key := by rw [atSite]; rfl
  have agentKey : agentLateKey setup timeouts leaks bounds Initial horizon scheduler agent =
      some key := by
    change lateKey setup timeouts leaks agent.1 agent.2.1 = some key
    exact siteKey
  have continuationEq : continuation n agent =
      siteValue setup timeouts leaks bounds horizon scheduler parameter utility excludedPayoff
        (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site := by
    dsimp only [continuation]
    rw [dite_eq_left decision]
  refine ⟨?_, ?_⟩
  · rw [continuationEq]
    exact (siteValue_mem_Icc setup timeouts leaks bounds horizon scheduler parameter utility
      excludedPayoff (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site
      (upper agent.1) (fun outcome => le_upper outcome agent.1)
      (fun point reached => excludedPayoff_le_of_reached setup parameter utility excludedPayoff
        wellFormed below (sequence n).strategy point reached agent.1)).1
  intro option
  have terminalNear := (terminalValues n agent.1 site keyedSite.2 debtFree atSite turn).1
    (onePacketLate setup timeouts leaks bounds horizon scheduler sequence scale positive le_one n
      ((N).agentAt site) option)
  have stoppedNear := stoppedValues n agent.1 site keyedSite.2 debtFree keyedSite key siteKey option
  dsimp only at terminalNear stoppedNear
  rw [continuationEq, agentKey]
  change |_ - (excludedPayoff agent.1 + (1 - failureScore n key option) *
    (siteValue setup timeouts leaks bounds horizon scheduler parameter utility excludedPayoff
      (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site -
        excludedPayoff agent.1))| ≤ error n
  have combined := (abs_sub_le _ _ _).trans (add_le_add terminalNear stoppedNear)
  exact combined.trans (by
    dsimp only [error]
    linarith [le_abs_self (terminalError n), le_abs_self (stoppedError n)])

open Classical in
/-- The supplied pooled continuation witness bounds every native member's
component-mixture gain by one vanishing error. -/
theorem assembled_pooled_member_gain_bounds
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup timeouts leaks bounds horizon scheduler (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (slotsPositive : 0 < bounds.candidateCount)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds Initial
      horizon scheduler bounds.candidateCount p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (targetSequence n)
      ((Menu).decisionRecall Initial horizon scheduler).decisionInformationAntichain)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Opportunity timeouts leaks Initial horizon scheduler delay)
    (inclusion : ProtectedInclusion timeouts leaks Initial horizon scheduler bound)
    (timely : (AsyncTimely timeouts) delay bound)
    (completes : CompletesPlay timeouts leaks Initial horizon scheduler)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (payoffBound : ℝ) (nonnegative : 0 ≤ payoffBound)
    (payoffBounded : ∀ who (final : (E).History),
      |exclusionBase setup timeouts parameter utility excludedPayoff leaks final.state who| ≤
        payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound)
    (readoutBounded : ∀ who readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ payoffBound)
    (upper : Player → ℝ) (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    (below : ∀ (final : setup.intendedProtocol.History) terminal,
      setup.protocolReadout final.state = some terminal →
        ∀ who, excludedPayoff who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (pooled : ∀ n (alternative : ∀ p, PMF (OnePacketPart setup timeouts leaks bounds Initial
        horizon scheduler bounds.candidateCount p)) p,
      ∑ agent ∈ Finset.univ.filter
          (fun agent =>
            onePacketPool setup timeouts leaks bounds Initial horizon scheduler agent = p),
        (if decision : (N).IsDecisionInfo agent.1 agent.2.1 then
          ((targetSequence n).continuationContext
              ((Menu).bounded Initial horizon scheduler).wellFoundedHistories
              ⟨agent.2.1, decision⟩ (fun final =>
                exclusionBase setup timeouts parameter utility excludedPayoff leaks
                  final.state agent.1)).value
              (((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (onePacketPool setup timeouts leaks bounds Initial horizon scheduler
                  agent)).bind
                  (onePacketComponent setup timeouts leaks bounds Initial horizon scheduler
                    (sequence n) (scale n) (positive n).le (le_one n) agent))) -
            ((targetSequence n).continuationContext
              ((Menu).bounded Initial horizon scheduler).wellFoundedHistories
              ⟨agent.2.1, decision⟩ (fun final =>
                exclusionBase setup timeouts parameter utility excludedPayoff leaks
                  final.state agent.1)).value ((targetSequence n).strategy agent.1)
        else 0) ≤ 0) :
    ∃ memberError : ℕ → ℝ, Tendsto memberError atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who)
        (alternative : PMF (OnePacketPart setup timeouts leaks bounds Initial horizon scheduler
          bounds.candidateCount
          (onePacketPool setup timeouts leaks bounds Initial horizon scheduler ((N).agentAt
            site)))),
        localGain (2 * horizon + 1) (fun final => final.state)
          (exclusionBase setup timeouts parameter utility excludedPayoff leaks)
            (targetSequence n) site
          (alternative.bind (onePacketComponent setup timeouts leaks bounds Initial horizon
            scheduler
            (sequence n) (scale n) (positive n).le (le_one n) ((N).agentAt site))) ≤
          memberError n := by
  obtain ⟨continuation, score, error, limit, _scoreUnit, values⟩ :=
    assembled_keyed_component_value_bounds setup timeouts leaks bounds horizon scheduler
      wellFormed independent observable sequence sourceMixed scale positive le_one scaleEq
      covers coversInputs capacity slotsPositive weights targetSequence assembled mixed bayes
      opportunity inclusion timely completes parameter utility excludedPayoff payoffBound
      nonnegative
      payoffBounded excludedBounded readoutBounded upper le_upper below
  let memberError := fun n =>
    (Fintype.card ((N).InformationAgent (N).playedInformation) : ℝ) * (2 * max (error n) 0)
  have memberLimit : Tendsto memberError atTop (nhds 0) := by
    have clipped : Tendsto (fun n => max (error n) 0) atTop (nhds 0) := by
      simpa only [max_self] using limit.max (tendsto_const_nhds (x := (0 : ℝ)))
    simpa only [mul_zero] using (clipped.const_mul 2).const_mul
      (Fintype.card ((N).InformationAgent (N).playedInformation) : ℝ)
  refine ⟨memberError, memberLimit, ?_⟩
  intro n who site alternative
  have pooledGain := pooledLocalGain_nonpos_of_continuation setup timeouts leaks bounds horizon
    scheduler (fun final => final.state)
    (exclusionBase setup timeouts parameter utility excludedPayoff leaks)
    (targetSequence n) (sequence n) (scale n) (positive n).le (le_one n) (pooled n)
  exact componentGain_le_of_common_values setup timeouts leaks bounds horizon scheduler parameter
    utility excludedPayoff completes (targetSequence n) (sequence n) (scale n) (positive n).le
    (le_one n) (weights n) (onePacketFallback setup timeouts leaks bounds horizon scheduler)
    (assembled n) pooledGain (continuation n) (score n) (error n) (values n) who site alternative

omit [Finite setup.intendedProtocol.History] in
open Classical in
/-- Each late option is an actual part of the same native pool, so it inherits
the member-mixture gain bound. -/
theorem lateComponent_gain_le_of_member_mixtures
    [∀ who, DecidableEq ((N).InfoState who)]
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (assessment : (N).BehavioralAssessment)
    (source : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    {who : Player} (site : (N).InformationSite who)
    (keyed : ownedKeyed (Vegas.FreeAgent setup timeouts leaks bounds Initial horizon scheduler)
      (LateDeliveryAgent setup timeouts leaks bounds Initial horizon scheduler) ((N).agentAt site))
    {error : ℝ}
    (members : ∀ alternative : PMF (OnePacketPart setup timeouts leaks bounds Initial horizon
        scheduler slots (onePacketPool setup timeouts leaks bounds Initial horizon scheduler
          ((N).agentAt site))),
      localGain (2 * horizon + 1) (fun final => final.state)
        (exclusionBase setup timeouts parameter utility excludedPayoff leaks) assessment site
        (alternative.bind (onePacketComponent setup timeouts leaks bounds Initial horizon scheduler
          source scale nonnegative le_one ((N).agentAt site))) ≤ error)
    (option : LateOption slots) :
    localGain (2 * horizon + 1) (fun final => final.state)
      (exclusionBase setup timeouts parameter utility excludedPayoff leaks) assessment site
      (lateComponent setup timeouts leaks bounds Initial horizon scheduler source scale nonnegative
        le_one who site.1 option) ≤ error := by
  let agent := (N).agentAt site
  let prescribed := fun agent : (N).InformationAgent (N).playedInformation =>
    slotPrescribedComponent setup timeouts leaks bounds Initial horizon scheduler source
      scale nonnegative le_one agent.1 agent.2.1
  let lateLaw := fun (agent : (N).InformationAgent (N).playedInformation)
      (option : LateOption slots) =>
    lateComponent setup timeouts leaks bounds Initial horizon scheduler source scale nonnegative
      le_one agent.1 agent.2.1 option
  obtain ⟨identify, same⟩ := freeKeyedComponent_of_not_free
    (key := agentLateKey setup timeouts leaks bounds Initial horizon scheduler)
    (keyed := LateDeliveryAgent setup timeouts leaks bounds Initial horizon scheduler)
    (unforcedLaw setup timeouts leaks bounds Initial horizon scheduler scale nonnegative le_one)
    prescribed lateLaw keyed.2
  let best := keyedBest
    (keyed := ownedKeyed (Vegas.FreeAgent setup timeouts leaks bounds Initial horizon scheduler)
      (LateDeliveryAgent setup timeouts leaks bounds Initial horizon scheduler))
    (key := agentLateKey setup timeouts leaks bounds Initial horizon scheduler) (fun _ => option)
    (keyedPool (ownedKeyed (Vegas.FreeAgent setup timeouts leaks bounds Initial horizon scheduler)
      (LateDeliveryAgent setup timeouts leaks bounds Initial horizon scheduler))
      (agentLateKey setup timeouts leaks bounds Initial horizon scheduler) agent)
  let part := identify.symm best
  have lawEq : onePacketComponent setup timeouts leaks bounds Initial horizon scheduler source scale
      nonnegative le_one agent part = lateLaw agent option := by
    refine (same part).trans ?_
    change InformationModel.keyedComponent prescribed lateLaw agent
      (identify (identify.symm best)) = lateLaw agent option
    rw [identify.apply_symm_apply]
    exact keyedComponent_best_of_keyed prescribed lateLaw (fun _ => option) keyed
  have near := members (PMF.pure part)
  simp only [PMF.pure_bind] at near
  rw [lawEq] at near
  exact near

end Vegas.OnePacketComparison
