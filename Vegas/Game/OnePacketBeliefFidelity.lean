module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketSourceBeliefBounds
public import Vegas.Game.OnePacketIrregularBeliefBounds

@[expose] public section

/-! # Exact intended posteriors through actual native replay -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

private theorem atom_eq_of_real_eq {α : Type} (p q : PMF α) (a : α)
    (same : (p a).toReal = (q a).toReal) : p a = q a := by
  have mapped := congrArg ENNReal.ofReal same
  simpa only [ENNReal.ofReal_toReal (p.apply_ne_top a),
    ENNReal.ofReal_toReal (q.apply_ne_top a)] using mapped

private theorem projected_belief_limit_eq {α β : Type} [Fintype β]
    {pseq : ℕ → PMF α} {qseq : ℕ → PMF β} {p : PMF α} {q : PMF β}
    (project : α → β) {error : ℕ → ℝ}
    (pconv : PMFConvergesPointwise pseq p)
    (qconv : PMFConvergesPointwise qseq q)
    (econv : Tendsto error atTop (nhds 0))
    (bound : ∀ n, ∑ b, |((pseq n).map project b).toReal - (qseq n b).toReal| ≤ error n) :
    p.map project = q := by
  apply PMF.ext
  intro b
  have converges := (((pconv.map project).toReal b).sub (qconv.toReal b)).abs
  have le_zero : |(p.map project b).toReal - (q b).toReal| ≤ 0 :=
    le_of_tendsto_of_tendsto converges econv (Eventually.of_forall fun n =>
      (Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => abs_nonneg
        (((pseq n).map project a).toReal - (qseq n a).toReal))
          (Finset.mem_univ b)).trans (bound n))
  exact atom_eq_of_real_eq _ _ b (sub_eq_zero.mp
    (abs_eq_zero.mp (le_antisymm le_zero (abs_nonneg _))))

private theorem support_of_bad_expect_zero {α : Type} [Finite α] (law : PMF α)
    (good : α → Prop) [DecidablePred good]
    (zero : expect law (fun a => if good a then (0 : ℝ) else 1) = 0) :
    ∀ a ∈ law.support, good a := by
  intro a supported
  by_contra bad
  have strict := expect_lt_of_mem_support
    (payoffIntegrable_of_finite law (fun _ => (0 : ℝ)))
    (payoffIntegrable_of_finite law (fun a => if good a then (0 : ℝ) else 1))
    (fun b _ => by split <;> norm_num) a supported (by simp [bad])
  rw [expect_constant, zero] at strict
  exact lt_irrefl (0 : ℝ) strict

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

local instance beliefFidelityHistoryFintype : Fintype
    ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon scheduler).History :=
  (bounds.onePacketMenu timeouts leaks).historyFintype (initialLaw setup) horizon scheduler

section Assembled

open Classical in
/-- The common native limit has exactly the supplied intended posterior after replay at every
debt-free forced own turn, including sites outside the equilibrium path. -/
theorem assembled_limit_belief_eq
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
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
    {who : Player} (site : (N).InformationSite who)
    (notFree : ¬ FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    (notOwing : ¬ OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup timeouts leaks who
      site.1)) :
    ((native.belief who site).map (replayProjection setup timeouts leaks bounds horizon scheduler
      (projectedSite setup timeouts leaks decision) site atSite rfl)) =
        intended.belief who (projectedSite setup timeouts leaks decision) := by
  let : Fintype (setup.intendedModel.InformationHistory who
      (projectedSite setup timeouts leaks decision).1) := Fintype.ofFinite _
  obtain ⟨error, errorConverges, errorBounds⟩ := source_belief_bounds_of_assembled setup timeouts
    leaks bounds horizon scheduler wellFormed independent observable sequence sourceMixed
    sourceBayes scale positive le_one scaleEq covers coversInputs capacity weights target assembled
    mixed bayes
  exact projected_belief_limit_eq _ (nativeConverges.belief who site)
    (fun h => (sourceConverges.belief who (projectedSite setup timeouts leaks decision) h).comp
      increasing.tendsto_atTop)
    (errorConverges.comp increasing.tendsto_atTop) (fun n => by
      simpa only [tsum_fintype, Function.comp_apply] using errorBounds (index n) who site notFree
        notOwing atSite turn
        decision)

open Classical in
/-- Every supported posterior history at a debt-free forced own turn has an actual successful
intended replay; the arbitrary branch of `replayProjection` receives no limiting belief mass. -/
theorem assembled_limit_belief_replay_exists
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
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler bounds.candidateCount p))
    (target : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence
      scale positive le_one weights target)
    (mixed : ∀ n, (target n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (target n)
      ((bounds.onePacketMenu timeouts leaks).decisionRecall
        (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    (native : (N).BehavioralAssessment)
    (index : ℕ → ℕ) (increasing : StrictMono index)
    (nativeConverges : BehavioralAssessmentConvergesPointwise (fun n => target (index n)) native)
    {who : Player} (site : (N).InformationSite who)
    (notFree : ¬ FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    (notOwing : ¬ OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event) :
    ∀ (history : (N).InformationHistory who site.1), history ∈ (native.belief who site).support →
      ∃ replay, intendedHistory? setup timeouts leaks bounds horizon scheduler history.1.trace =
        some replay := by
  let good := fun history : (N).InformationHistory who site.1 =>
    ∃ replay, intendedHistory? setup timeouts leaks bounds horizon scheduler history.1.trace =
      some replay
  let bad := fun history : (N).InformationHistory who site.1 =>
    if good history then (0 : ℝ) else 1
  have forced := forcedAgent_of_not_free setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler notFree
  have debtFree := siteDebtFree_of_not_owing setup timeouts leaks bounds horizon scheduler notOwing
  have regularGood (n : ℕ) (history : (N).InformationHistory who site.1)
      (regular : RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
        history.1.trace) : good history := by
    have own := ownCompletionsIntended_of_siteNotOwes (timeouts := timeouts) wellFormed debtFree
      history
    have inForced := forcedState_of_regular (timeouts := timeouts) wellFormed (sequence n) atSite
      forced history regular own
    obtain ⟨control, current, _⟩ := state_of_decision (timeouts := timeouts) history atSite
    exact intendedHistory?_isSome (sequence n) who history.1.trace control current
      (current ▸ inForced) regular own
  have inputs := OnePacketCounterpartInputs.ofBindingRepairs (timeouts := timeouts) wellFormed
    independent observable sourceMixed positive le_one scaleEq covers coversInputs capacity
    weights assembled mixed notFree notOwing atSite turn
  have irregularConverges := onePacket_irregularVanishes setup timeouts leaks bounds horizon
    scheduler mixed bayes inputs
  have badConverges : Tendsto (fun n => expect ((target n).belief who site) bad) atTop
      (nhds 0) := by
    refine squeeze_zero (fun n => expect_nonneg _ _ (fun history _ => by
      dsimp [bad]
      split <;> norm_num)) (fun n => ?_) irregularConverges
    refine expect_mono (fun history _ => ?_) (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)
    by_cases regular : RegularTrace setup timeouts leaks bounds horizon scheduler (sequence n) who
        history.1.trace
    · simp [bad, regularGood n history regular, regular]
    · dsimp [bad]
      simp only [regular, ↓reduceIte]
      split <;> norm_num
  have nativeBadConverges := (nativeConverges.belief who site).expect_finite bad
  have zero : expect (native.belief who site) bad = 0 :=
    tendsto_nhds_unique nativeBadConverges (badConverges.comp increasing.tendsto_atTop)
  exact support_of_bad_expect_zero _ good zero

open Classical in
/-- The limiting native posterior, replayed by the actual partial replay function, is exactly the
intended posterior on successful replays. In particular replay failure has zero posterior mass. -/
theorem assembled_limit_belief_replay_law
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (sourceBayes : ∀ n, BehavioralAssessment.IsBayesConsistent setup.intendedModel (sequence n)
      setup.intended_decision_antichain)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
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
    {who : Player} (site : (N).InformationSite who)
    (notFree : ¬ FreeAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    (notOwing : ¬ OwingAgent setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      ((N).agentAt site))
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView}
    (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (decision : setup.intendedModel.IsDecisionInfo who (projectView setup timeouts leaks who
      site.1)) :
    (native.belief who site).map (fun history =>
      intendedHistory? setup timeouts leaks bounds horizon scheduler history.1.trace) =
    (intended.belief who (projectedSite setup timeouts leaks decision)).map
      (fun history => some history.1) := by
  have beliefEq := assembled_limit_belief_eq setup timeouts leaks bounds horizon scheduler
    wellFormed independent observable sequence sourceMixed sourceBayes scale positive le_one
    scaleEq covers coversInputs capacity weights target assembled mixed bayes intended native
    sourceConverges index increasing nativeConverges site notFree notOwing atSite turn decision
  have replayExists := assembled_limit_belief_replay_exists setup timeouts leaks bounds horizon
    scheduler wellFormed independent observable sequence sourceMixed scale positive le_one scaleEq
    covers coversInputs capacity weights target assembled mixed bayes native index increasing
    nativeConverges site notFree notOwing atSite turn
  calc
    _ = ((native.belief who site).map
        (replayProjection setup timeouts leaks bounds horizon scheduler
          (projectedSite setup timeouts leaks decision) site atSite rfl)).map
        (fun history => some history.1) := by
      rw [PMF.map_comp]
      apply map_congr_on_support
      intro history supported
      obtain ⟨replay, replayed⟩ := replayExists history supported
      dsimp only [Function.comp_apply]
      rw [replayed, replayProjection_eq atSite rfl history replayed]
    _ = _ := congrArg (fun law => law.map (fun history => some history.1)) beliefEq

end Assembled

end Vegas
