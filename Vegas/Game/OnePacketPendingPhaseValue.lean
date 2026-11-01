/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketPhasePotential
import Vegas.Game.OnePacketSourcePhase
import Vegas.Game.OnePacketBeliefWiring
import Vegas.Game.OnePacketLateCertificate
import Vegas.Game.OnePacketLateDecomposition

/-! # Source potentials at completed native phases -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

local notation "onePacketN" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  scheduler

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- Forced pending-event source potentials need only counted clear terminal completion. -/
theorem pending_phase_value_bounds
    [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)]
    [Finite ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (terminalCompletes : ∀ (final : (application setup runtime leaks).Control),
      ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      final.execution.application.config.defaulted = ∅ →
      (application setup runtime leaks).terminal (some final) →
      final.execution.application.config.cut.Terminal)
    (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      scale_pos
      scale_le_one weights targetSequence) (n : ℕ)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount) {who : Player}
    (site : (onePacketN).InformationSite who)
    (pendingSite : LateDelivery setup runtime leaks who site.1 ∨ FirstActivation setup runtime
      leaks who site.1)
    (debtFree : SiteDebtFree setup runtime leaks bounds horizon scheduler site)
    {key : LateKey setup runtime leaks} (siteKey : lateKey setup runtime leaks who site.1 = some
      key)
    {event : (graph setup).EventId} (pending : pendingEvent setup runtime leaks who site.1 = some
      event)
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    (forced : ForcedState setup runtime leaks who history.1.state)
    (lawShape : (∃ option : LateOption slots,
      law = onePacketLate setup runtime leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n ((onePacketN).agentAt site) option) ∨
      law = PMF.pure (silenceChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler
        who site.1))
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound) :
    let profile := setup.intendedOpeningProfile (sequence n).strategy
    let installed := Profile.update (sig := (onePacketN).behavioralSignature)
      (targetSequence n).strategy who (((targetSequence n).strategy who).withLaw site.1 law)
    let phase := (onePacketN).runBehavioralUntil
      ((bounds.onePacketMenu runtime leaks).bounded (initialLaw setup) horizon
        scheduler).wellFoundedHistories installed
      (LateStopped setup runtime leaks bounds horizon scheduler (siteRank (runtime := runtime)
        site.1)) history.1
    |expect phase (completionValue setup runtime leaks bounds horizon scheduler parameter utility
        excludedPayoff profile (siteRank (runtime := runtime) site.1) (siteFresh (runtime :=
          runtime) who site.1) who
        (fun _ => excludedPayoff who)) -
      ((1 - expect phase (fun final => if DecisionFailed (runtime := runtime) key final.state then
        (1 : ℝ) else 0)) *
        decodedPointValue setup runtime leaks bounds horizon scheduler parameter utility
          excludedPayoff
          profile who (siteRank (runtime := runtime) site.1) history.1 +
        expect phase (fun final => if DecisionFailed (runtime := runtime) key final.state then (1
          : ℝ) else 0) *
          excludedPayoff who)| ≤
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
          (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * bound) ∧
      expect phase (lateBadStop setup runtime leaks bounds horizon scheduler (siteRank (runtime :=
        runtime) site.1)
        (siteFresh (runtime := runtime) who site.1) event) ≤ scale n ^ 3 * (2 * horizon + 1) := by
  intro profile installed phase
  have errorNonneg : 0 ≤
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
          (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * bound) := by
    have := (scale_pos n).le
    have := (abs_nonneg _).trans excludedBounded
    positivity
  obtain ⟨remaining, execution, current, recallEq, observeEq⟩ :=
    state_of_site setup runtime leaks bounds horizon scheduler atSite history
  let menu := bounds.onePacketMenu runtime leaks
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.1.trace
  obtain ⟨found, foundOrdered, _⟩ := pendingAt_history (runtime := runtime)
    (menu.toRawTrace (initialLaw setup) horizon scheduler trace)
  have rankEq : siteRank (runtime := runtime) site.1 = found := by
    rw [atSite, ← observeEq]
    change (execution.application.config.history.map EventCompletion.event).length = found
    rw [List.length_map]
    exact history_length_of_isPrefix _ foundOrdered
  have ordered : execution.application.config.cut.IsPrefix
      (siteRank (runtime := runtime) site.1) := rankEq.symm ▸ foundOrdered
  subst recallEq
  subst observeEq
  have pendingAt := pending
  rw [atSite] at pendingAt
  obtain ⟨turn, readyView, owned, _⟩ := pendingEvent_spec (runtime := runtime) pendingAt
  have turnExecution : execution.application.publicView.ownTurn? who = some event := turn
  have ready := (execution.application.publicView_eventReady event).mp readyView
  obtain ⟨point, decoded, intendedPoint, reachedPoint⟩ := intendedReached_of_forced_debtFree
    (runtime := runtime)
    wellFormed site debtFree history current ordered forced
  have terminalCompleted := terminal_completed_of_decodedIntended terminalCompletes ordered decoded
    intendedPoint event
  have valueEq : decodedPointValue setup runtime leaks bounds horizon scheduler parameter utility
      excludedPayoff profile who (siteRank (runtime := runtime) site.1) history.1 =
      sourcePointValue setup parameter utility excludedPayoff profile who point := by
    unfold decodedPointValue
    rw [current]
    dsimp only
    rw [decoded]
    dsimp only
    rw [ite_eq_left reachedPoint ..]
  rw [valueEq]
  cases node : nodeView (graph setup) event with
  | bind owner payload outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst owner
      constructor
      · exact pendingBinding_sourceValue (runtime := runtime) terminalCompletes sequence scale
          scale_pos scale_le_one weights targetSequence assembled n covers capacity slotsLe site
          pendingSite debtFree siteKey pending law history current atSite forced node ordered
            decoded
          intendedPoint lawShape parameter utility excludedPayoff readoutBounded excludedBounded
      · exact (pendingBinding_sourceKernel (runtime := runtime) sequence scale
          scale_pos scale_le_one weights targetSequence assembled n covers capacity slotsLe site
          pendingSite debtFree siteKey pending law history current atSite forced node ordered
            decoded
          intendedPoint
          terminalCompleted lawShape).2
  | resolve owner payload binding checks outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst owner
      have decided : decidedEvent (runtime := runtime) key = some event := by
        have siteKeyHere := siteKey
        rw [atSite] at siteKeyHere
        simp only [lateKey, Option.some.injEq] at siteKeyHere
        subst siteKeyHere
        unfold decidedEvent
        rw [turnEvent_of_publicationTurn (runtime := runtime)
          ⟨turn, payload, binding, checks, outputEq, codeEq, node⟩]
      have exactValue := disclosure_sourceValue setup runtime leaks bounds horizon scheduler
        terminalCompletes
        (sequence n)
        (targetSequence n) site pending law history current turnExecution ordered outputEq codeEq
        decoded intendedPoint decided parameter utility excludedPayoff readoutBounded
      constructor
      · rw [exactValue, sub_self, abs_zero]
        exact errorNonneg
      obtain ⟨target, _step, _targetIntended, stops⟩ := disclosure_sourceKernel (runtime := runtime)
        (sequence n) (targetSequence n) site pending law history current turnExecution ordered
        outputEq codeEq decoded intendedPoint
        terminalCompleted
      have zero : expect phase (lateBadStop setup runtime leaks bounds horizon scheduler (siteRank
        (runtime := runtime) site.1)
          (siteFresh (runtime := runtime) who site.1) event) = 0 := by
        calc
          _ = expect phase (fun _ => (0 : ℝ)) := by
            apply expect_congr_on_support
            intro stop supported
            obtain ⟨final, state, alternatives⟩ := stops stop supported
            unfold lateBadStop
            split_ifs with bad
            · obtain ⟨⟨control, controlState, _completed, notFailed⟩, absent⟩ := bad
              rw [state] at controlState
              cases Option.some.inj controlState
              rcases alternatives with somePoint | ⟨_none, failed⟩
              · rw [somePoint] at absent
                cases absent
              · exact (notFailed failed).elim
            · rfl
          _ = 0 := expect_constant _ _
      rw [zero]
      have := (scale_pos n).le
      positivity
  | sample payload distribution outputEq codeEq =>
      rw [nodeView_sample_actor outputEq codeEq] at owned
      cases owned


end Vegas
