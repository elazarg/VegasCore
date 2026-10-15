/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryPhasePotential
import Vegas.Game.OnePacketLateValueBlind
import Vegas.Game.RecoveryEventPhaseLaw

/-! # Source potentials at completed recovery phases -/

noncomputable section
namespace Vegas
open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {recoveryScheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)
local notation "scheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks)
  (initialLaw setup) horizon scheduler
local notation "onePacketN" => onePacketModel setup leaks bounds (initialLaw setup) horizon
  scheduler
include initialized nativeLaw completes

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- Evaluating the primitive pending-event failure at the finite horizon or at
its next completion gives the same probability under the actual recovery service. -/
theorem recovery_pending_failure_run_eq_phase [Finite (E).History]
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (onePacketN).BehavioralPolicy player)
    (start : (E).History) {control : (application setup leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : PublicExclusionRecord (RecoveryState.mk control.execution.application ∅))
    (key : LateKey setup leaks) (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (decided : decidedEvent key = some event) :
    expect ((onePacketN).runBehavioralFrom players (2 * horizon + 1) start)
        (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) =
      expect ((onePacketN).runBehavioralUntil certificate players
        (LateStopped setup leaks bounds horizon scheduler rank) start)
        (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) := by
  rw [← (onePacketN).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
    ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon scheduler),
    recovery_pending_failure_terminal_eq_stopped initialized nativeLaw completes certificate
      players start current ordered clear key event ready decided,
    ← recovery_pending_until_eq_clearUntil initialized nativeLaw completes certificate
      players start current ordered clear event ready]

omit initialized nativeLaw completes in
/-- A forced history whose observer owes no failure decodes to a point reached
by the intended source game. -/
theorem intendedReached_of_forced_debtFree (wellFormed : setup.WellFormed) {who : Player}
    (site : (onePacketN).InformationSite who)
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site)
    (history : (onePacketN).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (ordered : execution.application.config.cut.IsPrefix (siteRank site.1))
    (forced : ForcedState setup leaks who history.1.state) :
    ∃ point, sourceServicePrefix? setup (siteRank site.1) execution.application.config =
      some point ∧ ProtocolState.Intended setup.program point ∧ IntendedReached setup point := by
  classical
  let menu := bounds.onePacketMenu (runtime setup) leaks
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.1.trace
  obtain ⟨decodedRank, ⟨residual⟩, holds⟩ := decodedState_intended_or_owes wellFormed
    (failureProfile setup.program) menu horizon scheduler trace _ rfl
  have sameRank := isPrefix_unique residual.checkpoint.ordered ordered
  subst sameRank
  have decoded := residual.decode
  generalize residual.lift (ProtocolState.entry residual.program residual.source) = point
    at decoded
  have pointDecoded : decodedPoint setup execution.application.config = some point :=
    (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have forcedHere := forced
  rw [current] at forcedHere
  obtain ⟨forcedFound, forcedDecoded, forcedHolds⟩ :=
    (forcedState_iff_decodedPoint _).mp forcedHere
  rw [pointDecoded, Option.some.injEq] at forcedDecoded
  subst forcedDecoded
  have free : ∀ found, decodedPoint setup execution.application.config = some found →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program found := by
    intro found foundDecoded player
    rw [pointDecoded, Option.some.injEq] at foundDecoded
    subst foundDecoded
    by_cases same : player = who
    · subst same
      exact debtFree history point (by rw [current]; exact pointDecoded)
    · exact (forcedHolds.2 player same).2
  have intendedPoint : ProtocolState.Intended setup.program point := by
    rcases holds point decoded with intendedHere | ⟨player, owed⟩
    · exact intendedHere
    · exact (free point pointDecoded player owed).elim
  obtain ⟨replay, replayed⟩ := intendedHistory?_isSome_of_debtFree wellFormed trace _ rfl free
  have reachedPoint : IntendedReached setup point :=
    ⟨replay, (intendedHistory?_state trace replayed).trans pointDecoded⟩
  exact ⟨point, decoded, intendedPoint, reachedPoint⟩

open Classical in
theorem recovery_pending_phase_value_bounds
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)]
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount) {who : Player}
    (site : (onePacketN).InformationSite who)
    (pendingSite : LateDelivery setup leaks who site.1 ∨ FirstActivation setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    (forced : ForcedState setup leaks who history.1.state)
    (lawShape : (∃ option : LateOption slots,
      law = onePacketLate setup leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one n ((onePacketN).agentAt site) option) ∨
      law = PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler
        who site.1))
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound)
    (excludedBounded : |excludedPayoff who| ≤ bound) :
    let profile := setup.intendedOpeningProfile (sequence n).strategy
    let installed := Profile.update (sig := (onePacketN).behavioralSignature)
      (targetSequence n).strategy who (((targetSequence n).strategy who).withLaw site.1 law)
    let phase := (onePacketN).runBehavioralUntil
      ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
        scheduler).wellFoundedHistories installed
      (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) history.1
    |expect phase (completionValue setup leaks bounds horizon scheduler parameter utility
        excludedPayoff profile (siteRank site.1) (siteFresh who site.1) who
        (fun _ => excludedPayoff who)) -
      ((1 - expect phase (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0)) *
        decodedPointValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          profile who (siteRank site.1) history.1 +
        expect phase (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) *
          excludedPayoff who)| ≤
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
          (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * bound) ∧
      expect phase (lateBadStop setup leaks bounds horizon scheduler (siteRank site.1)
        (siteFresh who site.1) event) ≤ scale n ^ 3 * (2 * horizon + 1) := by
  intro profile installed phase
  have errorNonneg : 0 ≤
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
          (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * bound) := by
    have := (scale_pos n).le
    have := (abs_nonneg _).trans excludedBounded
    positivity
  obtain ⟨remaining, execution, current, recallEq, observeEq, ordered⟩ :=
    ordered_of_site setup leaks bounds horizon scheduler atSite history
  subst recallEq
  subst observeEq
  let menu := bounds.onePacketMenu (runtime setup) leaks
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.1.trace
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    menu.toRawTrace (initialLaw setup) horizon scheduler trace
  have pendingAt := pending
  rw [atSite] at pendingAt
  obtain ⟨turn, readyView, owned, _⟩ := pendingEvent_spec pendingAt
  have turnExecution : execution.application.publicView.ownTurn? who = some event := turn
  have ready := (execution.application.publicView_eventReady event).mp readyView
  have siteKeyHere := siteKey
  rw [atSite] at siteKeyHere
  have decided := decidedEvent_eq_of_pending setup leaks horizon scheduler pendingAt rawTrace rfl
    siteKeyHere
  obtain ⟨point, decoded, intendedPoint, reachedPoint⟩ := intendedReached_of_forced_debtFree
    wellFormed site debtFree history current ordered forced
  have valueEq : decodedPointValue setup leaks bounds horizon scheduler parameter utility
      excludedPayoff profile who (siteRank site.1) history.1 =
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
      · exact recovery_pendingBinding_sourceValue initialized nativeLaw completes sequence scale
          scale_pos scale_le_one weights targetSequence assembled n covers capacity slotsLe site
          pendingSite debtFree siteKey pending law history current atSite forced node ordered
            decoded
          intendedPoint lawShape parameter utility excludedPayoff readoutBounded excludedBounded
      · exact (recovery_pendingBinding_sourceKernel initialized nativeLaw completes sequence scale
          scale_pos scale_le_one weights targetSequence assembled n covers capacity slotsLe site
          pendingSite debtFree siteKey pending law history current atSite forced node ordered
            decoded
          intendedPoint lawShape).2
  | resolve owner payload binding checks outputEq codeEq =>
      have ownerEq : owner = who :=
        Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
      subst owner
      have exactValue := recovery_disclosure_sourceValue initialized nativeLaw completes
        (sequence n)
        (targetSequence n) site pending law history current turnExecution ordered outputEq codeEq
        decoded intendedPoint decided parameter utility excludedPayoff readoutBounded
      constructor
      · rw [exactValue, sub_self, abs_zero]
        exact errorNonneg
      obtain ⟨target, _step, _targetIntended, stops⟩ := disclosure_sourceKernel
        (sequence n) (targetSequence n) site pending law history current turnExecution ordered
        outputEq codeEq decoded intendedPoint
        (recovery_terminal_completed_of_decodedIntended initialized nativeLaw completes ordered
          decoded intendedPoint event)
      have zero : expect phase (lateBadStop setup leaks bounds horizon scheduler (siteRank site.1)
          (siteFresh who site.1) event) = 0 := by
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
