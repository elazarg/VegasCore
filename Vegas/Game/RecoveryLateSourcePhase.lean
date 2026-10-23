/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryPendingFailure
import Vegas.Game.OnePacketSilentShape

/-! # Local late commitment completion under the recovery service -/

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

include initialized nativeLaw completes

omit [Fintype Player] in
/-- Actual recovery completion settles a native terminal whose configuration
still equals a fixed intended source prefix. -/
theorem recovery_terminal_completed_of_decodedIntended
    {rank : Nat} {sent : (graph setup).Config} (ordered : sent.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank sent = some point)
    (intended : ProtocolState.Intended setup.program point)
    (event : (graph setup).EventId) (final : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some final)) (ended : (application setup leaks).terminal (some final))
    (same : final.execution.application.config = sent) :
    event ∈ final.execution.application.config.cut.completed := by
  have finalDecoded : decodedPoint setup final.execution.application.config = some point := by
    rw [decodedPoint_eq_of_isPrefix (show
      final.execution.application.config.cut.IsPrefix rank by rw [same]; exact ordered), same]
    exact decoded
  have clear := publicExclusionRecord_of_decodedIntended trace finalDecoded intended
  rw [← nativeLaw] at trace
  have complete := Recovery.CompletesPlay.clear_native (runtime setup) leaks initialized completes
    final trace clear ended
  rw [complete]
  exact Finset.mem_univ _

section

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

open Classical in
theorem recovery_pending_completion_failure_split [Finite (E).History]
    (certificate : (E).WellFoundedHistories)
    (players : ∀ player, (N).BehavioralPolicy player)
    (start : (E).History) {control : (application setup leaks).Control}
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (clear : PublicExclusionRecord (RecoveryState.mk control.execution.application ∅))
    (key : LateKey setup leaks) (event : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready event)
    (decided : decidedEvent key = some event)
    (fresh : (application setup leaks).Control → Prop)
    (freshIff : ∀ next, fresh next ↔
      ¬ StoreEventFailed next.execution.application.config.store event) :
    let phase := (N).runBehavioralUntil certificate players
      (LateStopped setup leaks bounds horizon scheduler rank) start
    1 - expect phase (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) =
      expect phase (completionIndicator setup leaks bounds horizon scheduler rank fresh) +
      expect phase (lateBadStop setup leaks bounds horizon scheduler rank fresh event) := by
  intro phase
  have pointwise : ∀ final ∈ phase.support,
      1 - (if DecisionFailed key final.state then (1 : ℝ) else 0) =
        completionIndicator setup leaks bounds horizon scheduler rank fresh final +
          lateBadStop setup leaks bounds horizon scheduler rank fresh event final := by
    intro final supported
    obtain ⟨anchor, state, completed, _prefix, _seen⟩ :=
      recovery_pending_stop_completed initialized nativeLaw completes false
        certificate players start current ordered clear event ready final supported
    have failure : DecisionFailed key final.state ↔
        StoreEventFailed anchor.application.config.store event := by
      simp only [DecisionFailed, state, decided, completed, true_and]
    have bad : lateBadStop setup leaks bounds horizon scheduler rank fresh event final =
        if ¬ StoreEventFailed anchor.application.config.store event ∧
          completionPoint setup leaks bounds horizon scheduler rank fresh final = none
        then 1 else 0 := by
      have predicate : ((∃ control, final.state = some control ∧
          event ∈ control.execution.application.config.cut.completed ∧
          ¬ StoreEventFailed control.execution.application.config.store event) ∧
          completionPoint setup leaks bounds horizon scheduler rank fresh final = none) ↔
          (¬ StoreEventFailed anchor.application.config.store event ∧
          completionPoint setup leaks bounds horizon scheduler rank fresh final = none) := by
        constructor
        · rintro ⟨⟨control, controlState, _done, notFailed⟩, noPoint⟩
          rw [state] at controlState
          cases Option.some.inj controlState
          exact ⟨notFailed, noPoint⟩
        · rintro ⟨notFailed, noPoint⟩
          exact ⟨⟨_, state, completed, notFailed⟩, noPoint⟩
      simp only [lateBadStop, predicate]
    by_cases failed : StoreEventFailed anchor.application.config.store event
    · have absent := completionPoint_eq_none_of_not_fresh (rank := rank) (fresh := fresh) state
        (fun present => (freshIff _).mp present failed)
      simp only [failure.mpr failed, ↓reduceIte, completionIndicator, absent, Option.elim_none,
        bad, failed, not_true_eq_false, false_and]
      norm_num
    · rw [ite_eq_right (mt failure.mp failed), bad]
      cases pointEq : completionPoint setup leaks bounds horizon scheduler rank fresh final with
      | none => simp only [completionIndicator, pointEq, Option.elim_none, failed,
          not_false_eq_true, and_self, ↓reduceIte]; norm_num
      | some point => simp only [completionIndicator, pointEq, Option.elim_some, reduceCtorEq,
          and_false, ↓reduceIte]; norm_num
  have averaged := expect_congr_on_support pointwise
  rw [expect_sub (payoffIntegrable_constant phase 1) (payoffIntegrable_of_finite _ _),
    expect_constant, expect_add (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)] at averaged
  exact averaged

end

section

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

theorem recovery_certificate_lateSuccessFree
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] (sequence : ℕ →
  setup.intendedModel.BehavioralAssessment)
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
    (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.recall who,
      execution.observe (application setup leaks) who))
    (forced : ForcedState setup leaks who history.1.state)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (ordered : execution.application.config.cut.IsPrefix (siteRank site.1))
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank site.1) execution.application.config =
      some point)
    (intendedPoint : ProtocolState.Intended setup.program point) :
    ∀ (later : ((bounds.onePacketMenu (runtime setup) leaks).protocol
        (initialLaw setup) horizon scheduler).History) (laterRemaining : Nat)
        (reached : (application setup leaks).Execution),
      later.state = some ⟨laterRemaining, some who, reached⟩ →
      LateUnsent setup leaks who event execution.application.config (execution.recall who)
        later.state →
      (reached.recall who = execution.recall who →
        reached.observe (application setup leaks) who =
          execution.observe (application setup leaks) who) →
      (reached.recall who ≠ execution.recall who → ∃ response,
        execution.recall who ++ [respondEntry setup leaks execution who response] <+:
          reached.recall who) →
      ∀ slot < bounds.candidateCount,
        countPermits ((application setup leaks).outputs (reached.recall who))
          (slotEnvelope setup leaks who (reached.recall who)
            (reached.observe (application setup leaks) who) event slot) = true →
        ∃ factor : ℝ, ∀ choice ∈ (asIfHonestProfile setup leaks (sequence n) who
            (some (reached.recall who, reached.observe (application setup leaks) who))).support,
          ∀ next : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
              horizon scheduler).History,
            next.state = some ⟨laterRemaining, none, reached.respond (application setup leaks)
              who (slotResponse setup leaks who (reached.recall who)
                (reached.observe (application setup leaks) who) event slot choice)⟩ →
            |expect ((onePacketN).runBehavioralUntil
                ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
                  scheduler).wellFoundedHistories
                (Profile.update (sig := (onePacketN).behavioralSignature)
                  (targetSequence n).strategy who
                  (((targetSequence n).strategy who).withLaw site.1 law))
                (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) next)
                (completionIndicator setup leaks bounds horizon scheduler (siteRank site.1)
                  (siteFresh who site.1)) - factor| ≤
              (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3) := by
  exact certificate_lateSuccessFree setup leaks bounds horizon scheduler
    sequence scale scale_pos scale_le_one weights
    targetSequence assembled n covers capacity slotsLe site pendingSite debtFree siteKey pending law
    history current atSite forced node ordered decoded
    (recovery_terminal_completed_of_decodedIntended initialized nativeLaw completes ordered decoded
      intendedPoint event) intendedPoint

theorem recovery_pendingBinding_sourceKernel
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] (sequence : ℕ →
  setup.intendedModel.BehavioralAssessment)
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
    (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.recall who,
      execution.observe (application setup leaks) who))
    (forced : ForcedState setup leaks who history.1.state)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (ordered : execution.application.config.cut.IsPrefix (siteRank site.1))
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank site.1) execution.application.config =
      some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (lawShape : (∃ option : LateOption slots, law = onePacketLate setup leaks bounds horizon
        scheduler sequence scale scale_pos scale_le_one n ((onePacketN).agentAt site) option) ∨
      law = PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        site.1)) :
    let installed := Profile.update (sig := (onePacketN).behavioralSignature)
      (targetSequence n).strategy who (((targetSequence n).strategy who).withLaw site.1 law)
    let phase := (onePacketN).runBehavioralUntil
      ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
        scheduler).wellFoundedHistories installed
      (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) history.1
    CompletionPointLaw setup leaks bounds horizon scheduler installed (siteRank site.1)
      (siteFresh who site.1) history.1
      (expect phase (completionIndicator setup leaks bounds horizon scheduler (siteRank site.1)
        (siteFresh who site.1)))
      (ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile (sequence n).strategy) point)
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1)) ∧
    expect phase (lateBadStop setup leaks bounds horizon scheduler (siteRank site.1)
      (siteFresh who site.1) event) ≤ scale n ^ 3 * (2 * horizon + 1) := by
  intro installed phase
  have shape := certificate_firstActivation_lateOwnerShapeFrom setup leaks bounds horizon scheduler
    sequence scale scale_pos scale_le_one weights targetSequence assembled n site pending law
      lawShape
    history current atSite forced
  have terminalCompleted := recovery_terminal_completed_of_decodedIntended initialized nativeLaw
    completes ordered decoded intendedPoint event
  have freshIff : ∀ control, siteFresh who site.1 control ↔
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [siteFresh, pending]
  have pendingHere := pending
  rw [atSite] at pendingHere
  obtain ⟨turn, _, _, unrecorded⟩ := pendingEvent_spec pendingHere
  have factor := recovery_certificate_lateSuccessFree initialized nativeLaw completes sequence scale
    scale_pos scale_le_one weights targetSequence assembled n covers capacity slotsLe site
      pendingSite
    debtFree siteKey pending law history current atSite forced node ordered decoded intendedPoint
  constructor
  · exact lateBinding_completionPointLaw covers capacity (sequence n) (scale_pos n)
      (scale_le_one n) slotsLe installed history.1 current node turn unrecorded ordered decoded
      terminalCompleted intendedPoint (fun control failed fresh => (freshIff control).mp fresh
        failed)
      shape (by have := (scale_pos n).le; positivity) factor
  · exact lateBinding_badMass covers capacity (sequence n) (scale_pos n)
      (scale_le_one n) slotsLe installed history.1 current node turn unrecorded ordered decoded
      terminalCompleted intendedPoint freshIff shape


open Classical in
theorem recovery_pendingBinding_sourceValue
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] (sequence : ℕ →
  setup.intendedModel.BehavioralAssessment)
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
    (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.recall who,
      execution.observe (application setup leaks) who))
    (forced : ForcedState setup leaks who history.1.state)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (ordered : execution.application.config.cut.IsPrefix (siteRank site.1))
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank site.1) execution.application.config =
      some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (lawShape : (∃ option : LateOption slots, law = onePacketLate setup leaks bounds horizon
        scheduler sequence scale scale_pos scale_le_one n ((onePacketN).agentAt site) option) ∨
      law = PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        site.1))
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) {bound : ℝ}
    (readoutBounded : ∀ readout,
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
          sourcePointValue setup parameter utility excludedPayoff profile who point +
        expect phase (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) *
          excludedPayoff who)| ≤
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1) + scale n ^ 3 * (2 * horizon + 1)) * (2 * bound) := by
  intro profile installed phase
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let value := sourcePointValue setup parameter utility excludedPayoff profile who
  let center := excludedPayoff who
  let centered := fun target => value target - center
  let indicator := completionIndicator setup leaks bounds horizon scheduler (siteRank site.1)
    (siteFresh who site.1)
  let bad := lateBadStop setup leaks bounds horizon scheduler (siteRank site.1)
    (siteFresh who site.1) event
  let failure := fun final : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    if DecisionFailed key final.state then (1 : ℝ) else 0
  have boundNonneg : 0 ≤ bound := (abs_nonneg _).trans excludedBounded
  have valueBounded : ∀ target, |value target| ≤ bound := fun target =>
    expect_abs_le_of_bounded boundNonneg readoutBounded
  have centeredBounded : ∀ target, |centered target| ≤ 2 * bound := fun target => by
    calc |value target - center| ≤ |value target| + |center| := abs_sub _ _
      _ ≤ 2 * bound := by linarith [valueBounded target, excludedBounded]
  obtain ⟨kernel, badBound⟩ := recovery_pendingBinding_sourceKernel initialized nativeLaw completes
    sequence scale scale_pos scale_le_one weights targetSequence assembled n covers capacity slotsLe
    site pendingSite debtFree siteKey pending law history current atSite forced node ordered decoded
    intendedPoint lawShape
  have near := kernel centered (2 * bound) centeredBounded
  have centeredMean : expect (ProtocolState.behavioralStateStep setup.program profile point)
      centered = value point - center := by
    rw [show centered = fun target => value target - center from rfl,
      expect_sub (payoffIntegrable_of_bounded _ _ valueBounded) (payoffIntegrable_constant _
        center),
      expect_constant,
      expect_sourcePointValue_behavioralStateStep setup parameter utility excludedPayoff profile
        who readoutBounded point]
  rw [centeredMean] at near
  have rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler (current ▸ history.1.trace)
  have initialDecoded := (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have clear := publicExclusionRecord_of_decodedIntended rawTrace initialDecoded intendedPoint
  have pendingHere := pending
  rw [atSite] at pendingHere
  obtain ⟨turn, readyView, _, _⟩ := pendingEvent_spec pendingHere
  have ready := (execution.application.publicView_eventReady event).mp readyView
  have decided := decidedEvent_eq_of_pending setup leaks horizon scheduler pendingHere rawTrace rfl
    (by simpa only [atSite] using siteKey)
  have freshIff : ∀ control, siteFresh who site.1 control ↔
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [siteFresh, pending]
  have split := recovery_pending_completion_failure_split initialized nativeLaw completes
    certificate
    installed history.1 current ordered clear key event ready decided (siteFresh who site.1)
      freshIff
  have rewriteValue : expect phase (completionValue setup leaks bounds horizon scheduler parameter
      utility excludedPayoff profile (siteRank site.1) (siteFresh who site.1) who
      (fun _ => center)) = center + expect phase (fun stop =>
        (completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
          (siteFresh who site.1) stop).elim 0 centered) := by
    calc
      _ = expect phase (fun stop => center +
        (completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
          (siteFresh who site.1) stop).elim 0 centered) := by
        apply expect_congr_on_support
        intro stop supported
        obtain ⟨anchor, state, _completed, prefixed, _seen⟩ :=
          recovery_pending_stop_completed initialized nativeLaw completes false
            certificate installed history.1 current ordered clear event ready stop supported
        rw [completionValue_eq_elim setup leaks bounds horizon scheduler parameter utility
          excludedPayoff profile (siteRank site.1) (siteFresh who site.1) who (fun _ => center)
          ⟨_, state, prefixed⟩]
        cases completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
          (siteFresh who site.1) stop <;>
            simp only [Option.elim_none, Option.elim_some, centered] <;> ring
      _ = _ := by
        rw [expect_add (payoffIntegrable_constant _ center) (payoffIntegrable_of_finite _ _),
          expect_constant]
  have centeredNear : |expect phase (completionValue setup leaks bounds horizon scheduler parameter
      utility excludedPayoff profile (siteRank site.1) (siteFresh who site.1) who
      (fun _ => center)) - (center + expect phase indicator * (value point - center))| ≤
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
        (2 * horizon + 1)) * (2 * bound) := by
    rw [rewriteValue]
    simpa only [add_sub_add_left_eq_sub] using near
  have badNonneg : 0 ≤ expect phase bad := expect_nonneg _ _ fun stop _ => by
    simp only [bad, lateBadStop]
    split <;> norm_num
  have badGap : |expect phase bad * (value point - center)| ≤
      scale n ^ 3 * (2 * horizon + 1) * (2 * bound) := by
    rw [abs_mul, abs_of_nonneg badNonneg]
    exact mul_le_mul badBound (centeredBounded point) (abs_nonneg _) (by
      have := (scale_pos n).le
      positivity)
  have target : (1 - expect phase failure) * value point + expect phase failure * center =
      center + expect phase indicator * (value point - center) +
        expect phase bad * (value point - center) := by
    have mass : 1 - expect phase failure = expect phase indicator + expect phase bad := split
    calc (1 - expect phase failure) * value point + expect phase failure * center =
        (1 - expect phase failure) * (value point - center) + center := by ring
      _ = (expect phase indicator + expect phase bad) * (value point - center) + center := by
        rw [mass]
      _ = _ := by ring
  change |expect phase _ - ((1 - expect phase failure) * value point +
    expect phase failure * center)| ≤ _
  rw [target]
  calc _ ≤ |expect phase (completionValue setup leaks bounds horizon scheduler parameter utility
          excludedPayoff profile (siteRank site.1) (siteFresh who site.1) who
          (fun _ => center)) - (center + expect phase indicator * (value point - center))| +
        |expect phase bad * (value point - center)| := by
          convert abs_sub (expect phase (completionValue setup leaks bounds horizon scheduler
            parameter utility excludedPayoff profile (siteRank site.1) (siteFresh who site.1) who
            (fun _ => center)) - (center + expect phase indicator * (value point - center)))
            (expect phase bad * (value point - center)) using 1
          · congr 1
            ring
    _ ≤ _ := (add_le_add centeredNear badGap).trans (le_of_eq (by ring))


theorem recovery_committed_sourceKernel
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] [Finite ((bounds.onePacketMenu (runtime setup)
  leaks).protocol
      (initialLaw setup) horizon scheduler).History]
    (assessment : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralAssessment) {who : Player}
    (site : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InformationSite who)
    {key : LateKey setup leaks}
    {event : (graph setup).EventId} (_decided : decidedEvent key = some event)
    (pending : pendingEvent setup leaks who site.1 = some event)
    (choice : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).Choice who site.1) (response : (application setup leaks).Action)
    (selected : choice.1 = some response)
    (history : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.recall who,
      execution.observe (application setup leaks) who))
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (turn : execution.application.publicView.ownTurn? who = some event)
    (ordered : execution.application.config.cut.IsPrefix (siteRank site.1))
    {payload : L.Ty} (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {value : L.Val payload}
    (after : material.call.candidateAfter who
      (execution.observe (application setup leaks) who).application.candidates
      (.prepared serial) = .openable ⟨payload, value⟩)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank site.1) execution.application.config =
      some point)
    (pointIntended : ProtocolState.Intended setup.program point)
    (targetIntended : ∀ target ∈ (ProtocolState.step setup.program point
      (fun _ => sourceOfValue setup event outputEq value)).support,
      ProtocolState.Intended setup.program target) :
    let installed := Profile.update (sig := (onePacketN).behavioralSignature)
      assessment.strategy who
      ((assessment.strategy who).withLaw site.1 (PMF.pure choice))
    let phase := (onePacketN).runBehavioralUntil
      ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
        scheduler).wellFoundedHistories installed
      (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) history.1
    ∃ target, ProtocolState.step setup.program point
        (fun _ => sourceOfValue setup event outputEq value) = PMF.pure target ∧
      ProtocolState.Intended setup.program target ∧
      ∀ stop ∈ phase.support, ∃ final, stop.state = some final ∧
        (completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
            (siteFresh who site.1) stop = some target ∨
          (completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
              (siteFresh who site.1) stop = none ∧
            StoreEventFailed final.execution.application.config.store event)) := by
  intro installed phase
  classical
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
  have horizonBound := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := horizonBound.wellFoundedHistories
  have freshIff : ∀ control, siteFresh who site.1 control ↔
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [siteFresh, pending]
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  have traceHere : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.1.trace
  -- The committed action and the point it reaches.
  let committed : (graph setup).Action event :=
    cast (congrArg EventGraph.EventField.Action outputEq.symm) (PublicationResult.success value)
  have successful : (cast (congrArg EventGraph.EventField.Action outputEq) committed :
      PublicationResult (L.Val payload)) = .success value := by
    simp only [committed, cast_cast, cast_eq]
  have owned : (graph setup).actor? event = some who := nodeView_bind_actor outputEq codeEq
  have pointDecoded : decodedPoint setup execution.application.config = some point :=
    (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have acts : ∀ player, ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some who := fun player =>
    (decodedPoint_actor player ready pointDecoded).trans owned
  obtain ⟨target, stepEq⟩ := ProtocolState.step_eq_pure_of_actor who who setup.program point
    (fun _ => decodeEventAction setup.program event committed) (acts who)
  have intended := targetIntended target (by
    change target ∈ (ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event committed)).support
    rw [stepEq]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  obtain ⟨found, ⟨residualFound⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
    menu horizon scheduler traceHere _ rfl
  have foundEq : found = siteRank site.1 :=
    isPrefix_unique residualFound.checkpoint.ordered ordered
  have residual := foundEq ▸ residualFound
  -- The owner's first step performs the commitment.
  have notStopped : ¬ LateStopped setup leaks bounds horizon scheduler (siteRank site.1)
      history.1 := by
    rintro ⟨control, state, prefixed⟩
    rw [current] at state
    cases Option.some.inj state
    exact Nat.succ_ne_self _ (isPrefix_unique prefixed ordered)
  have running : ¬ (menu.protocol (initialLaw setup) horizon scheduler).terminal
      history.1.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have infoEq : model.infoOf who history.1.trace = site.1 := history.2
  have stepStates := menu.run_one_response (initialLaw setup) horizon scheduler installed
    history.1 who remaining execution current
  have responseLaw : (installed who (some (execution.recall who,
      execution.observe (application setup leaks) who))).map
        (fun choice => choice.1.getD ⟨none⟩) = PMF.pure response := by
    rw [← atSite]
    simp only [installed, Profile.update_same, BehavioralPolicy.withLaw_self, PMF.pure_map,
      selected, Option.getD_some]
  rw [decodeProfile_eq_map, responseLaw, PMF.pure_map] at stepStates
  have stops : ∀ stop ∈ (model.runBehavioralUntil certificate installed
      (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) history.1).support,
      ∃ final, stop.state = some final ∧
        (completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
            (siteFresh who site.1) stop = some target ∨
          (completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
              (siteFresh who site.1) stop = none ∧
            StoreEventFailed final.execution.application.config.store event)) := by
    intro stop stopMember
    rw [model.runBehavioralUntil_of_running certificate installed notStopped running,
      PMF.mem_support_bind_iff] at stopMember
    obtain ⟨next, nextMember, reached⟩ := stopMember
    have nextState : next.state = some ⟨remaining, none,
        execution.respond (application setup leaks) who response⟩ := by
      have inStates : next.state ∈ ((model.runBehavioralFrom installed 1 history.1).map
          History.state).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨next, nextMember, rfl⟩
      rw [stepStates, PMF.mem_support_pure_iff] at inStates
      exact inStates
    have afterTrace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩) :=
      nextState ▸ next.trace
    obtain ⟨acceptance, lookup⟩ := acceptanceInvariant_respond_commitment traceHere event turn
      outputEq response member material sends packet after afterTrace
    obtain ⟨_, records, emitted, _, _, stable, _⟩ := acceptance
    have invariant : OpenableCommitmentInvariant setup leaks bounds horizon scheduler who
        (respondEntry setup leaks execution who response)
        (sentEnvelope setup leaks execution who material) event (who, .prepared serial) outputEq
        value execution.application.config ready committed next.state := by
      rw [nextState]
      refine ⟨⟨afterTrace⟩, records, emitted, rfl, packet, lookup, stable, fun done => ?_⟩
      exact ((ready.1 (by
        rw [← ((runtime setup).reactive_respond_application leaks execution who response).1]
        exact done))).elim
    obtain ⟨final, finalState, stepped⟩ := openableCommitment_stop bounds
      horizon scheduler certificate installed codeEq successful ordered
      (recovery_terminal_completed_of_decodedIntended initialized nativeLaw completes ordered
        decoded
        pointIntended event) next invariant stop reached
    refine ⟨final, finalState, ?_⟩
    rcases stepped with inStep | ⟨failing, failed, inStep⟩
    · have pointEq := completionPoint_of_mem_step (fresh := siteFresh who site.1) residual
        decoded ready stepEq finalState inStep
      by_cases freshHere : siteFresh who site.1 final
      · left
        rw [pointEq, ite_eq_left ⟨intended, freshHere⟩ ..]
      · right
        exact ⟨by rw [pointEq, ite_eq_right (fun good => freshHere good.2) ..],
          not_not.mp ((not_congr (freshIff final)).mp freshHere)⟩
    · right
      have output := step_binding_output (outputEq := outputEq) (codeEq := codeEq) inStep
      have failedHere : StoreEventFailed final.execution.application.config.store event :=
        ⟨_, by rw [EventGraph.Config.store_output, output],
          (isFailure_cast_binding_iff outputEq _).mpr failed⟩
      exact ⟨completionPoint_eq_none_of_not_fresh finalState fun freshHere =>
        (freshIff final).mp freshHere failedHere, failedHere⟩
  refine ⟨target, ?_, intended, stops⟩
  exact stepEq


open Classical in
theorem recovery_committed_sourceValue
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)] [Finite ((bounds.onePacketMenu (runtime setup)
  leaks).protocol
      (initialLaw setup) horizon scheduler).History]
    (assessment : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralAssessment) {who : Player}
    (site : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InformationSite who)
    {key : LateKey setup leaks}
    {event : (graph setup).EventId} (decided : decidedEvent key = some event)
    (pending : pendingEvent setup leaks who site.1 = some event)
    (choice : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).Choice who site.1) (response : (application setup leaks).Action)
    (selected : choice.1 = some response)
    (history : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.recall who,
      execution.observe (application setup leaks) who))
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (turn : execution.application.publicView.ownTurn? who = some event)
    (ordered : execution.application.config.cut.IsPrefix (siteRank site.1))
    {payload : L.Ty} (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {value : L.Val payload}
    (after : material.call.candidateAfter who
      (execution.observe (application setup leaks) who).application.candidates
      (.prepared serial) = .openable ⟨payload, value⟩)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank site.1) execution.application.config =
      some point)
    (pointIntended : ProtocolState.Intended setup.program point)
    (targetIntended : ∀ target ∈ (ProtocolState.step setup.program point
      (fun _ => sourceOfValue setup event outputEq value)).support,
      ProtocolState.Intended setup.program target)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (profile : BehavioralProfile setup.program) :
    let installed := Profile.update (sig := (onePacketN).behavioralSignature)
      assessment.strategy who
      ((assessment.strategy who).withLaw site.1 (PMF.pure choice))
    let phase := (onePacketN).runBehavioralUntil
      ((bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup) horizon
        scheduler).wellFoundedHistories installed
      (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) history.1
    expect phase (completionValue setup leaks bounds horizon scheduler parameter utility
      excludedPayoff profile (siteRank site.1) (siteFresh who site.1) who
      (fun _ => excludedPayoff who)) =
      (1 - expect phase (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0)) *
        expect (ProtocolState.step setup.program point
          (fun _ => sourceOfValue setup event outputEq value))
          (sourcePointValue setup parameter utility excludedPayoff profile who) +
      expect phase (fun final => if DecisionFailed key final.state then (1 : ℝ) else 0) *
        excludedPayoff who := by
  intro installed phase
  obtain ⟨target, stepEq, intended, stops⟩ := recovery_committed_sourceKernel initialized nativeLaw
    completes assessment site decided pending choice response selected history current atSite member
    material sends packet turn ordered outputEq codeEq after decoded pointIntended targetIntended
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  let targetValue := sourcePointValue setup parameter utility excludedPayoff profile who target
  let failure := fun final : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    if DecisionFailed key final.state then (1 : ℝ) else 0
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  have trace := menu.toRawTrace (initialLaw setup) horizon scheduler (current ▸ history.1.trace)
  have clear := publicExclusionRecord_of_decodedIntended trace
    ((decodedPoint_eq_of_isPrefix ordered).trans decoded) pointIntended
  have freshIff : ∀ control, siteFresh who site.1 control ↔
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [siteFresh, pending]
  have pointwise : ∀ final ∈ phase.support,
      completionValue setup leaks bounds horizon scheduler parameter utility excludedPayoff profile
          (siteRank site.1) (siteFresh who site.1) who (fun _ => excludedPayoff who) final =
        (1 - failure final) * targetValue + failure final * excludedPayoff who := by
    intro final supported
    obtain ⟨anchor, state, completed, prefixed, _seen⟩ :=
      recovery_pending_stop_completed initialized nativeLaw completes false
        certificate installed history.1 current ordered clear event ready final supported
    rw [completionValue_eq_elim setup leaks bounds horizon scheduler parameter utility
      excludedPayoff
      profile (siteRank site.1) (siteFresh who site.1) who (fun _ => excludedPayoff who)
      ⟨_, state, prefixed⟩]
    obtain ⟨other, otherState, cases⟩ := stops final supported
    have same : other = ⟨horizon - anchor.environmentRecall.length, none, anchor⟩ :=
      Option.some.inj (otherState.symm.trans state)
    subst other
    rcases cases with pointEq | ⟨pointEq, failed⟩
    · have good : ¬ DecisionFailed key final.state := by
        intro failed
        have stored : StoreEventFailed anchor.application.config.store event := by
          simpa only [DecisionFailed, state, decided, completed, true_and] using failed
        have absent := completionPoint_eq_none_of_not_fresh (rank := siteRank site.1)
          (fresh := siteFresh who site.1) state
          (fun fresh => (freshIff _).mp fresh stored)
        rw [pointEq] at absent
        cases absent
      simp only [pointEq, Option.elim_some, failure, good, ↓reduceIte, sub_zero, one_mul,
        zero_mul, add_zero, targetValue]
    · have failedHere : DecisionFailed key final.state := by
        simpa only [DecisionFailed, state, decided, completed, true_and] using failed
      simp only [pointEq, Option.elim_none, failure, failedHere, ↓reduceIte, sub_self, zero_mul,
        one_mul, zero_add]
  rw [stepEq, expect_pure, expect_congr_on_support pointwise,
    expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    expect_mul_const, expect_mul_const,
    expect_sub (payoffIntegrable_constant _ 1) (payoffIntegrable_of_finite _ _), expect_constant]



theorem recovery_unintendedCommitment_phase_owes (profile : BehavioralProfile setup.program)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    {event : (graph setup).EventId}
    (turn : execution.application.publicView.ownTurn? who = some event) {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {point : ProtocolState setup.program}
    (decoded : decodedPoint setup execution.application.config = some point)
    (pointIntended : ProtocolState.Intended setup.program point)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    (response : (application setup leaks).Action) (material : (application setup leaks).Submission)
    (submits : response.transmission = some material) {candidate : Handle (graph setup)}
    (call : (sentEnvelope setup leaks execution who material).payload.call =
      .commitment event candidate)
    (fixed : (execution.respond (application setup leaks) who
      response).application.candidates.lookup candidate ≠ .fresh)
    (unintended : ∀ value act, (execution.respond (application setup leaks) who
        response).application.candidates.lookup candidate = .openable ⟨payload, value⟩ →
      decodeEventAction setup.program event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (PublicationResult.success value)) = some act →
      act ∉ ProtocolView.intendedAvailable who setup.program
        (ProtocolState.observe who setup.program point))
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (current : history.state = some ⟨remaining, none,
      execution.respond (application setup leaks) who response⟩) :
    ∀ final ∈ ((onePacketN).runBehavioralUntil certificate players
        (LateStopped setup leaks bounds horizon scheduler rank) history).support,
      DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program) final.state
        := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  have afterTrace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩) :=
    current ▸ history.trace
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  have sameConfig := ((runtime setup).reactive_respond_application leaks execution who response).1
  have start : UnintendedCommitmentInvariant setup leaks bounds horizon scheduler profile who
      (respondEntry setup leaks execution who response)
      (sentEnvelope setup leaks execution who material) event candidate outputEq
      execution.application.config point history.state := by
    rw [current]
    refine ⟨⟨afterTrace⟩, recordsEntry_respond execution who response remaining none,
      by rw [respondEntry_of_transmission execution who response material submits], rfl, call,
      fixed, unintended, fun _ => sameConfig, fun done => ?_⟩
    rw [sameConfig] at done
    exact (ready.1 done).elim
  have clear := publicExclusionRecord_of_decodedIntended
    (menu.toRawTrace (initialLaw setup) horizon scheduler afterTrace)
    (show decodedPoint setup
      (execution.respond (application setup leaks) who response).application.config = some point by
      rw [sameConfig]; exact decoded) pointIntended
  have initialOrdered :
      (execution.respond (application setup leaks) who response).application.config.cut.IsPrefix
        rank :=
    by rw [sameConfig]; exact ordered
  have initialReady :
      (execution.respond (application setup leaks) who response).application.config.cut.Ready
        event :=
    by rw [sameConfig]; exact ready
  intro final supported
  have reachedInvariant := model.runBehavioralUntil_support_closed certificate players
    (LateStopped setup leaks bounds horizon scheduler rank) _
    (fun state joint legal target holds reached =>
      unintendedCommitmentInvariant_transition bounds horizon scheduler profile codeEq decoded
        (ProtocolState.intendedFor_of_intended who setup.program point pointIntended) ready
        state target joint legal holds reached) history start final supported
  obtain ⟨anchor, state, completed, _prefix, _seen⟩ :=
    recovery_pending_stop_completed initialized nativeLaw completes false
      certificate
      players history current initialOrdered clear event initialReady final supported
  rw [state] at reachedInvariant
  have debt := reachedInvariant.2.2.2.2.2.2.2.2 completed
  simpa only [state] using debt

end

end Vegas
