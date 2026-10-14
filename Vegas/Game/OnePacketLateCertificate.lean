/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateHistoryNear

/-! # The certificate's late bindings

At a late delivery of a binding, a profile assembled from the certificate's
components with a late option or silence installed at the site plays the late
owner shape (`Vegas.certificate_lateOwnerShape`): at the site the installed
law, and later the late component of the key's weights while the owner has
sent nothing. The relevant-site lumping of the certificate makes success after
a commitment value-free (`Vegas.certificate_lateSuccessFree`), so the
completion value from each forced history of the site whose decoded point the
intended game reaches is one less its failure probability times its
continuation value, up to a multiple of the cube of the scale
(`Vegas.certificate_lateBinding_historyNear`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- At a history of a decision site of `who`, the state is a decision of `who`
whose recall and view are the site's. -/
theorem state_of_site {who : Player} {site : (onePacketN).InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    (history : (onePacketN).InformationHistory who site.1) :
    ∃ remaining execution, history.1.state = some ⟨remaining, some who, execution⟩ ∧
      execution.recall who = past ∧ execution.observe (application setup leaks) who = view := by
  obtain ⟨fullHistory, infoEq⟩ := history
  have observed : (application setup leaks).observe who fullHistory.state = some (past, view) :=
    ((bounds.onePacketMenu (runtime setup) leaks).info (initialLaw setup) horizon scheduler who
      fullHistory.trace).symm.trans (infoEq.trans atSite)
  cases state : fullHistory.state with
  | none =>
      rw [state] at observed
      cases observed
  | some control =>
      rw [state] at observed
      rcases control with ⟨remaining, actor, execution⟩
      unfold ReactiveApplication.observe at observed
      by_cases acting : actor = some who
      · subst acting
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at observed
        exact ⟨remaining, execution, rfl, observed.1, observed.2⟩
      · simp only [acting, ↓reduceIte] at observed
        cases observed

/-- **The certificate's late owner shape.** At a late delivery of `who` for its
pending `event`, from a forced history of the site, the profile assembled from
the certificate's components with a late option or silence installed at the
site plays the late owner shape. -/
theorem certificate_lateOwnerShape (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ) {who : Player}
    (site : (onePacketN).InformationSite who) (late : LateDelivery setup leaks who site.1)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    (law : PMF ((onePacketN).Choice who site.1))
    (lawShape : (∃ option : LateOption slots, law = onePacketLate setup leaks bounds horizon
        scheduler sequence scale scale_pos scale_le_one n ((onePacketN).agentAt site) option) ∨
      law = PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        site.1))
    (history : (onePacketN).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.recall who,
      execution.observe (application setup leaks) who))
    (forced : ForcedState setup leaks who history.1.state) :
    LateOwnerShape setup leaks bounds horizon scheduler (sequence n) (scale_pos n).le
      (scale_le_one n) slots
      (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
        (((targetSequence n).strategy who).withLaw site.1 law)) who event
      execution.application.config (execution.recall who) := by
  intro later laterRemaining reached state holds
  obtain ⟨atSent, extends_, unrecordedHere⟩ := (by simpa only [state] using holds :
    LateUnsent setup leaks who event execution.application.config (execution.recall who)
      (some ⟨laterRemaining, some who, reached⟩))
  rw [Profile.update_same]
  by_cases same : (some (reached.recall who, reached.observe (application setup leaks) who) :
      (application setup leaks).Info) = site.1
  · -- At the site, the installed law.
    obtain ⟨siteInfo, decision⟩ := site
    change _ = siteInfo at same
    subst same
    rw [BehavioralPolicy.withLaw_self]
    rcases lawShape with ⟨option, lawEq⟩ | lawEq
    · left
      refine ⟨PMF.pure option, ?_⟩
      rw [lawEq, PMF.pure_bind]
      rfl
    · right
      exact lawEq
  · -- Later, the late component of the key's weights.
    rw [BehavioralPolicy.withLaw_of_ne _ _ _ same]
    left
    have forcedHere : ForcedState setup leaks who later.state := by
      rw [current] at forced
      obtain ⟨forcedRank, forcedPoint, forcedOrdered, forcedDecoded, forcedHolds⟩ := forced
      rw [state]
      exact ⟨forcedRank, forcedPoint, by rw [atSent]; exact forcedOrdered,
        by rw [atSent]; exact forcedDecoded, forcedHolds⟩
    obtain ⟨past, view, lateEvent, lateAt, latePending, entry, member, activatedAt⟩ := late
    rw [lateAt] at latePending
    rw [atSite] at lateAt
    cases Option.some.inj lateAt
    rw [atSite] at pending
    cases Option.some.inj (latePending.symm.trans pending)
    obtain ⟨turn, readyView, _, _⟩ := pendingEvent_spec pending
    have ready : reached.application.config.cut.Ready event := by
      rw [atSent]
      exact (execution.application.publicView_eventReady event).mp readyView
    have activated : ∃ entry ∈ reached.recall who, ActivatedAt setup leaks who event entry :=
      ⟨entry, extends_.subset member, activatedAt⟩
    exact ⟨_, (certificate_strategyShape setup leaks bounds horizon scheduler sequence scale
      scale_pos scale_le_one weights targetSequence assembled n who later laterRemaining reached
      event state forcedHere ready activated).1 unrecordedHere⟩

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler] in
/-- The key of a late delivery of a binding with nothing sent decides that
binding: it is no publication turn, its binding turn is the event, and its
decided event is the event. -/
theorem lateKey_decides_binding {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (recallEq : control.execution.recall who = past) {key : LateKey setup leaks}
    (siteKey : lateKey setup leaks who (some (past, view)) = some key)
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime setup).eventRecorded leaks past event = false) {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) :
    key.owner = who ∧ turnEvent key = none ∧ bindingTurn key = some (event, payload) ∧
      decidedEvent key = some event := by
  have unsent := (unsentFor_iff_unrecorded setup leaks horizon scheduler trace recallEq
    siteKey event).mpr unrecorded
  simp only [lateKey, Option.some.injEq] at siteKey
  subst siteKey
  have noPublication : turnEvent (setup := setup) (leaks := leaks)
      { owner := who, current := operationalView setup leaks view,
        recalled := past.map fun entry =>
          (operationalView setup leaks entry.beforeView, entry.emitted),
        delivered := deliveredValue setup leaks who view } = none := by
    cases found : turnEvent (setup := setup) (leaks := leaks) _ with
    | none => rfl
    | some other =>
        obtain ⟨otherTurn, _, _, _, _, _, otherNode⟩ := publicationTurn_of_turnEvent found
        have same : other = event := Option.some.inj (otherTurn.symm.trans turn)
        subst same
        rw [node] at otherNode
        cases otherNode
  have binding := bindingTurn_of_bindingTurn ⟨turn, ⟨outputEq, codeEq, node⟩, unsent⟩
  refine ⟨rfl, noPublication, binding, ?_⟩
  unfold decidedEvent
  rw [noPublication, binding]
  rfl

open Classical in
/-- **The certificate's value-free success at a pending binding.** At a late
delivery or first activation of the binding `event` of `who` at which `who` owes
no failure, from a forced history of the site, with every binding value bounded,
a positive capacity covering the late options' slots, after the profile
installing a law at the site commits an as-if-honest choice at a permitted slot,
from a decision since the site's, the completion mass depends on the slot alone
up to the horizon times twice the cube of the scale. -/
theorem certificate_lateSuccessFree (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
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
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      (current ▸ history.1.trace)
  have pendingHere := pending
  rw [atSite] at pendingHere
  obtain ⟨turn, _, _, unrecorded⟩ := pendingEvent_spec pendingHere
  have siteKeyHere := siteKey
  rw [atSite] at siteKeyHere
  obtain ⟨ownerEq, noPublication, binding, decided⟩ := lateKey_decides_binding setup leaks
    horizon scheduler rawTrace rfl siteKeyHere turn unrecorded node
  have freshIff : ∀ control, siteFresh who site.1 control ↔
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [siteFresh, pending]
  have through := siteThrough_of_pendingHistory setup leaks bounds horizon scheduler pendingSite
    debtFree siteKey history
  rw [current] at through
  let lumping := certificateLumping setup leaks bounds horizon scheduler sequence scale scale_pos
    scale_le_one covers capacity slotsLe weights targetSequence assembled n who
  have imageBinding : ∀ state, lumping.image key state =
      Sum.inr (bindingImage event who payload state) := by
    intro state
    change decisionImage key state = _
    unfold decisionImage
    rw [noPublication, binding, ownerEq]
  refine lateBinding_successFree completes covers (sequence n) lumping site ⟨pendingSite, debtFree⟩
    siteKey (none : LateOption slots) decided Sum.inr imageBinding history.1 current ?_ _ ?_ node
    turn ordered decoded intendedPoint forced freshIff
  · -- Forced states with the event ready, the site's configuration and a recall
    -- extended by an entry at the site's view are kept.
    intro later control laterState laterForced laterReady sameConfig longer
    obtain ⟨entry, rest, recallEq, beforeEq⟩ := longer
    refine ⟨?_, ?_⟩
    · unfold decisionKept
      rw [decided]
      exact ⟨⟨later, laterState.symm ▸ rfl⟩, control, laterState,
        Or.inr ⟨ownerEq ▸ laterForced, laterReady⟩⟩
    · rw [laterState]
      refine ⟨⟨Or.inr ⟨entry, rest, by rw [recallEq, atSite]; rfl⟩,
        fun turnEvent siteTurn => ?_⟩, Or.inr ?_⟩
      · have clear := through.2 turnEvent siteTurn
        simp only [DebtClear] at clear ⊢
        rw [sameConfig]
        exact clear
      · intro control' controlEq entry' rest' recallEq' pendingEvent' pendingEq
        cases Option.some.inj controlEq
        have sameTail : entry :: rest = entry' :: rest' := by
          rw [atSite] at recallEq'
          exact List.append_cancel_left (recallEq.symm.trans recallEq')
        cases sameTail
        have samePending : pendingEvent' = event :=
          Option.some.inj (pendingEq.symm.trans pending)
        subst samePending
        change entry.beforeView.application.publicView.ownTurn? who = some pendingEvent'
        rw [beforeEq]
        exact turn
  · -- The installed law and the option's agree where the recall is longer.
    intro later longer player
    by_cases same : player = who
    · subst same
      simp only [Profile.update_same]
      have different : (onePacketN).infoOf player later.trace ≠ site.1 := by
        rw [atSite]
        change ((bounds.onePacketMenu (runtime setup) leaks).signals (initialLaw setup) horizon
          scheduler).infoOf player later.trace ≠ _
        rw [(bounds.onePacketMenu (runtime setup) leaks).info (initialLaw setup) horizon
          scheduler player later.trace]
        cases laterState : later.state with
        | none => simp [ReactiveApplication.observe]
        | some control =>
            have lengthLt := longer control laterState
            simp only [ReactiveApplication.observe]
            split_ifs
            · intro infoEq
              have recallEq := congrArg (fun info : (application setup leaks).Info =>
                (info.map Prod.fst).map List.length) infoEq
              simp only [Option.map_some] at recallEq
              have := Option.some.inj recallEq
              omega
            · simp
      rw [BehavioralPolicy.withLaw_of_ne _ _ _ different,
        BehavioralPolicy.withLaw_of_ne _ _ _ different]
    · simp only [Profile.update_of_ne _ _ same]

section Value

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- **The certificate's completion value at a pending binding.** At a late
delivery or first activation of the binding `event` of `who` at which `who` owes
no failure, from a forced history of the site whose decoded point at the site's
rank is intended and reached by the intended game, with every binding value
bounded and a positive capacity covering the late options' slots, under a
scheduler completing play, a law installed at the site under which the owner
plays the late owner shape from the history has completion value within a
multiple of the cube of the scale, times the payoff bound, of one less its
failure probability times the history's continuation value. -/
theorem certificate_pendingBinding_historyNear
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
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
    (shape : LateOwnerShapeFrom setup leaks bounds horizon scheduler (sequence n)
      (scale_pos n).le (scale_le_one n) slots
      (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
        (((targetSequence n).strategy who).withLaw site.1 law)) who event execution)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (ordered : execution.application.config.cut.IsPrefix (siteRank site.1))
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank site.1) execution.application.config =
      some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (reachedPoint : IntendedReached setup point)
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound) :
    |historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site law
        history.1 -
      (1 - siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site law
          history) *
        decodedPointValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          (setup.intendedOpeningProfile (sequence n).strategy) who (siteRank site.1) history.1| ≤
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
          (2 * horizon + 1) + 2 * (scale n ^ 3 * (2 * horizon + 1))) * bound := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      (current ▸ history.1.trace)
  have pendingHere := pending
  rw [atSite] at pendingHere
  obtain ⟨turn, _, _, unrecorded⟩ := pendingEvent_spec pendingHere
  have siteKeyHere := siteKey
  rw [atSite] at siteKeyHere
  obtain ⟨_, _, _, decided⟩ := lateKey_decides_binding setup leaks horizon scheduler rawTrace rfl
    siteKeyHere turn unrecorded node
  exact lateBinding_historyNear setup leaks bounds horizon scheduler parameter utility
    excludedPayoff completes covers capacity (sequence n) (scale_pos n) (scale_le_one n) slotsLe
    (targetSequence n) site decided pending law history current node turn
    unrecorded ordered decoded intendedPoint reachedPoint shape
    (mul_nonneg (Nat.cast_nonneg _) (by have := pow_nonneg (scale_pos n).le 3; linarith))
    (certificate_lateSuccessFree setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence assembled n completes covers capacity slotsLe site
      pendingSite debtFree siteKey pending law history current atSite forced node ordered decoded
      intendedPoint)
    readoutBounded

/-- **The certificate's completion value at a late binding.** At a late delivery
of the binding `event` of `who` at which `who` owes no failure, from a forced
history of the site whose decoded point at the site's rank is intended and
reached by the intended game, with every binding value bounded and a positive
capacity covering the late options' slots, under a scheduler completing play,
the profile installing a late option or silence at the site has completion value
within a multiple of the cube of the scale, times the payoff bound, of one less
its failure probability times the history's continuation value. -/
theorem certificate_lateBinding_historyNear
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount) {who : Player}
    (site : (onePacketN).InformationSite who) (late : LateDelivery setup leaks who site.1)
    (debtFree : SiteDebtFree setup leaks bounds horizon scheduler site)
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    {event : (graph setup).EventId} (pending : pendingEvent setup leaks who site.1 = some event)
    (law : PMF ((onePacketN).Choice who site.1))
    (lawShape : (∃ option : LateOption slots, law = onePacketLate setup leaks bounds horizon
        scheduler sequence scale scale_pos scale_le_one n ((onePacketN).agentAt site) option) ∨
      law = PMF.pure (silenceChoice setup leaks bounds (initialLaw setup) horizon scheduler who
        site.1))
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
    (reachedPoint : IntendedReached setup point)
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound) :
    |historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        (targetSequence n) (setup.intendedOpeningProfile (sequence n).strategy) site law
        history.1 -
      (1 - siteHistoryFailure setup leaks bounds horizon scheduler (targetSequence n) site law
          history) *
        decodedPointValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          (setup.intendedOpeningProfile (sequence n).strategy) who (siteRank site.1) history.1| ≤
      (2 * (scale n ^ 3 + (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3)) *
          (2 * horizon + 1) + 2 * (scale n ^ 3 * (2 * horizon + 1))) * bound := by
  exact certificate_pendingBinding_historyNear setup leaks bounds horizon scheduler parameter
    utility excludedPayoff sequence scale scale_pos scale_le_one weights targetSequence assembled n
    completes covers capacity slotsLe site (Or.inl late) debtFree siteKey pending law history
    current atSite forced
    (LateOwnerShape.from (certificate_lateOwnerShape setup leaks bounds horizon scheduler
      sequence scale scale_pos scale_le_one weights targetSequence assembled n site late pending
      law lawShape history current atSite forced))
    node ordered decoded intendedPoint reachedPoint readoutBounded

end Value

end Vegas
