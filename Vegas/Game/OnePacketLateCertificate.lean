/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateBadMass
import Vegas.Game.AsyncDeviationForeign

/-! # The certificate's late bindings

At a history of a decision site, the state is a decision of the site's owner
with the site's recall and view (`Vegas.state_of_site`). The key of a late
delivery of a binding with nothing sent decides that binding
(`Vegas.lateKey_decides_binding`). The certificate's lumping
(`Vegas.certificateLumping`) makes success after a commitment value-free: at a
late delivery or first activation of a pending binding at which the owner owes
no failure, after an as-if-honest commitment at a permitted slot, the completion
mass depends on the slot alone up to the horizon times twice the cube of the
scale (`Vegas.certificate_lateSuccessFree`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler

omit [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- At a history of a decision site of `who`, the state is a decision of `who`
whose recall and view are the site's. -/
theorem state_of_site {who : Player} {site : (onePacketN).InformationSite who}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (atSite : site.1 = some (past, view))
    (history : (onePacketN).InformationHistory who site.1) :
    ∃ remaining execution, history.1.state = some ⟨remaining, some who, execution⟩ ∧
      execution.recall who = past ∧ execution.observe (application setup runtime leaks) who = view
        := by
  obtain ⟨fullHistory, infoEq⟩ := history
  have observed : (application setup runtime leaks).observe who fullHistory.state = some (past,
    view) :=
    ((bounds.onePacketMenu runtime leaks).info (initialLaw setup) horizon scheduler who
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

omit [Fintype Player] [(application setup runtime leaks).FiniteNature (initialLaw setup)
  scheduler] in
/-- The key of a late delivery of a binding with nothing sent decides that
binding: it is no publication turn, its binding turn is the event, and its
decided event is the event. -/
theorem lateKey_decides_binding {who : Player} {past : List (application setup runtime
  leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} {control : (application setup runtime
      leaks).Control}
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (recallEq : control.execution.recall who = past) {key : LateKey setup runtime leaks}
    (siteKey : lateKey setup runtime leaks who (some (past, view)) = some key)
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (unrecorded : runtime.eventRecorded leaks past event = false) {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) :
    key.owner = who ∧ turnEvent (runtime := runtime) key = none ∧ bindingTurn
      (runtime := runtime) key = some (event, payload) ∧
      decidedEvent (runtime := runtime) key = some event := by
  have unsent := (unsentFor_iff_unrecorded setup runtime leaks horizon scheduler trace recallEq
    siteKey event).mpr unrecorded
  simp only [lateKey, Option.some.injEq] at siteKey
  subst siteKey
  have noPublication : turnEvent (runtime := runtime) (setup := setup) (leaks := leaks)
      { owner := who
        current := operationalView setup runtime leaks view
        recalled := past.map fun entry =>
          (operationalView setup runtime leaks entry.beforeView, entry.emitted)
        delivered := deliveredValue setup runtime leaks who view } = none := by
    cases found : turnEvent (runtime := runtime) (setup := setup) (leaks := leaks) _ with
    | none => rfl
    | some other =>
        obtain ⟨otherTurn, _, _, _, _, _, otherNode⟩ := publicationTurn_of_turnEvent (runtime :=
          runtime) found
        have same : other = event := Option.some.inj (otherTurn.symm.trans turn)
        subst same
        rw [node] at otherNode
        cases otherNode
  have binding := bindingTurn_of_bindingTurn (runtime := runtime) ⟨turn, ⟨outputEq, codeEq, node⟩,
    unsent⟩
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
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
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
    (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup runtime leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.recall who,
      execution.observe (application setup runtime leaks) who))
    (forced : ForcedState setup runtime leaks who history.1.state)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (ordered : execution.application.config.cut.IsPrefix (siteRank (runtime := runtime) site.1))
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank (runtime := runtime) site.1)
      execution.application.config =
      some point)
    (terminalCompleted : ∀ (final : (application setup runtime leaks).Control),
      ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup runtime leaks).terminal (some final) →
      final.execution.application.config = execution.application.config →
      event ∈ final.execution.application.config.cut.completed)
    (intendedPoint : ProtocolState.Intended setup.program point) :
    ∀ (later : ((bounds.onePacketMenu runtime leaks).protocol
        (initialLaw setup) horizon scheduler).History) (laterRemaining : Nat)
        (reached : (application setup runtime leaks).Execution),
      later.state = some ⟨laterRemaining, some who, reached⟩ →
      LateUnsent setup runtime leaks who event execution.application.config (execution.recall who)
        later.state →
      (reached.recall who = execution.recall who →
        reached.observe (application setup runtime leaks) who =
          execution.observe (application setup runtime leaks) who) →
      (reached.recall who ≠ execution.recall who → ∃ response,
        execution.recall who ++ [respondEntry setup runtime leaks execution who response] <+:
          reached.recall who) →
      ∀ slot < bounds.candidateCount,
        countPermits ((application setup runtime leaks).outputs (reached.recall who))
          (slotEnvelope setup runtime leaks who (reached.recall who)
            (reached.observe (application setup runtime leaks) who) event slot) = true →
        ∃ factor : ℝ, ∀ choice ∈ (asIfHonestProfile setup runtime leaks (sequence n) who
            (some (reached.recall who, reached.observe (application setup runtime leaks)
              who))).support,
          ∀ next : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
              horizon scheduler).History,
            next.state = some ⟨laterRemaining, none, reached.respond (application setup runtime
              leaks)
              who (slotResponse setup runtime leaks who (reached.recall who)
                (reached.observe (application setup runtime leaks) who) event slot choice)⟩ →
            |expect ((onePacketN).runBehavioralUntil
                ((bounds.onePacketMenu runtime leaks).bounded (initialLaw setup) horizon
                  scheduler).wellFoundedHistories
                (Profile.update (sig := (onePacketN).behavioralSignature)
                  (targetSequence n).strategy who
                  (((targetSequence n).strategy who).withLaw site.1 law))
                (LateStopped setup runtime leaks bounds horizon scheduler (siteRank (runtime :=
                  runtime) site.1)) next)
                (completionIndicator setup runtime leaks bounds horizon scheduler (siteRank
                  (runtime := runtime) site.1)
                  (siteFresh (runtime := runtime) who site.1)) - factor| ≤
              (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3) := by
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      (current ▸ history.1.trace)
  have pendingHere := pending
  rw [atSite] at pendingHere
  obtain ⟨turn, _, _, unrecorded⟩ := pendingEvent_spec (runtime := runtime) pendingHere
  have siteKeyHere := siteKey
  rw [atSite] at siteKeyHere
  obtain ⟨ownerEq, noPublication, binding, decided⟩ := lateKey_decides_binding setup runtime leaks
    horizon scheduler rawTrace rfl siteKeyHere turn unrecorded node
  have freshIff : ∀ control, siteFresh (runtime := runtime) who site.1 control ↔
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [siteFresh, pending]
  have through := siteThrough_of_pendingHistory setup runtime leaks bounds horizon scheduler
    pendingSite
    debtFree siteKey history
  rw [current] at through
  let lumping := certificateLumping setup runtime leaks bounds horizon scheduler sequence scale
    scale_pos
    scale_le_one covers capacity slotsLe weights targetSequence assembled n who
  have imageBinding : ∀ state, lumping.image key state =
      Sum.inr (bindingImage (runtime := runtime) event who payload state) := by
    intro state
    change decisionImage (runtime := runtime) key state = _
    unfold decisionImage
    rw [noPublication, binding, ownerEq]
  refine lateBinding_successFree (runtime := runtime) covers (sequence n) lumping site
    ⟨pendingSite, debtFree⟩
    siteKey (none : LateOption slots) decided Sum.inr imageBinding history.1 current ?_ _ ?_ node
    turn ordered decoded terminalCompleted intendedPoint forced freshIff
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
        change ((bounds.onePacketMenu runtime leaks).signals (initialLaw setup) horizon
          scheduler).infoOf player later.trace ≠ _
        rw [(bounds.onePacketMenu runtime leaks).info (initialLaw setup) horizon
          scheduler player later.trace]
        cases laterState : later.state with
        | none => simp [ReactiveApplication.observe]
        | some control =>
            have lengthLt := longer control laterState
            simp only [ReactiveApplication.observe]
            split_ifs
            · intro infoEq
              have recallEq := congrArg (fun info : (application setup runtime leaks).Info =>
                (info.map Prod.fst).map List.length) infoEq
              simp only [Option.map_some] at recallEq
              have := Option.some.inj recallEq
              omega
            · simp
      rw [BehavioralPolicy.withLaw_of_ne _ _ _ different,
        BehavioralPolicy.withLaw_of_ne _ _ _ different]
    · simp only [Profile.update_of_ne _ _ same]

end Vegas
