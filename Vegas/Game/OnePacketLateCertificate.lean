module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketLateBadMass
public import Vegas.Game.OnePacketCertificateLumping

@[expose] public section

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
  (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon scheduler

omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- At a history of a decision site of `who`, the state is a decision of `who`
whose recall and view are the site's. -/
theorem state_of_site {who : Player} {site : (onePacketN).InformationSite who}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (atSite : site.1 = some (past, view))
    (history : (onePacketN).InformationHistory who site.1) :
    ∃ remaining execution, history.1.state = some ⟨remaining, some who, execution⟩ ∧
      execution.logs who = past ∧ execution.observe (application setup timeouts leaks) who = view
        := by
  obtain ⟨fullHistory, infoEq⟩ := history
  have observed : (application setup timeouts leaks).observe who fullHistory.state = some (past,
    view) :=
    ((bounds.onePacketMenu timeouts leaks).info (initialLaw setup) horizon scheduler who
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

omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- Every history of a decision site of `who` with a pending event is a prefix of
the site's rank. -/
theorem ordered_of_site {who : Player} {site : (onePacketN).InformationSite who}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} (atSite : site.1 = some (past, view))
    (history : (onePacketN).InformationHistory who site.1) :
    ∃ remaining execution, history.1.state = some ⟨remaining, some who, execution⟩ ∧
      execution.logs who = past ∧ execution.observe (application setup timeouts leaks) who = view ∧
      execution.application.config.cut.IsPrefix (siteRank (timeouts := timeouts) site.1) := by
  obtain ⟨remaining, execution, current, recallEq, observeEq⟩ :=
    state_of_site setup timeouts leaks bounds horizon scheduler atSite history
  refine ⟨remaining, execution, current, recallEq, observeEq, ?_⟩
  have rawTrace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon scheduler
      (current ▸ history.1.trace)
  obtain ⟨found, foundOrdered, _⟩ := pendingAt_history (timeouts := timeouts) rawTrace
  have rankEq : siteRank (timeouts := timeouts) site.1 = found := by
    rw [atSite, ← observeEq]
    change (execution.application.config.history.map EventCompletion.event).length = found
    rw [List.length_map]
    exact history_length_of_isPrefix _ foundOrdered
  exact rankEq ▸ foundOrdered

omit [Fintype Player] [(application setup timeouts leaks).FiniteNature (initialLaw setup)
  scheduler] in
/-- The key of a late delivery of a binding with nothing sent decides that
binding: it is no publication turn, its binding turn is the event, and its
decided event is the event. -/
theorem lateKey_decides_binding {who : Player} {past : List (application setup timeouts
  leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} {control : (application setup timeouts
      leaks).Control}
    (trace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace
      (some control))
    (recallEq : control.execution.logs who = past) {key : LateKey setup timeouts leaks}
    (siteKey : lateKey setup timeouts leaks who (some (past, view)) = some key)
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (unrecorded : (eventRecorded timeouts) leaks past event = false) {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq) :
    key.owner = who ∧ turnEvent (timeouts := timeouts) key = none ∧ bindingTurn
      (timeouts := timeouts) key = some (event, payload) ∧
      decidedEvent (timeouts := timeouts) key = some event := by
  have unsent := (unsentFor_iff_unrecorded setup timeouts leaks horizon scheduler trace recallEq
    siteKey event).mpr unrecorded
  simp only [lateKey, Option.some.injEq] at siteKey
  subst siteKey
  have noPublication : turnEvent (timeouts := timeouts) (setup := setup) (leaks := leaks)
      { owner := who
        current := operationalView setup timeouts leaks view
        recalled := past.map fun entry =>
          (operationalView setup timeouts leaks entry.beforeView, entry.emitted)
        delivered := deliveredValue setup timeouts leaks who view } = none := by
    cases found : turnEvent (timeouts := timeouts) (setup := setup) (leaks := leaks) _ with
    | none => rfl
    | some other =>
        obtain ⟨otherTurn, _, _, _, _, _, otherNode⟩ := publicationTurn_of_turnEvent (timeouts :=
          timeouts) found
        have same : other = event := Option.some.inj (otherTurn.symm.trans turn)
        subst same
        rw [node] at otherNode
        cases otherNode
  have binding := bindingTurn_of_bindingTurn (timeouts := timeouts) ⟨turn, ⟨outputEq, codeEq, node⟩,
    unsent⟩
  refine ⟨rfl, noPublication, binding, ?_⟩
  unfold decidedEvent
  rw [noPublication, binding]
  rfl

section

variable {setup timeouts leaks bounds horizon scheduler}

omit [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
open Classical in
/-- **Value-free success after a late commitment.** Let a one-step lumping of
the profiles profileOf fail where the decided binding `event` of `who` fails
in the store, with its image at the key read off the binding image, and keep
every forced state with the event ready, the configuration of a history, and a
recall of `who` extending the one there by an entry taken at its view. Let
`installed` agree with the profile of an option wherever the recall of `who` is
longer than there. Then, at every decision of `who` since the history at which
it has sent nothing for the event, after committing
an as-if-honest source choice at a permitted slot within the capacity, the
completion mass of play of `installed` until the event completes depends, up
to the horizon times `δ`, on the slot alone. -/
theorem lateBinding_successFree
    [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
    (covers : bounds.CoversOutputValues)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {target : (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralAssessment}
    {who : Player}
    {relevant : (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).InformationSite who →
      Prop} {LateOption' : Type}
    {profileOf : (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).InformationSite who →
      LateOption' → ∀ player,
        (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
          scheduler).BehavioralPolicy player}
    {δ : ℝ} {Y : Type}
    (lumping : PendingLumpingOn (timeouts := timeouts) target who relevant profileOf
      (DecisionFailed (timeouts := timeouts)) δ Y)
    (site : (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).InformationSite who)
    (isRelevant : relevant site) {key : LateKey setup timeouts leaks}
    (siteKey : lateKey setup timeouts leaks who site.1 = some key)
    (option : LateOption') {event : (graph setup).EventId}
    (decided : decidedEvent (timeouts := timeouts) key = some event) {payload : L.Ty}
    (imageOfBinding : BindingImage (timeouts := timeouts) (setup := setup) (leaks := leaks) → Y)
    (imageBinding : ∀ state, lumping.image key state =
      imageOfBinding (bindingImage (timeouts := timeouts) event who payload state))
    (start : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    {remaining : Nat} {execution : (application setup timeouts leaks).Execution}
    (current : start.state = some ⟨remaining, some who, execution⟩)
    (keptOf : ∀ (history : ((bounds.onePacketMenu timeouts leaks).protocol
        (initialLaw setup) horizon scheduler).History)
        (control : (application setup timeouts leaks).Control),
      history.state = some control → ForcedState setup timeouts leaks who (some control) →
      control.execution.application.config.cut.Ready event →
      control.execution.application.config = execution.application.config →
      (∃ entry rest, control.execution.logs who = execution.logs who ++ entry :: rest ∧
        entry.beforeView = execution.observe (application setup timeouts leaks) who) →
      history.state ∈ lumping.keep site key)
    (installed : ∀ player, (onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy player)
    (agreeLonger : ∀ history : ((bounds.onePacketMenu timeouts leaks).protocol
        (initialLaw setup) horizon scheduler).History,
      (∀ control, history.state = some control →
        (execution.logs who).length < (control.execution.logs who).length) →
      ∀ player, installed player
          ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
            scheduler).infoOf player
            history.trace) =
        profileOf site option player
          ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
            scheduler).infoOf player
            history.trace))
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (turn : execution.application.publicView.ownTurn? who = some event)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (terminalCompleted : ∀ (final : (application setup timeouts leaks).Control),
      ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup timeouts leaks).terminal (some final) →
      final.execution.application.config = execution.application.config →
      event ∈ final.execution.application.config.cut.completed)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (forced : ForcedState setup timeouts leaks who start.state)
    {fresh : (application setup timeouts leaks).Control → Prop}
    (freshIff : ∀ control, fresh control ↔
      ¬ StoreEventFailed control.execution.application.config.store event) :
    ∀ (history : ((bounds.onePacketMenu timeouts leaks).protocol
        (initialLaw setup) horizon scheduler).History) (later : Nat)
        (reached : (application setup timeouts leaks).Execution),
      history.state = some ⟨later, some who, reached⟩ →
      LateUnsent setup timeouts leaks who event execution.application.config (execution.logs who)
        history.state →
      (reached.logs who = execution.logs who →
        reached.observe (application setup timeouts leaks) who =
          execution.observe (application setup timeouts leaks) who) →
      (reached.logs who ≠ execution.logs who → ∃ response,
        execution.logs who ++ [respondEntry setup timeouts leaks execution who response] <+:
          reached.logs who) →
      ∀ slot < bounds.candidateCount,
        countPermits ((application setup timeouts leaks).outputs (reached.logs who))
          (slotEnvelope setup timeouts leaks who (reached.logs who)
            (reached.observe (application setup timeouts leaks) who) event slot) = true →
        ∃ factor : ℝ, ∀ choice ∈ (asIfHonestProfile setup timeouts leaks assessment who
            (some (reached.logs who, reached.observe (application setup timeouts leaks)
              who))).support,
          ∀ next : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
              horizon scheduler).History,
            next.state = some ⟨later, none, reached.respond (application setup timeouts leaks) who
              (slotResponse setup timeouts leaks who (reached.logs who)
                (reached.observe (application setup timeouts leaks) who) event slot choice)⟩ →
            |expect ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
                scheduler).runBehavioralUntil
                ((bounds.onePacketMenu timeouts leaks).bounded (initialLaw setup) horizon
                  scheduler).wellFoundedHistories installed
                (LateStopped setup timeouts leaks bounds horizon scheduler rank) next)
                (completionIndicator setup timeouts leaks bounds horizon scheduler rank fresh) -
              factor| ≤ (2 * horizon + 1 : ℕ) * δ := by
  intro history later reached state holds sameView extended slot below permitted
  let menu := bounds.onePacketMenu timeouts leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  obtain ⟨atSent, extends_, _⟩ := (by simpa only [state] using holds :
    LateUnsent setup timeouts leaks who event execution.application.config (execution.logs who)
      (some ⟨later, some who, reached⟩))
  have traceHere : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨later, some who, reached⟩) := state ▸ history.trace
  have readySent : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  have readyHere : reached.application.config.cut.Ready event := by
    rw [atSent]
    exact readySent
  have orderedHere : reached.application.config.cut.IsPrefix rank := by
    rw [atSent]
    exact ordered
  have decodedHere : sourceServicePrefix? setup rank reached.application.config =
      some point := by
    rw [atSent]
    exact decoded
  have turnHere : reached.application.publicView.ownTurn? who = some event := by
    rw [ownTurn?_eq_of_eventReady_iff (second := execution.application.publicView)
      (fun other => by
        rw [State.publicView_eventReady, State.publicView_eventReady, atSent]) who]
    exact turn
  have forcedHere : ∀ control : (application setup timeouts leaks).Control,
      control.execution.application.config = execution.application.config →
      ForcedState setup timeouts leaks who (some control) := by
    intro control sameConfig
    rw [current] at forced
    obtain ⟨forcedRank, forcedPoint, forcedOrdered, forcedDecoded, forcedHolds⟩ := forced
    exact ⟨forcedRank, forcedPoint, by rw [sameConfig]; exact forcedOrdered,
      by rw [sameConfig]; exact forcedDecoded, forcedHolds⟩
  -- The committed image, read off the slot alone.
  let committed : BindingImage (timeouts := timeouts) (setup := setup) (leaks := leaks) :=
    committedImage (timeouts := timeouts) event who (who, .prepared slot)
      (operationalState setup timeouts leaks (some ⟨later, some who, reached⟩))
  refine ⟨1 - expect ((fun law => law.bind (lumping.kernel key option))^[2 *
    horizon + 1]
    (PMF.pure (imageOfBinding committed))) (lumping.failure key), fun choice
      member next
      nextState => ?_⟩
  have covered := onePacket_honest_covered (timeouts := timeouts) assessment covers traceHere who
    event turnHere choice
    member
  have inMenu := (slotResponse_mem_onePacket_iff setup timeouts leaks bounds who (reached.logs who)
    (reached.observe (application setup timeouts leaks) who) event node slot below choice
    covered).mpr permitted
  obtain ⟨action, encoded, values⟩ := covered
  obtain ⟨committedValue, successful, _⟩ := values who payload outputEq codeEq node
  obtain ⟨material, transmits, envelope⟩ := slotResponse_transmission setup timeouts leaks who
    (reached.logs who) (reached.observe (application setup timeouts leaks) who) event node slot
      choice
    action encoded (by rw [successful]; rfl)
  have call : material.call.packet = .commitment event (who, .prepared slot) :=
    congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
      message.payload.call) envelope
  -- The commitment invariant and the source step of the committed choice.
  obtain ⟨entry, message, invariant⟩ := openableCommitmentInvariant_slot (timeouts := timeouts)
    bounds horizon
    scheduler traceHere node readyHere slot choice action encoded successful permitted
    (nextState ▸ next.trace)
  obtain ⟨found, ⟨residualFound⟩⟩ := protocol_sourceResidual (timeouts := timeouts) (failureProfile
    setup.program)
    menu horizon scheduler traceHere _ rfl
  have foundEq : found = rank :=
      EventOrder.Cut.IsPrefix.unique residualFound.checkpoint.ordered orderedHere
  have residual := foundEq ▸ residualFound
  cases choice with
  | none => simp at encoded
  | some source =>
  have encodedSource : encodeEventAction? setup.program event source = some action := encoded
  have decodeEq := decodeEventAction_encodeEventAction?_eq_some setup.program event source action
    encodedSource
  have owned : (graph setup).actor? event = some who := nodeView_bind_actor outputEq codeEq
  have pointDecoded : decodedPoint setup reached.application.config = some point :=
    (decodedPoint_eq_of_isPrefix orderedHere).trans decodedHere
  have rawTrace := menu.toRawTrace (initialLaw setup) horizon scheduler traceHere
  have active := reached.application.active_of_ready_owned
    (legalFacts setup leaks horizon scheduler _ rawTrace).quiescent readyHere owned
  have acts : ∀ player, ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some who := fun player =>
    (decodedPoint_actor player readyHere pointDecoded).trans (by simp [owned, active])
  obtain ⟨stepTarget, stepEq⟩ := ProtocolState.step_eq_pure_of_actor who who setup.program point
    (fun _ => some source) (acts who)
  have stepEq' : ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) = PMF.pure stepTarget := by
    rw [decodeEq]
    exact stepEq
  obtain ⟨intended, _, same⟩ := (mem_support_asIfHonestProfile_observe setup timeouts leaks
    assessment who
    reached rank orderedHere point decodedHere (reached.logs who) _).mp member
  have legal := intended.2
  change ProtocolView.intendedMenu who setup.program
    (ProtocolState.observe who setup.program point) intended.1 at legal
  rw [same] at legal
  have targetIntended : ProtocolState.Intended setup.program stepTarget := by
    refine ProtocolState.intended_step_of_actors setup.program point _ stepTarget intendedPoint
      (fun player active => ?_) (by rw [stepEq]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
    cases (acts player).symm.trans active
    exact ⟨source, rfl, legal.2⟩
  have massEq := expect_completionIndicator_of_openableCommitment (timeouts := timeouts) installed
    codeEq
    successful residual decodedHere
    (fun final trace ended same => terminalCompleted final trace ended (same.trans atSent))
      stepEq' targetIntended freshIff next
    (by rw [nextState]; exact invariant)
  -- Play from the commitment is play of the option's profile.
  have nextRecall : (execution.logs who).length <
      ((reached.respond (application setup timeouts leaks) who (slotResponse setup timeouts
        leaks who
        (reached.logs who) (reached.observe (application setup timeouts leaks) who) event slot
          (some source))).logs who).length := by
    rw [(respond_recall timeouts) leaks reached who who, ite_eq_left rfl ..,
      List.length_append, List.length_singleton]
    have lengthLe : (execution.logs who).length ≤ (reached.logs who).length :=
      extends_.length_le
    omega
  have samePlay : model.runBehavioralFrom installed (2 * horizon + 1) next =
      model.runBehavioralFrom (profileOf site option) (2 * horizon + 1) next := by
    apply model.runBehavioralFrom_congr (2 * horizon + 1) next
    intro later' path _ player
    apply agreeLonger later'
    intro control laterState
    have rawPath := menu.reaches_raw (initialLaw setup) horizon scheduler path
    have grown := (application setup timeouts leaks).reaches_recall_prefix (initialLaw setup)
      horizon
      scheduler rawPath _ control nextState laterState who
    exact lt_of_lt_of_le nextRecall grown.length_le
  have failedEq : (fun final : (menu.protocol (initialLaw setup) horizon scheduler).History =>
      if EventFailedState setup timeouts leaks event final.state then (1 : ℝ) else 0) =
      fun final => if DecisionFailed (timeouts := timeouts) key final.state then 1 else 0 := by
    funext final
    have same : EventFailedState setup timeouts leaks event final.state ↔
        DecisionFailed (timeouts := timeouts) key final.state := by
      cases final.state with
      | none => simp [EventFailedState, DecisionFailed]
      | some control => simp [EventFailedState, DecisionFailed, decided]
    exact if_congr same rfl rfl
  -- The kept image after the commitment is the committed image.
  have keptNext : next.state ∈ lumping.keep site key := by
    have configEq := ((reactive_respond_application timeouts) leaks reached who
      (slotResponse setup timeouts leaks who (reached.logs who)
        (reached.observe (application setup timeouts leaks) who) event slot (some source))).1.trans
          atSent
    refine keptOf next _ nextState (forcedHere _ configEq) ?_ configEq ?_
    · rw [((reactive_respond_application timeouts) leaks reached who _).1]
      exact readyHere
    · have respondRecall : ∃ emitted, (reached.respond (application setup timeouts leaks) who
          (slotResponse setup timeouts leaks who (reached.logs who)
            (reached.observe (application setup timeouts leaks) who) event slot (some
              source))).logs
            who = reached.logs who ++
            [⟨reached.observe (application setup timeouts leaks) who, slotResponse setup timeouts
              leaks who
              (reached.logs who) (reached.observe (application setup timeouts leaks) who) event
                slot
              (some source), emitted⟩] := by
        rcases (slotResponse setup timeouts leaks who (reached.logs who)
          (reached.observe (application setup timeouts leaks) who) event slot (some source)) with
          ⟨transmission⟩
        cases transmission <;>
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte] <;> exact ⟨_, rfl⟩
      obtain ⟨emitted, recallEq⟩ := respondRecall
      rw [recallEq]
      by_cases atStart : reached.logs who = execution.logs who
      · exact ⟨_, [], by rw [atStart], sameView atStart⟩
      · obtain ⟨response, tail, tailEq⟩ := extended atStart
        refine ⟨respondEntry setup timeouts leaks execution who response,
          tail ++ [⟨reached.observe (application setup timeouts leaks) who, slotResponse setup
            timeouts leaks who
            (reached.logs who) (reached.observe (application setup timeouts leaks) who) event slot
            (some source), emitted⟩], ?_, rfl⟩
        rw [← tailEq]
        simp
  have fresh' : reached.application.candidates.lookup (who, .prepared slot) = .fresh :=
    onePacket_permitted_fresh (timeouts := timeouts) (control := ⟨later, some who, reached⟩)
      traceHere who event slot
      permitted
  have succeeds : candidateSucceeds ((application setup timeouts leaks).submit reached.application
    who
      material) (who, .prepared slot) payload = true := by
    have bound := slotResponse_of_bind setup timeouts leaks who (reached.logs who)
      (reached.observe (application setup timeouts leaks) who) event node slot (some source) action
        encoded
    have boundTransmits := transmits
    rw [successful] at bound
    rw [bound] at boundTransmits
    have materialEq := Option.some.inj boundTransmits.symm
    have submitted : (application setup timeouts leaks).submit reached.application who material =
        (reached.respond (application setup timeouts leaks) who
          ((reactiveBinding timeouts) leaks who event payload (.success committedValue)
            slot)).application
          := by
      rw [materialEq]
      change (application setup timeouts leaks).submit reached.application who
        (((reactiveNormalization timeouts) leaks).normalize who
          ((application setup timeouts leaks).observePlayer reached.application who)
          (ReactiveApplication.ResponseMenu.knownPackets (reached.logs who)
            (reached.observe (application setup timeouts leaks) who))
          ⟨⟨.commitment event (who, .prepared slot), some ⟨payload, committedValue⟩⟩, .none⟩) = _
      rw [((reactiveNormalization timeouts) leaks).submit]
      rfl
    have result := (reactiveBinding_result timeouts) leaks who event payload
      (.success committedValue) slot reached fresh'
    unfold candidateSucceeds
    rw [submitted]
    change (match (reached.respond ((reactiveApplication timeouts) leaks) who
        ((reactiveBinding timeouts) leaks who event payload (.success committedValue)
          slot)).application.bindingResult (who, .prepared slot) payload with
      | .success _ => true
      | .failure => false) = true
    rw [result]
  have imageNext : lumping.image key next.state = imageOfBinding committed :=
    by
    rw [imageBinding, nextState, committed_bindingImage (timeouts := timeouts) bounds history state
      readyHere.1
      (commitStatuses_nil_of_permitted (timeouts := timeouts) traceHere who event slot permitted
        payload) _ inMenu
      transmits call succeeds]
  have lumped := lumping.abs_failure_sub_le_of_keep (2 * horizon + 1) site
    isRelevant key siteKey
    option next
    keptNext
  rw [imageNext, ← failedEq, ← samePlay] at lumped
  rw [massEq]
  calc _ = |expect ((fun law => law.bind (lumping.kernel key option))^[2 *
    horizon + 1]
        (PMF.pure (imageOfBinding committed))) (lumping.failure key) -
      expect (model.runBehavioralFrom installed (2 * horizon + 1) next)
        (fun final => if EventFailedState setup timeouts leaks event final.state then 1 else 0)| :=
          by
        congr 1
        ring
    _ = _ := abs_sub_comm _ _
    _ ≤ _ := lumped

end

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
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup timeouts leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup timeouts leaks bounds horizon scheduler sequence scale
      scale_pos
      scale_le_one weights targetSequence) (n : ℕ)
    (covers : bounds.CoversOutputValues) (capacity : 1 ≤ bounds.candidateCount)
    (slotsLe : slots ≤ bounds.candidateCount) {who : Player}
    (site : (onePacketN).InformationSite who)
    (pendingSite : LateDelivery setup timeouts leaks who site.1 ∨ FirstActivation setup timeouts
      leaks who site.1)
    (debtFree : SiteDebtFree setup timeouts leaks bounds horizon scheduler site)
    {key : LateKey setup timeouts leaks} (siteKey : lateKey setup timeouts leaks who site.1 = some
      key)
    {event : (graph setup).EventId} (pending : pendingEvent setup timeouts leaks who site.1 = some
      event)
    (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup timeouts leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.logs who,
      execution.observe (application setup timeouts leaks) who))
    (forced : ForcedState setup timeouts leaks who history.1.state)
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (ordered : execution.application.config.cut.IsPrefix (siteRank (timeouts := timeouts) site.1))
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank (timeouts := timeouts) site.1)
      execution.application.config =
      some point)
    (terminalCompleted : ∀ (final : (application setup timeouts leaks).Control),
      ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup timeouts leaks).terminal (some final) →
      final.execution.application.config = execution.application.config →
      event ∈ final.execution.application.config.cut.completed)
    (intendedPoint : ProtocolState.Intended setup.program point) :
    ∀ (later : ((bounds.onePacketMenu timeouts leaks).protocol
        (initialLaw setup) horizon scheduler).History) (laterRemaining : Nat)
        (reached : (application setup timeouts leaks).Execution),
      later.state = some ⟨laterRemaining, some who, reached⟩ →
      LateUnsent setup timeouts leaks who event execution.application.config (execution.logs who)
        later.state →
      (reached.logs who = execution.logs who →
        reached.observe (application setup timeouts leaks) who =
          execution.observe (application setup timeouts leaks) who) →
      (reached.logs who ≠ execution.logs who → ∃ response,
        execution.logs who ++ [respondEntry setup timeouts leaks execution who response] <+:
          reached.logs who) →
      ∀ slot < bounds.candidateCount,
        countPermits ((application setup timeouts leaks).outputs (reached.logs who))
          (slotEnvelope setup timeouts leaks who (reached.logs who)
            (reached.observe (application setup timeouts leaks) who) event slot) = true →
        ∃ factor : ℝ, ∀ choice ∈ (asIfHonestProfile setup timeouts leaks (sequence n) who
            (some (reached.logs who, reached.observe (application setup timeouts leaks)
              who))).support,
          ∀ next : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
              horizon scheduler).History,
            next.state = some ⟨laterRemaining, none, reached.respond (application setup timeouts
              leaks)
              who (slotResponse setup timeouts leaks who (reached.logs who)
                (reached.observe (application setup timeouts leaks) who) event slot choice)⟩ →
            |expect ((onePacketN).runBehavioralUntil
                ((bounds.onePacketMenu timeouts leaks).bounded (initialLaw setup) horizon
                  scheduler).wellFoundedHistories
                (Profile.update (sig := (onePacketN).behavioralSignature)
                  (targetSequence n).strategy who
                  (((targetSequence n).strategy who).withLaw site.1 law))
                (LateStopped setup timeouts leaks bounds horizon scheduler (siteRank (timeouts :=
                  timeouts) site.1)) next)
                (completionIndicator setup timeouts leaks bounds horizon scheduler (siteRank
                  (timeouts := timeouts) site.1)
                  (siteFresh (timeouts := timeouts) who site.1)) - factor| ≤
              (2 * horizon + 1 : ℕ) * (scale n ^ 3 + scale n ^ 3) := by
  have rawTrace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon scheduler
      (current ▸ history.1.trace)
  have pendingHere := pending
  rw [atSite] at pendingHere
  obtain ⟨turn, _, _, unrecorded⟩ := pendingEvent_spec (timeouts := timeouts) pendingHere
  have siteKeyHere := siteKey
  rw [atSite] at siteKeyHere
  obtain ⟨ownerEq, noPublication, binding, decided⟩ := lateKey_decides_binding setup timeouts leaks
    horizon scheduler rawTrace rfl siteKeyHere turn unrecorded node
  have freshIff : ∀ control, siteFresh (timeouts := timeouts) who site.1 control ↔
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [siteFresh, pending]
  have through := siteThrough_of_pendingHistory setup timeouts leaks bounds horizon scheduler
    pendingSite
    debtFree siteKey history
  rw [current] at through
  let lumping := certificateLumping setup timeouts leaks bounds horizon scheduler sequence scale
    scale_pos
    scale_le_one covers capacity slotsLe weights targetSequence assembled n who
  have imageBinding : ∀ state, lumping.image key state =
      Sum.inr (bindingImage (timeouts := timeouts) event who payload state) := by
    intro state
    change decisionImage (timeouts := timeouts) key state = _
    unfold decisionImage
    rw [noPublication, binding, ownerEq]
  refine lateBinding_successFree (timeouts := timeouts) covers (sequence n) lumping site
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
        change ((bounds.onePacketMenu timeouts leaks).signals (initialLaw setup) horizon
          scheduler).infoOf player later.trace ≠ _
        rw [(bounds.onePacketMenu timeouts leaks).info (initialLaw setup) horizon
          scheduler player later.trace]
        cases laterState : later.state with
        | none => simp [ReactiveApplication.observe]
        | some control =>
            have lengthLt := longer control laterState
            simp only [ReactiveApplication.observe]
            split_ifs
            · intro infoEq
              have recallEq := congrArg (fun info : (application setup timeouts leaks).Info =>
                (info.map Prod.fst).map List.length) infoEq
              simp only [Option.map_some] at recallEq
              have := Option.some.inj recallEq
              omega
            · simp
      rw [BehavioralPolicy.withLaw_of_ne _ _ _ different,
        BehavioralPolicy.withLaw_of_ne _ _ _ different]
    · simp only [Profile.update_of_ne _ _ same]

end Vegas
