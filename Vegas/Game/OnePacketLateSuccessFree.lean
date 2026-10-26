/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketLateCompletionLaw
import Vegas.Game.ServiceWithheldForfeit

/-! # Value-free success after a late commitment

**Completion mass is the success probability.** After a commitment of a binding
to an openable value whose source action reaches an intended point, the mass of
stops with a completion point is one less the probability that terminal play
fails the event (`Vegas.expect_completionIndicator_of_openableCommitment`): the
event completes by the committed action, at a fresh intended point, or by a
failure, and either outcome stays on the store.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

variable (setup runtime leaks) in
/-- The event has completed with a failure. -/
def EventFailedState (event : (graph setup).EventId) :
    (application setup runtime leaks).ProtocolState → Prop
  | none => False
  | some control => event ∈ control.execution.application.config.cut.completed ∧
      StoreEventFailed control.execution.application.config.store event

open Classical in
/-- At a stop one step of the event from `sent` by the committed action, the
completion point is the target when it is intended and the control fresh. -/
theorem completionPoint_of_mem_step {rank : Nat} {profile : BehavioralProfile setup.program}
    {sent : (graph setup).Config} (residual : SourceResidual setup profile rank sent)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank sent = some point)
    {event : (graph setup).EventId} (ready : sent.cut.Ready event)
    {action : (graph setup).Action event} {target : ProtocolState setup.program}
    (stepEq : ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) = PMF.pure target)
    {fresh : (application setup runtime leaks).Control → Prop}
    {stop : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History} {final : (application setup runtime leaks).Control}
    (state : stop.state = some final)
    (inStep : final.execution.application.config ∈ (sent.step event ready action).support) :
    completionPoint setup runtime leaks bounds horizon scheduler rank fresh stop =
      if ProtocolState.Intended setup.program target ∧ fresh final then some target
      else none := by
  have ordered := residual.checkpoint.ordered
  obtain ⟨before, after, beforeDecoded, afterDecoded, reachedPoint⟩ :=
    decodedPoint_step residual event ready action _ inStep
  rw [decodedPoint_eq_of_isPrefix ordered, decoded] at beforeDecoded
  cases Option.some.inj beforeDecoded
  rw [stepEq, PMF.mem_support_pure_iff] at reachedPoint
  subst reachedPoint
  have prefixed := isPrefix_succ_of_mem_step ordered ready inStep
  have prefixDecoded : sourceServicePrefix? setup (rank + 1)
      final.execution.application.config = some after :=
    (decodedPoint_eq_of_isPrefix prefixed).symm.trans afterDecoded
  unfold completionPoint
  rw [state]
  dsimp only
  rw [ite_eq_left prefixed .., prefixDecoded]

open Classical in
/-- **Completion mass is the success probability.** Under a scheduler completing
play, from a history at which the openable-commitment invariant holds for the
binding of rank `rank`, whose configuration `sent` has a source residual and
decodes at `rank` to a point at which the committed action's source action
reaches the intended point `target`, the completion mass under play until the
event completes is one less the probability that terminal play from the
history fails the event, for every property `fresh` of controls that holds
exactly when the event has not failed. -/
theorem expect_completionIndicator_of_openableCommitment
    (players : ∀ player, ((bounds.onePacketMenu runtime leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup runtime leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {candidate : Handle (graph setup)} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {value : L.Val payload} {sent : (graph setup).Config} {ready : sent.cut.Ready event}
    {action : (graph setup).Action event}
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      PublicationResult (L.Val payload)) = .success value)
    {rank : Nat} {profile : BehavioralProfile setup.program}
    (residual : SourceResidual setup profile rank sent) {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank sent = some point)
    (terminalCompleted : ∀ (final : (application setup runtime leaks).Control),
      ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup runtime leaks).terminal (some final) →
      final.execution.application.config = sent →
      event ∈ final.execution.application.config.cut.completed)
    {target : ProtocolState setup.program}
    (stepEq : ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) = PMF.pure target)
    (targetIntended : ProtocolState.Intended setup.program target)
    {fresh : (application setup runtime leaks).Control → Prop}
    (freshIff : ∀ control, fresh control ↔
      ¬ StoreEventFailed control.execution.application.config.store event)
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (holds : OpenableCommitmentInvariant setup runtime leaks bounds horizon scheduler who entry
      message
      event candidate outputEq value sent ready action start.state) :
    expect (((bounds.onePacketMenu runtime leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil
        ((bounds.onePacketMenu runtime leaks).bounded (initialLaw setup) horizon
          scheduler).wellFoundedHistories players
        (LateStopped setup runtime leaks bounds horizon scheduler rank) start)
        (completionIndicator setup runtime leaks bounds horizon scheduler rank fresh) =
      1 - expect (((bounds.onePacketMenu runtime leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralFrom players (2 * horizon + 1) start)
        (fun final => if EventFailedState setup runtime leaks event final.state then 1 else 0) := by
  let menu := bounds.onePacketMenu runtime leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  have horizonBound := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := horizonBound.wellFoundedHistories
  let stopped := LateStopped setup runtime leaks bounds horizon scheduler rank
  let failure := fun final : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    if EventFailedState setup runtime leaks event final.state then (1 : ℝ) else 0
  have failureBounded : ∀ final, |failure final| ≤ 1 := by
    intro final
    simp only [failure]
    split <;> norm_num
  have ordered := residual.checkpoint.ordered
  -- The event's output stays on the store along terminal play.
  have kept : ∀ stop : (menu.protocol (initialLaw setup) horizon scheduler).History,
      ∀ control, stop.state = some control →
      ∀ final ∈ (model.runBehavioralTerminalFrom certificate players stop).support,
        ∃ finalControl, final.state = some finalControl ∧
          ∀ stored, control.execution.application.config.store (.inr event) = some stored →
            finalControl.execution.application.config.store (.inr event) = some stored := by
    intro stop control state
    exact model.runBehavioralTerminalFrom_support_closed certificate players
      (fun reachedState => ∃ reachedControl, reachedState = some reachedControl ∧
        ∀ stored, control.execution.application.config.store (.inr event) = some stored →
          reachedControl.execution.application.config.store (.inr event) = some stored)
      (fun state joint legal target holds reached => by
        obtain ⟨reachedControl, rfl, keeps⟩ := holds
        obtain ⟨next, rfl, _⟩ := (application setup runtime leaks).transition_recall_prefix
          (initialLaw setup) horizon scheduler reachedControl target joint reached
        have keptStore := (keepsStore_step runtime leaks).transition
          (initialLaw setup) horizon scheduler reachedControl next joint reached
        exact ⟨next, rfl, fun stored storedEq =>
          keptStore (.inr event) stored (keeps stored storedEq)⟩)
      stop ⟨control, state, fun _ storedEq => storedEq⟩
  -- At each stop the completion mass is one exactly when terminal play does not fail.
  have pointwise : ∀ stop ∈ (model.runBehavioralUntil certificate players stopped start).support,
      completionIndicator setup runtime leaks bounds horizon scheduler rank fresh stop =
        1 - expect (model.runBehavioralTerminalFrom certificate players stop) failure := by
    intro stop member
    obtain ⟨final, finalState, stepped⟩ := openableCommitment_stop (runtime := runtime) bounds
      horizon scheduler
      certificate players codeEq successful ordered terminalCompleted start holds stop member
    rcases stepped with inStep | ⟨failing, failed, inStep⟩
    · -- Completed by the committed action, a success that stays.
      have output := step_binding_output (outputEq := outputEq) (codeEq := codeEq) inStep
      have notFailed : ¬ StoreEventFailed final.execution.application.config.store event := by
        rintro ⟨stored, storedEq, isFailed⟩
        rw [EventGraph.Config.store_output, output] at storedEq
        cases Option.some.inj storedEq
        have failedResult := (isFailure_cast_binding_iff outputEq _).mp isFailed
        rw [successful] at failedResult
        cases failedResult
      have pointEq := completionPoint_of_mem_step (runtime := runtime) (fresh := fresh) residual
        decoded ready stepEq
        finalState inStep
      rw [ite_eq_left ⟨targetIntended, (freshIff final).mpr notFailed⟩ ..] at pointEq
      have never : expect (model.runBehavioralTerminalFrom certificate players stop) failure =
          0 := by
        rw [expect_congr_on_support (g := fun _ => 0) (fun later laterMember => ?_),
          expect_constant]
        obtain ⟨laterControl, laterState, keeps⟩ := kept stop final finalState later laterMember
        simp only [failure, laterState, EventFailedState]
        rw [ite_eq_right_iff]
        rintro ⟨_, stored, storedEq, isFailed⟩
        rw [keeps _ (by rw [EventGraph.Config.store_output, output])] at storedEq
        cases Option.some.inj storedEq
        have failedResult := (isFailure_cast_binding_iff outputEq _).mp isFailed
        rw [successful] at failedResult
        cases failedResult
      simp only [completionIndicator, pointEq, Option.elim_some, never, sub_zero]
    · -- Completed by a failure, which stays, with no completion point.
      have output := step_binding_output (outputEq := outputEq) (codeEq := codeEq) inStep
      have storeFailed : StoreEventFailed final.execution.application.config.store event :=
        ⟨_, by rw [EventGraph.Config.store_output, output],
          (isFailure_cast_binding_iff outputEq _).mpr failed⟩
      have pointNone := completionPoint_eq_none_of_not_fresh (runtime := runtime) (rank := rank)
        (fresh := fresh)
        finalState (fun freshHere => (freshIff final).mp freshHere storeFailed)
      have always : expect (model.runBehavioralTerminalFrom certificate players stop) failure =
          1 := by
        rw [expect_congr_on_support (g := fun _ => 1) (fun later laterMember => ?_),
          expect_constant]
        obtain ⟨laterControl, laterState, keeps⟩ := kept stop final finalState later laterMember
        obtain ⟨stored, storedEq, isFailed⟩ := storeFailed
        have laterStored := keeps stored storedEq
        have done : event ∈ laterControl.execution.application.config.cut.completed :=
          (laterControl.execution.application.config.output_available event).mp
            (by rw [← EventGraph.Config.store_output, laterStored]; rfl)
        simp only [failure, laterState, EventFailedState]
        rw [ite_eq_left_iff.mpr fun notFailed =>
          (notFailed ⟨done, stored, laterStored, isFailed⟩).elim]
      simp only [completionIndicator, pointNone, Option.elim_none, always, sub_self]
  rw [← model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate horizonBound
      players start,
    model.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate players stopped start,
    expect_bind_tower_bounded _ _ _ failureBounded,
    expect_congr_on_support pointwise]
  have terminalIntegrable : PayoffIntegrable (model.runBehavioralUntil certificate players
      stopped start) (fun stop => expect (model.runBehavioralTerminalFrom certificate players
        stop) failure) :=
    payoffIntegrable_of_bounded _ _ (C := 1) fun stop =>
      expect_abs_le_of_bounded zero_le_one failureBounded
  rw [expect_sub (payoffIntegrable_constant _ 1) terminalIntegrable, expect_constant]

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
    [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
    (covers : bounds.CoversOutputValues)
    (assessment : setup.intendedModel.BehavioralAssessment)
    {target : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).BehavioralAssessment}
    {who : Player}
    {relevant : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationSite who →
      Prop} {LateOption' : Type}
    {profileOf : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationSite who →
      LateOption' → ∀ player,
        (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player}
    {δ : ℝ} {Y : Type}
    (lumping : PendingLumpingOn (runtime := runtime) target who relevant profileOf
      (DecisionFailed (runtime := runtime)) δ Y)
    (site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who)
    (isRelevant : relevant site) {key : LateKey setup runtime leaks}
    (siteKey : lateKey setup runtime leaks who site.1 = some key)
    (option : LateOption') {event : (graph setup).EventId}
    (decided : decidedEvent (runtime := runtime) key = some event) {payload : L.Ty}
    (imageOfBinding : BindingImage (runtime := runtime) (setup := setup) (leaks := leaks) → Y)
    (imageBinding : ∀ state, lumping.image key state =
      imageOfBinding (bindingImage (runtime := runtime) event who payload state))
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    {remaining : Nat} {execution : (application setup runtime leaks).Execution}
    (current : start.state = some ⟨remaining, some who, execution⟩)
    (keptOf : ∀ (history : ((bounds.onePacketMenu runtime leaks).protocol
        (initialLaw setup) horizon scheduler).History)
        (control : (application setup runtime leaks).Control),
      history.state = some control → ForcedState setup runtime leaks who (some control) →
      control.execution.application.config.cut.Ready event →
      control.execution.application.config = execution.application.config →
      (∃ entry rest, control.execution.recall who = execution.recall who ++ entry :: rest ∧
        entry.beforeView = execution.observe (application setup runtime leaks) who) →
      history.state ∈ lumping.keep site key)
    (installed : ∀ player, (onePacketInformation setup runtime leaks bounds horizon
      scheduler).BehavioralPolicy player)
    (agreeLonger : ∀ history : ((bounds.onePacketMenu runtime leaks).protocol
        (initialLaw setup) horizon scheduler).History,
      (∀ control, history.state = some control →
        (execution.recall who).length < (control.execution.recall who).length) →
      ∀ player, installed player
          ((onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf player
            history.trace) =
        profileOf site option player
          ((onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf player
            history.trace))
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (turn : execution.application.publicView.ownTurn? who = some event)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (terminalCompleted : ∀ (final : (application setup runtime leaks).Control),
      ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup runtime leaks).terminal (some final) →
      final.execution.application.config = execution.application.config →
      event ∈ final.execution.application.config.cut.completed)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (forced : ForcedState setup runtime leaks who start.state)
    {fresh : (application setup runtime leaks).Control → Prop}
    (freshIff : ∀ control, fresh control ↔
      ¬ StoreEventFailed control.execution.application.config.store event) :
    ∀ (history : ((bounds.onePacketMenu runtime leaks).protocol
        (initialLaw setup) horizon scheduler).History) (later : Nat)
        (reached : (application setup runtime leaks).Execution),
      history.state = some ⟨later, some who, reached⟩ →
      LateUnsent setup runtime leaks who event execution.application.config (execution.recall who)
        history.state →
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
        ∃ factor : ℝ, ∀ choice ∈ (asIfHonestProfile setup runtime leaks assessment who
            (some (reached.recall who, reached.observe (application setup runtime leaks)
              who))).support,
          ∀ next : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
              horizon scheduler).History,
            next.state = some ⟨later, none, reached.respond (application setup runtime leaks) who
              (slotResponse setup runtime leaks who (reached.recall who)
                (reached.observe (application setup runtime leaks) who) event slot choice)⟩ →
            |expect ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
                scheduler).runBehavioralUntil
                ((bounds.onePacketMenu runtime leaks).bounded (initialLaw setup) horizon
                  scheduler).wellFoundedHistories installed
                (LateStopped setup runtime leaks bounds horizon scheduler rank) next)
                (completionIndicator setup runtime leaks bounds horizon scheduler rank fresh) -
              factor| ≤ (2 * horizon + 1 : ℕ) * δ := by
  intro history later reached state holds sameView extended slot below permitted
  let menu := bounds.onePacketMenu runtime leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  obtain ⟨atSent, extends_, _⟩ := (by simpa only [state] using holds :
    LateUnsent setup runtime leaks who event execution.application.config (execution.recall who)
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
  have forcedHere : ∀ control : (application setup runtime leaks).Control,
      control.execution.application.config = execution.application.config →
      ForcedState setup runtime leaks who (some control) := by
    intro control sameConfig
    rw [current] at forced
    obtain ⟨forcedRank, forcedPoint, forcedOrdered, forcedDecoded, forcedHolds⟩ := forced
    exact ⟨forcedRank, forcedPoint, by rw [sameConfig]; exact forcedOrdered,
      by rw [sameConfig]; exact forcedDecoded, forcedHolds⟩
  -- The committed image, read off the slot alone.
  let committed : BindingImage (runtime := runtime) (setup := setup) (leaks := leaks) :=
    committedImage (runtime := runtime) event who (who, .prepared slot)
      (operationalState setup runtime leaks (some ⟨later, some who, reached⟩))
  refine ⟨1 - expect ((fun law => law.bind (lumping.kernel key option))^[2 *
    horizon + 1]
    (PMF.pure (imageOfBinding committed))) (lumping.failure key), fun choice
      member next
      nextState => ?_⟩
  have covered := onePacket_honest_covered (runtime := runtime) assessment covers traceHere who
    event turnHere choice
    member
  have inMenu := (slotResponse_mem_onePacket_iff setup runtime leaks bounds who (reached.recall who)
    (reached.observe (application setup runtime leaks) who) event node slot below choice
    covered).mpr permitted
  obtain ⟨action, encoded, values⟩ := covered
  obtain ⟨committedValue, successful, _⟩ := values who payload outputEq codeEq node
  obtain ⟨material, transmits, envelope⟩ := slotResponse_transmission setup runtime leaks who
    (reached.recall who) (reached.observe (application setup runtime leaks) who) event node slot
      choice
    action encoded
  have call : material.call.packet = .commitment event (who, .prepared slot) :=
    congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
      message.payload.call) envelope
  -- The commitment invariant and the source step of the committed choice.
  obtain ⟨entry, message, invariant⟩ := openableCommitmentInvariant_slot (runtime := runtime)
    bounds horizon
    scheduler traceHere node readyHere slot choice action encoded successful permitted
    (nextState ▸ next.trace)
  obtain ⟨found, ⟨residualFound⟩⟩ := protocol_sourceResidual (runtime := runtime) (failureProfile
    setup.program)
    menu horizon scheduler traceHere _ rfl
  have foundEq : found = rank := isPrefix_unique residualFound.checkpoint.ordered orderedHere
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
  have acts : ∀ player, ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some who := fun player =>
    (decodedPoint_actor player readyHere pointDecoded).trans owned
  obtain ⟨stepTarget, stepEq⟩ := ProtocolState.step_eq_pure_of_actor who who setup.program point
    (fun _ => some source) (acts who)
  have stepEq' : ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) = PMF.pure stepTarget := by
    rw [decodeEq]
    exact stepEq
  obtain ⟨intended, _, same⟩ := (mem_support_asIfHonestProfile_observe setup runtime leaks
    assessment who
    reached rank orderedHere point decodedHere (reached.recall who) _).mp member
  have legal := intended.2
  change ProtocolView.intendedMenu who setup.program
    (ProtocolState.observe who setup.program point) intended.1 at legal
  rw [same] at legal
  have targetIntended : ProtocolState.Intended setup.program stepTarget := by
    refine ProtocolState.intended_step_of_actors setup.program point _ stepTarget intendedPoint
      (fun player active => ?_) (by rw [stepEq]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
    cases (acts player).symm.trans active
    exact ⟨source, rfl, legal.2⟩
  have massEq := expect_completionIndicator_of_openableCommitment (runtime := runtime) installed
    codeEq
    successful residual decodedHere
    (fun final trace ended same => terminalCompleted final trace ended (same.trans atSent))
      stepEq' targetIntended freshIff next
    (by rw [nextState]; exact invariant)
  -- Play from the commitment is play of the option's profile.
  have nextRecall : (execution.recall who).length <
      ((reached.respond (application setup runtime leaks) who (slotResponse setup runtime leaks who
        (reached.recall who) (reached.observe (application setup runtime leaks) who) event slot
          (some source))).recall who).length := by
    rw [runtime.respond_recall leaks reached who who, ite_eq_left rfl ..,
      List.length_append, List.length_singleton]
    have lengthLe : (execution.recall who).length ≤ (reached.recall who).length :=
      extends_.length_le
    omega
  have samePlay : model.runBehavioralFrom installed (2 * horizon + 1) next =
      model.runBehavioralFrom (profileOf site option) (2 * horizon + 1) next := by
    apply model.runBehavioralFrom_congr (2 * horizon + 1) next
    intro later' path _ player
    apply agreeLonger later'
    intro control laterState
    have rawPath := menu.reaches_raw (initialLaw setup) horizon scheduler path
    have grown := (application setup runtime leaks).reaches_recall_prefix (initialLaw setup) horizon
      scheduler rawPath _ control nextState laterState who
    exact lt_of_lt_of_le nextRecall grown.length_le
  have failedEq : (fun final : (menu.protocol (initialLaw setup) horizon scheduler).History =>
      if EventFailedState setup runtime leaks event final.state then (1 : ℝ) else 0) =
      fun final => if DecisionFailed (runtime := runtime) key final.state then 1 else 0 := by
    funext final
    have same : EventFailedState setup runtime leaks event final.state ↔
        DecisionFailed (runtime := runtime) key final.state := by
      cases final.state with
      | none => simp [EventFailedState, DecisionFailed]
      | some control => simp [EventFailedState, DecisionFailed, decided]
    exact if_congr same rfl rfl
  -- The kept image after the commitment is the committed image.
  have keptNext : next.state ∈ lumping.keep site key := by
    have configEq := (runtime.reactive_respond_application leaks reached who
      (slotResponse setup runtime leaks who (reached.recall who)
        (reached.observe (application setup runtime leaks) who) event slot (some source))).1.trans
          atSent
    refine keptOf next _ nextState (forcedHere _ configEq) ?_ configEq ?_
    · rw [(runtime.reactive_respond_application leaks reached who _).1]
      exact readyHere
    · have respondRecall : ∃ emitted, (reached.respond (application setup runtime leaks) who
          (slotResponse setup runtime leaks who (reached.recall who)
            (reached.observe (application setup runtime leaks) who) event slot (some
              source))).recall
            who = reached.recall who ++
            [⟨reached.observe (application setup runtime leaks) who, slotResponse setup runtime
              leaks who
              (reached.recall who) (reached.observe (application setup runtime leaks) who) event
                slot
              (some source), emitted⟩] := by
        rcases (slotResponse setup runtime leaks who (reached.recall who)
          (reached.observe (application setup runtime leaks) who) event slot (some source)) with
          ⟨transmission⟩
        cases transmission <;>
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte] <;> exact ⟨_, rfl⟩
      obtain ⟨emitted, recallEq⟩ := respondRecall
      rw [recallEq]
      by_cases atStart : reached.recall who = execution.recall who
      · exact ⟨_, [], by rw [atStart], sameView atStart⟩
      · obtain ⟨response, tail, tailEq⟩ := extended atStart
        refine ⟨respondEntry setup runtime leaks execution who response,
          tail ++ [⟨reached.observe (application setup runtime leaks) who, slotResponse setup
            runtime leaks who
            (reached.recall who) (reached.observe (application setup runtime leaks) who) event slot
            (some source), emitted⟩], ?_, rfl⟩
        rw [← tailEq]
        simp
  have fresh' : reached.application.candidates.lookup (who, .prepared slot) = .fresh :=
    onePacket_permitted_fresh (runtime := runtime) (control := ⟨later, some who, reached⟩)
      traceHere who event slot
      permitted
  have succeeds : candidateSucceeds ((application setup runtime leaks).submit reached.application
    who
      material) (who, .prepared slot) payload = true := by
    have bound := slotResponse_of_bind setup runtime leaks who (reached.recall who)
      (reached.observe (application setup runtime leaks) who) event node slot (some source) action
        encoded
    have boundTransmits := transmits
    rw [bound] at boundTransmits
    have materialEq := Option.some.inj boundTransmits.symm
    have submitted : (application setup runtime leaks).submit reached.application who material =
        (reached.respond (application setup runtime leaks) who
          ⟨some ⟨⟨.commitment event (who, .prepared slot), some ⟨payload, committedValue⟩⟩,
            .none⟩⟩).application := by
      rw [materialEq]
      change (application setup runtime leaks).submit reached.application who
        ((runtime.reactiveNormalization leaks).normalize who
          ((application setup runtime leaks).observePlayer reached.application who)
          (ReactiveApplication.ResponseMenu.knownPackets (reached.recall who)
            (reached.observe (application setup runtime leaks) who))
          ⟨⟨.commitment event (who, .prepared slot), match (cast (congrArg
            EventGraph.EventField.Action outputEq) action : PublicationResult (L.Val payload)) with
            | .failure => none
            | .success value => some ⟨payload, value⟩⟩, .none⟩) = _
      rw [(runtime.reactiveNormalization leaks).submit, successful]
      rfl
    have result := submitted_bindingResult runtime leaks reached who event payload slot
      (some ⟨payload, committedValue⟩) fresh'
    unfold candidateSucceeds
    rw [submitted]
    change (match (reached.respond (application setup runtime leaks) who
        ⟨some ⟨⟨.commitment event (who, .prepared slot), some ⟨payload, committedValue⟩⟩,
          .none⟩⟩).application.bindingResult (who, .prepared slot) payload with
      | .success _ => true
      | .failure => false) = true
    rw [result]
    simp [Raw.as?]
  have imageNext : lumping.image key next.state = imageOfBinding committed :=
    by
    rw [imageBinding, nextState, committed_bindingImage (runtime := runtime) bounds history state
      readyHere.1
      (commitStatuses_nil_of_permitted (runtime := runtime) traceHere who event slot permitted
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
        (fun final => if EventFailedState setup runtime leaks event final.state then 1 else 0)| :=
          by
        congr 1
        ring
    _ = _ := abs_sub_comm _ _
    _ ≤ _ := lumped

end Vegas
