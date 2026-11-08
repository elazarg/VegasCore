/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOpenableCommitment

/-! # The completion point after a commitment to an openable value

**One target.** After `who` commits its binding to an openable value, every
stop of play until the event completes has no completion point or the one the
committed action reaches from the decoded point
(`Vegas.completionPoint_of_openableCommitment`): the event completes by that
action or by a failure.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- **One target.** Under a scheduler completing play, from a history at which
the openable-commitment invariant holds for the binding of rank `rank`, whose
configuration `sent` has a source residual and decodes at `rank` to a point at
which the committed action's source action reaches the intended point
`target`, every stop of play until the event completes has no completion point
or `target`, for every property `fresh` of controls that fails when the event
has failed. -/
theorem completionPoint_of_openableCommitment
    (certificate : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu timeouts leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup timeouts leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {candidate : Handle (graph setup)} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {value : L.Val payload} {sent : (graph setup).Config} {ready : sent.cut.Ready event}
    {action : (graph setup).Action event}
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      Option (PublicationResult (L.Val payload))) = some (.success value))
    {rank : Nat} {profile : BehavioralProfile setup.program}
    (residual : SourceResidual setup profile rank sent) {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank sent = some point)
    (terminalCompleted : ∀ (final : (application setup timeouts leaks).Control),
      ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup timeouts leaks).terminal (some final) →
      final.execution.application.config = sent →
      event ∈ final.execution.application.config.cut.completed)
    {target : ProtocolState setup.program}
    (stepEq : ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) = PMF.pure target)
    {fresh : (application setup timeouts leaks).Control → Prop}
    (failedStale : ∀ control, StoreEventFailed control.execution.application.config.store event →
      ¬ fresh control)
    (start : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (holds : OpenableCommitmentInvariant setup timeouts leaks bounds horizon scheduler who entry
      message
      event candidate outputEq value sent ready action start.state) :
    ∀ stop ∈ (((bounds.onePacketMenu timeouts leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (LateStopped setup timeouts leaks bounds horizon scheduler rank) start).support,
      completionPoint setup timeouts leaks bounds horizon scheduler rank fresh stop = none ∨
        completionPoint setup timeouts leaks bounds horizon scheduler rank fresh stop = some target
          := by
  classical
  intro stop member
  obtain ⟨final, finalState, completed⟩ := openableCommitment_stop (timeouts := timeouts) bounds
    horizon scheduler certificate players codeEq successful residual.checkpoint.ordered
      terminalCompleted start holds stop member
  rcases completed with failed | ⟨primary, inStep, drained⟩
  · left
    have stale := failedStale final failed
    unfold completionPoint
    rw [finalState]
    dsimp only
    split
    · split
      · split
        · rename_i good
          exact (stale good.2).elim
        · rfl
      · rfl
    · rfl
  · unfold completionPoint
    rw [finalState]
    dsimp only
    split
    · split
      · rename_i found decodedFinal
        split
        · rename_i good
          have clear := defaulted_eq_empty_of_decodedIntended decodedFinal good.1
          have primaryClear : primary.config.defaulted = ∅ := by
            rw [← primary.drain_defaulted, ← drained]
            exact clear
          have same : final.execution.application.config = primary.config := by
            rw [drained, primary.drain_eq_of_empty primaryClear]
          have actualStep : final.execution.application.config ∈
              (sent.step event ready action).support := same.symm ▸ inStep
          obtain ⟨before, after, beforeDecoded, afterDecoded, reachedPoint⟩ :=
            decodedPoint_step residual event ready action _ actualStep
          have beforeRead : decodedPoint setup sent = some point :=
            (decodedPoint_eq residual).trans (residual.decode.symm.trans decoded)
          rw [beforeRead] at beforeDecoded
          cases Option.some.inj beforeDecoded
          rw [stepEq, PMF.mem_support_pure_iff] at reachedPoint
          subst reachedPoint
          have samePoint : found = after := Option.some.inj (decodedFinal.symm.trans afterDecoded)
          exact Or.inr (congrArg some samePoint)
        · exact Or.inl rfl
      · exact Or.inl rfl
    · exact Or.inl rfl

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem cast_option_some {A B : Type} (same : A = B) (value : A) :
    cast (congrArg Option same) (some value) = some (cast same value) := by
  cases same
  rfl

omit [Fintype Player] in
/-- **A binding its owner never sent for fails.** Along a history of the
supplied runtime, a completed binding of `who` for which the recall of `who`
records no submission holds a failure: a success would have an accepted handle
of `who`, which an emitted commitment of `who` signs. -/
theorem storeEventFailed_of_unrecorded {control : (application setup timeouts leaks).Control}
    (trace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace
      (some control))
    {who : Player} {event : (graph setup).EventId} {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (done : event ∈ control.execution.application.config.cut.completed)
    (unrecorded : (eventRecorded timeouts) leaks (control.execution.logs who) event =
      false) :
    StoreEventFailed control.execution.application.config.store event := by
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have signed := signedCommitments_history timeouts leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler trace
  obtain ⟨stored, storedEq⟩ := Option.isSome_iff_exists.mp
    ((control.execution.application.config.output_available event).mpr done)
  generalize resultEq : (cast (congrArg EventGraph.EventField.Value outputEq) stored :
    PublicationResult (L.Val payload)) = result
  cases result with
  | failure =>
      apply storeEventFailed_of_ref _ event ⟨.inr event, outputEq⟩ rfl _ rfl
      simp only [EventGraph.FieldRef.get?]
      change cast _ (control.execution.application.config.outputs event) = _
      rw [storedEq, cast_option_some (congrArg EventGraph.EventField.Value outputEq), resultEq]
  | success read =>
      exfalso
      have reads : (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
          (.binding who payload)).get? control.execution.application.config.store =
          some (.success read) := by
        simp only [EventGraph.FieldRef.get?]
        change cast _ (control.execution.application.config.outputs event) = _
        rw [storedEq, cast_option_some (congrArg EventGraph.EventField.Value outputEq), resultEq]
      obtain ⟨handle, accepted, ownerEq, _⟩ := facts.binding.success_provenance _ read reads
      obtain ⟨message, output, call⟩ := signed.acceptedSigned event handle accepted
      rw [ownerEq] at output
      obtain ⟨entry, member, emitted⟩ := List.mem_filterMap.mp output
      obtain ⟨_, material, sent, packet⟩ := signed.emissions who entry member message emitted
      have recorded := ((eventRecorded_iff timeouts) leaks _ event).mpr ⟨entry, member, ?_⟩
      · rw [unrecorded] at recorded
        cases recorded
      · unfold EventGraphRuntime.submittedEvent?
        rw [sent]
        change material.call.packet.event? (graph setup) = some event
        rw [← packet, call]
        rfl

section Payoffs

variable (setup timeouts leaks bounds horizon scheduler)

/-- **The centered completion value** of a stop: the value at its completion
point less `center`, and zero without one. -/
def centeredCompletion (rank : Nat) (fresh : (application setup timeouts leaks).Control → Prop)
    (value : ProtocolState setup.program → ℝ) (center : ℝ)
    (stop : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History) : ℝ :=
  (completionPoint setup timeouts leaks bounds horizon scheduler rank fresh stop).elim 0
    fun point => value point - center

/-- **The completion mass** of a stop: one when it has a completion point. -/
def completionIndicator (rank : Nat) (fresh : (application setup timeouts leaks).Control → Prop)
    (stop : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History) : ℝ :=
  (completionPoint setup timeouts leaks bounds horizon scheduler rank fresh stop).elim 0 fun _ => 1

end Payoffs

/-- The completion point reads only the state. -/
theorem completionPoint_congr_state {rank : Nat} {fresh : (application setup timeouts
  leaks).Control → Prop}
    {first second : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).History} (same : first.state = second.state) :
    completionPoint setup timeouts leaks bounds horizon scheduler rank fresh first =
      completionPoint setup timeouts leaks bounds horizon scheduler rank fresh second := by
  unfold completionPoint LateStopped
  rw [same]

omit [Fintype Player] in
/-- Public views with the same ready events give every player the same turn. -/
theorem ownTurn?_eq_of_eventReady_iff {first second : PublicView (graph setup)}
    (same : ∀ event, first.EventReady event ↔ second.EventReady event) (who : Player) :
    first.ownTurn? who = second.ownTurn? who := by
  classical
  unfold PublicView.ownTurn?
  congr 1
  funext event
  simp only [same event]

/-- **The centered completion value after a commitment to an openable value.**
Under the hypotheses of `Vegas.completionPoint_of_openableCommitment`, the
centered completion value under play until the event completes is the value at
the target less `center` times the completion mass. -/
theorem expect_centeredCompletion_of_openableCommitment
    (certificate : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu timeouts leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup timeouts leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {candidate : Handle (graph setup)} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {value : L.Val payload} {sent : (graph setup).Config} {ready : sent.cut.Ready event}
    {action : (graph setup).Action event}
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      Option (PublicationResult (L.Val payload))) = some (.success value))
    {rank : Nat} {profile : BehavioralProfile setup.program}
    (residual : SourceResidual setup profile rank sent) {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank sent = some point)
    (terminalCompleted : ∀ (final : (application setup timeouts leaks).Control),
      ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup timeouts leaks).terminal (some final) →
      final.execution.application.config = sent →
      event ∈ final.execution.application.config.cut.completed)
    {target : ProtocolState setup.program}
    (stepEq : ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) = PMF.pure target)
    {fresh : (application setup timeouts leaks).Control → Prop}
    (failedStale : ∀ control, StoreEventFailed control.execution.application.config.store event →
      ¬ fresh control)
    (start : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (holds : OpenableCommitmentInvariant setup timeouts leaks bounds horizon scheduler who entry
      message
      event candidate outputEq value sent ready action start.state)
    (pointValue : ProtocolState setup.program → ℝ) (center : ℝ) :
    expect (((bounds.onePacketMenu timeouts leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (LateStopped setup timeouts leaks bounds horizon scheduler rank) start)
        (centeredCompletion setup timeouts leaks bounds horizon scheduler rank fresh pointValue
          center) =
      (pointValue target - center) *
        expect (((bounds.onePacketMenu timeouts leaks).information (initialLaw setup)
          horizon scheduler).runBehavioralUntil certificate players
          (LateStopped setup timeouts leaks bounds horizon scheduler rank) start)
          (completionIndicator setup timeouts leaks bounds horizon scheduler rank fresh) := by
  rw [← expect_const_mul]
  apply expect_congr_on_support
  intro stop member
  rcases completionPoint_of_openableCommitment (timeouts := timeouts) certificate players codeEq
    successful
      residual decoded terminalCompleted stepEq failedStale start holds stop member with none_ |
        some_
  · simp only [centeredCompletion, completionIndicator, none_, Option.elim_none, mul_zero]
  · simp only [centeredCompletion, completionIndicator, some_, Option.elim_some, mul_one]

variable (setup timeouts leaks) in
/-- **The owner has not sent.** The configuration is `sent`, the recall of
`who` extends `past`, and it records no submission for `event`. -/
def LateUnsent (who : Player) (event : (graph setup).EventId) (sent : (graph setup).Config)
    (past : List (application setup timeouts leaks).PlayerEntry) :
    (application setup timeouts leaks).ProtocolState → Prop
  | none => False
  | some control => control.execution.application.config = sent ∧
      past <+: control.execution.logs who ∧
      (eventRecorded timeouts) leaks (control.execution.logs who) event = false

omit [Fintype Player] in
/-- A transition at which `who` does not respond keeps the recall of `who`. -/
theorem recall_eq_of_transition {initial : PMF (application setup timeouts leaks).State} {horizon :
  Nat}
    {scheduler : (application setup timeouts leaks).Scheduler} (who : Player)
    (before : (application setup timeouts leaks).Control) (actorNe : before.actor ≠ some who)
    (joint : Player → Option (application setup timeouts leaks).Action)
    {after : (application setup timeouts leaks).Control}
    (reached : some after ∈ ((application setup timeouts leaks).transition initial horizon scheduler
      (some before) joint).support) :
    after.execution.logs who = before.execution.logs who := by
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some responder =>
      cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
      exact (application setup timeouts leaks).respond_recall_other execution responder who
        (fun same => actorNe (by rw [same])) _
  | none =>
      cases remaining with
      | zero =>
          cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
          rfl
      | succ remaining =>
          obtain ⟨command, _, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨next, moved, same⟩ := PMF.support_map .. ▸ supported
          cases Option.some.inj same
          change next.logs who = execution.logs who
          rw [(application setup timeouts leaks).environmentStep_recall execution next command
            moved]

omit [Fintype Player] in
/-- **Steps of others keep the owner unsent or fail the event.** From a state at
which `who` has not sent for its binding `event`, the ready event
at `sent`, a transition at which `who` does not respond keeps `who` unsent, or
completes the event with a failure. -/
theorem lateUnsent_transition_other {who : Player} {event : (graph setup).EventId}
    {sent : (graph setup).Config} {past : List (application setup timeouts leaks).PlayerEntry}
    (ready : sent.cut.Ready event)
    {payload : L.Ty} (outputEq : (graph setup).outputLayout event = .binding who payload)
    (before : (application setup timeouts leaks).Control)
    (holds : LateUnsent setup timeouts leaks who event sent past (some before))
    (actorNe : before.actor ≠ some who)
    (joint : Player → Option (application setup timeouts leaks).Action)
    {after : (application setup timeouts leaks).ProtocolState}
    (reached : after ∈ ((application setup timeouts leaks).transition (initialLaw setup) horizon
      scheduler
      (some before) joint).support)
    (afterTrace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace
      after) :
    LateUnsent setup timeouts leaks who event sent past after ∨
      ∃ control : (application setup timeouts leaks).Control, after = some control ∧
        event ∈ control.execution.application.config.cut.completed ∧
        StoreEventFailed control.execution.application.config.store event := by
  obtain ⟨atSent, extends_, unrecorded⟩ := holds
  subst atSent
  obtain ⟨next, rfl, _⟩ := (application setup timeouts leaks).transition_recall_prefix (initialLaw
    setup)
    horizon scheduler before after joint reached
  have recallEq := recall_eq_of_transition (timeouts := timeouts) who before actorNe joint reached
  have path := reactive_protocol_graph_steps timeouts leaks (initialLaw setup) horizon scheduler
    before next joint reached
  by_cases completed : event ∈ next.execution.application.config.cut.completed
  · right
    refine ⟨next, rfl, completed,
      storeEventFailed_of_unrecorded (timeouts := timeouts) afterTrace outputEq completed ?_⟩
    rw [recallEq]
    exact unrecorded
  · left
    have same := EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
      (fun other otherReady =>
        setup.eventGraph.sequentialize_ready_unique _ otherReady ready) completed path
    exact ⟨same, recallEq ▸ extends_, by rw [recallEq]; exact unrecorded⟩

end Vegas
