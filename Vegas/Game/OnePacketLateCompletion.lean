/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketOpenableCommitment
import Vegas.Game.OnePacketLateSending
import Vegas.Game.OnePacketPrescribedCompletion
import Interaction.ReactiveStoppedState
import GameTheoryExtensions.Analysis.Protocol.StoppedExitBound

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
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **One target.** Under a scheduler completing play, from a history at which
the openable-commitment invariant holds for the binding of rank `rank`, whose
configuration `sent` has a source residual and decodes at `rank` to a point at
which the committed action's source action reaches the intended point
`target`, every stop of play until the event completes has no completion point
or `target`, for every property `fresh` of controls that fails when the event
has failed. -/
theorem completionPoint_of_openableCommitment
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
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
    (terminalCompleted : ∀ (final : (application setup leaks).Control),
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace (some final) →
      (application setup leaks).terminal (some final) →
      final.execution.application.config = sent →
      event ∈ final.execution.application.config.cut.completed)
    {target : ProtocolState setup.program}
    (stepEq : ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) = PMF.pure target)
    {fresh : (application setup leaks).Control → Prop}
    (failedStale : ∀ control, StoreEventFailed control.execution.application.config.store event →
      ¬ fresh control)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (holds : OpenableCommitmentInvariant setup leaks bounds horizon scheduler who entry message
      event candidate outputEq value sent ready action start.state) :
    ∀ stop ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (LateStopped setup leaks bounds horizon scheduler rank) start).support,
      completionPoint setup leaks bounds horizon scheduler rank fresh stop = none ∨
        completionPoint setup leaks bounds horizon scheduler rank fresh stop = some target := by
  classical
  intro stop member
  have ordered := residual.checkpoint.ordered
  obtain ⟨final, finalState, stepped⟩ := openableCommitment_stop bounds horizon scheduler
    certificate players codeEq successful ordered terminalCompleted start holds stop member
  rcases stepped with inStep | ⟨failing, failed, inStep⟩
  · -- The event completes by the committed action, at the target.
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
    rw [finalState]
    dsimp only
    rw [ite_eq_left prefixed .., prefixDecoded]
    dsimp only
    by_cases good : ProtocolState.Intended setup.program after ∧ fresh final
    · exact Or.inr (by rw [ite_eq_left good ..])
    · exact Or.inl (by rw [ite_eq_right good ..])
  · -- The event fails, so the control is not fresh.
    left
    have output := step_binding_output (outputEq := outputEq) (codeEq := codeEq) inStep
    have storeFailed : StoreEventFailed final.execution.application.config.store event :=
      ⟨_, by rw [EventGraph.Config.store_output, output],
        (isFailure_cast_binding_iff outputEq _).mpr failed⟩
    have stale := failedStale final storeFailed
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

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem cast_option_some {A B : Type} (same : A = B) (value : A) :
    cast (congrArg Option same) (some value) = some (cast same value) := by
  cases same
  rfl

omit [Fintype Player] in
/-- **A binding its owner never sent for fails.** Along a history of the
default runtime, a completed binding of `who` for which the recall of `who`
records no submission holds a failure: a success would have an accepted handle
of `who`, which an emitted commitment of `who` signs. -/
theorem storeEventFailed_of_unrecorded {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    {who : Player} {event : (graph setup).EventId} {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (done : event ∈ control.execution.application.config.cut.completed)
    (unrecorded : (runtime setup).eventRecorded leaks (control.execution.recall who) event =
      false) :
    StoreEventFailed control.execution.application.config.store event := by
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have signed := signedCommitments_history (runtime setup) leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler trace
  obtain ⟨stored, storedEq⟩ := Option.isSome_iff_exists.mp
    ((control.execution.application.config.output_available event).mpr done)
  generalize resultEq : (cast (congrArg EventGraph.EventField.Value outputEq) stored :
    PublicationResult (L.Val payload)) = result
  have storedCast : stored = cast (congrArg EventGraph.EventField.Value outputEq.symm) result := by
    rw [← resultEq]
    simp only [cast_cast, cast_eq]
  cases result with
  | failure =>
      refine ⟨stored, by rw [EventGraph.Config.store_output, storedEq], ?_⟩
      rw [storedCast]
      exact (isFailure_cast_binding_iff outputEq _).mpr rfl
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
      have recorded := (history_eventRecorded_iff trace who event).mpr
        ⟨message, output, by rw [call]; rfl⟩
      rw [unrecorded] at recorded
      cases recorded

section Payoffs

variable (setup leaks bounds horizon scheduler)

/-- **The centered completion value** of a stop: the value at its completion
point less `center`, and zero without one. -/
def centeredCompletion (rank : Nat) (fresh : (application setup leaks).Control → Prop)
    (value : ProtocolState setup.program → ℝ) (center : ℝ)
    (stop : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) : ℝ :=
  (completionPoint setup leaks bounds horizon scheduler rank fresh stop).elim 0
    fun point => value point - center

/-- **The completion mass** of a stop: one when it has a completion point. -/
def completionIndicator (rank : Nat) (fresh : (application setup leaks).Control → Prop)
    (stop : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) : ℝ :=
  (completionPoint setup leaks bounds horizon scheduler rank fresh stop).elim 0 fun _ => 1

end Payoffs

/-- The completion point reads only the state. -/
theorem completionPoint_congr_state {rank : Nat} {fresh : (application setup leaks).Control → Prop}
    {first second : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History} (same : first.state = second.state) :
    completionPoint setup leaks bounds horizon scheduler rank fresh first =
      completionPoint setup leaks bounds horizon scheduler rank fresh second := by
  unfold completionPoint
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
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
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
    (terminalCompleted : ∀ (final : (application setup leaks).Control),
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace (some final) →
      (application setup leaks).terminal (some final) →
      final.execution.application.config = sent →
      event ∈ final.execution.application.config.cut.completed)
    {target : ProtocolState setup.program}
    (stepEq : ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event action) = PMF.pure target)
    {fresh : (application setup leaks).Control → Prop}
    (failedStale : ∀ control, StoreEventFailed control.execution.application.config.store event →
      ¬ fresh control)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (holds : OpenableCommitmentInvariant setup leaks bounds horizon scheduler who entry message
      event candidate outputEq value sent ready action start.state)
    (pointValue : ProtocolState setup.program → ℝ) (center : ℝ) :
    expect (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (LateStopped setup leaks bounds horizon scheduler rank) start)
        (centeredCompletion setup leaks bounds horizon scheduler rank fresh pointValue center) =
      (pointValue target - center) *
        expect (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
          horizon scheduler).runBehavioralUntil certificate players
          (LateStopped setup leaks bounds horizon scheduler rank) start)
          (completionIndicator setup leaks bounds horizon scheduler rank fresh) := by
  rw [← expect_const_mul]
  apply expect_congr_on_support
  intro stop member
  rcases completionPoint_of_openableCommitment certificate players codeEq successful
      residual decoded terminalCompleted stepEq failedStale start holds stop member with none_ |
        some_
  · simp only [centeredCompletion, completionIndicator, none_, Option.elim_none, mul_zero]
  · simp only [centeredCompletion, completionIndicator, some_, Option.elim_some, mul_one]

variable (setup leaks) in
/-- **The owner has not sent.** The configuration is `sent`, the recall of
`who` extends `past`, and it records no submission for `event`. -/
def LateUnsent (who : Player) (event : (graph setup).EventId) (sent : (graph setup).Config)
    (past : List (application setup leaks).PlayerEntry) :
    (application setup leaks).ProtocolState → Prop
  | none => False
  | some control => control.execution.application.config = sent ∧
      past <+: control.execution.recall who ∧
      (runtime setup).eventRecorded leaks (control.execution.recall who) event = false

omit [Fintype Player] in
/-- A transition at which `who` does not respond keeps the recall of `who`. -/
theorem recall_eq_of_transition {initial : PMF (application setup leaks).State} {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} (who : Player)
    (before : (application setup leaks).Control) (actorNe : before.actor ≠ some who)
    (joint : Player → Option (application setup leaks).Action)
    {after : (application setup leaks).Control}
    (reached : some after ∈ ((application setup leaks).transition initial horizon scheduler
      (some before) joint).support) :
    after.execution.recall who = before.execution.recall who := by
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some responder =>
      cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
      exact (application setup leaks).respond_recall_other execution responder who
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
          change next.recall who = execution.recall who
          rw [(application setup leaks).environmentStep_recall execution next command moved]

omit [Fintype Player] in
/-- **Steps of others keep the owner unsent or fail the event.** From a state at
which `who` has not sent for its binding `event`, the ready event of rank `rank`
at `sent`, a transition at which `who` does not respond keeps `who` unsent, or
completes the event with a failure. -/
theorem lateUnsent_transition_other {who : Player} {event : (graph setup).EventId}
    {sent : (graph setup).Config} {past : List (application setup leaks).PlayerEntry}
    {rank : Nat} (ordered : sent.cut.IsPrefix rank) (ready : sent.cut.Ready event)
    {payload : L.Ty} (outputEq : (graph setup).outputLayout event = .binding who payload)
    (before : (application setup leaks).Control)
    (holds : LateUnsent setup leaks who event sent past (some before))
    (actorNe : before.actor ≠ some who)
    (joint : Player → Option (application setup leaks).Action)
    {after : (application setup leaks).ProtocolState}
    (reached : after ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler
      (some before) joint).support)
    (afterTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      after) :
    LateUnsent setup leaks who event sent past after ∨
      ∃ control : (application setup leaks).Control, after = some control ∧
        control.execution.application.config.cut.IsPrefix (rank + 1) ∧
        StoreEventFailed control.execution.application.config.store event := by
  obtain ⟨atSent, extends_, unrecorded⟩ := holds
  subst atSent
  obtain ⟨next, rfl, _⟩ := (application setup leaks).transition_recall_prefix (initialLaw setup)
    horizon scheduler before after joint reached
  have recallEq := recall_eq_of_transition who before actorNe joint reached
  rcases transition_configStep (initialLaw setup) horizon scheduler before next joint reached with
    same | ⟨completed, completedReady, action, member⟩
  · left
    exact ⟨same, recallEq ▸ extends_, by rw [recallEq]; exact unrecorded⟩
  · right
    have eventEq : completed = event := ready_unique (setup := setup) _ completedReady ready
    subst eventEq
    have done : completed ∈ next.execution.application.config.cut.completed := by
      rw [before.execution.application.config.step_cut completed completedReady action _ member]
      exact Finset.mem_insert_self _ _
    refine ⟨next, rfl, isPrefix_succ_of_mem_step ordered completedReady member,
      storeEventFailed_of_unrecorded afterTrace outputEq done ?_⟩
    rw [recallEq]
    exact unrecorded

end Vegas
