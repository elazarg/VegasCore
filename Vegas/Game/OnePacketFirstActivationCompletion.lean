/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCompletionLaw
import Vegas.Pending.ReactiveBindingReceipts

/-! # The stop after a commitment

**A step with an actor is deterministic.** At a source point where some player
acts, the source step is a point mass
(`Vegas.SourceProgram.ProtocolState.step_eq_pure_of_actor`).

**The stop after a commitment.** Let `who` have recorded a packet committing to
a handle whose meaning is fixed at a successful value, sent from a
configuration at which the binding event of rank `rank` is ready, with the
acceptance invariant holding. Under play of any profile until a late stop at
that rank or an extra stop, every stop keeps the sending configuration while
the event is pending, and once the event completes it is one step of the event
from the sending configuration by the action binding that value, with a
successful output, provided the packet settles on that stopped law
(`Vegas.committed_until_config`).
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **A step with an actor is deterministic.** At a source point where some
player acts, every joint choice steps to a single point. -/
theorem step_eq_pure_of_actor (who owner : Player) : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (state : ProtocolState program) → (joint : Player → Option (OwnAction Player L)) →
    ProtocolView.actor who program (observe who program state) = some owner →
    ∃ target, step program state joint = PMF.pure target
  | _, _, .ret _, _, _, acts => by
      simp [ProtocolView.actor] at acts
  | _, _, .sample _ _ _ next, state, joint, acts => by
      cases state with
      | inl config => simp [observe, ProtocolView.actor] at acts
      | inr rest =>
          obtain ⟨target, stepEq⟩ := step_eq_pure_of_actor who owner next rest joint acts
          exact ⟨Sum.inr target, by simp only [step, Sum.elim_inr, stepEq, PMF.pure_map]⟩
  | _, _, .commit _ _ _ _ next, state, joint, acts => by
      cases state with
      | inl config => exact ⟨_, rfl⟩
      | inr rest =>
          obtain ⟨target, stepEq⟩ := step_eq_pure_of_actor who owner next rest joint acts
          exact ⟨Sum.inr target, by simp only [step, Sum.elim_inr, stepEq, PMF.pure_map]⟩
  | _, _, .reveal _ _ _ _ _ _ next, state, joint, acts => by
      cases state with
      | inl config => exact ⟨_, rfl⟩
      | inr rest =>
          obtain ⟨target, stepEq⟩ := step_eq_pure_of_actor who owner next rest joint acts
          exact ⟨Sum.inr target, by simp only [step, Sum.elim_inr, stepEq, PMF.pure_map]⟩

end Vegas.SourceProgram.ProtocolState

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

omit [Fintype Player] in
/-- At a completed prefix, the decoded point is the readout at that prefix. -/
theorem decodedPoint_eq_of_isPrefix {config : (graph setup).Config} {rank : Nat}
    (ordered : config.cut.IsPrefix rank) :
    decodedPoint setup config = sourceServicePrefix? setup rank config := by
  have exists_ordered : ∃ rank, config.cut.IsPrefix rank := ⟨rank, ordered⟩
  unfold decodedPoint
  rw [dite_eq_left_of_eq_true (eq_true exists_ordered), show exists_ordered.choose = rank from
    EventOrder.Cut.IsPrefix.unique exists_ordered.choose_spec ordered]

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- A binding output read at its own type is not a failure exactly when its
result is not a failure. -/
private theorem isFailure_cast {kind : EventGraph.EventField Player L} {owner : Player}
    {payload : L.Ty} (kindEq : kind = .binding owner payload)
    (result : PublicationResult (L.Val payload)) :
    kind.IsFailure (cast (congrArg EventGraph.EventField.Value kindEq.symm) result) ↔
      result = .failure := by
  subst kindEq
  rfl

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- Reading a stored binding output at its own type recovers its result. -/
private theorem get_cast {kind : EventGraph.EventField Player L} {owner : Player}
    {payload : L.Ty} (kindEq : kind = .binding owner payload)
    (result : PublicationResult (L.Val payload)) :
    cast (congrArg (fun field : EventGraph.EventField Player L => Option field.Value) kindEq)
      (some (cast (congrArg EventGraph.EventField.Value kindEq.symm) result)) = some result := by
  subst kindEq
  rfl

variable (setup runtime leaks bounds horizon scheduler) in
/-- After a recorded commitment of candidate sent for event from sent:
the acceptance invariant, the meaning of candidate fixed at raw, and, once
the event has completed, the configuration is one step of the event from
sent. -/
private def CommitInvariant (who : Player) (entry : (application setup runtime leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (sent : (graph setup).Config) (ready : sent.cut.Ready event)
    (candidate : Handle (graph setup)) (raw : Raw L) :
    (application setup runtime leaks).ProtocolState → Prop
  | none => False
  | some control =>
      AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry message event sent
          (some control) ∧
        control.execution.application.candidates.lookup candidate = .openable raw ∧
        (event ∈ control.execution.application.config.cut.completed →
          ∃ action, control.execution.application.config ∈
            (sent.step event ready action).support)

/-- The commitment invariant passes along every transition from a state where
the event of rank rank has not completed. -/
private theorem commitInvariant_transition {who : Player}
    {entry : (application setup runtime leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} {ready : sent.cut.Ready event}
    {candidate : Handle (graph setup)} {raw : Raw L} {rank : Nat}
    (ordered : sent.cut.IsPrefix rank) (before after : (application setup runtime
      leaks).ProtocolState)
    (going : ∀ control, before = some control →
      ¬ control.execution.application.config.cut.IsPrefix (rank + 1))
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Legal before joint)
    (holds : CommitInvariant setup runtime leaks bounds horizon scheduler who entry message event
      sent
      ready candidate raw before)
    (reached : after ∈ (((bounds.onePacketMenu runtime leaks).protocol
      (initialLaw setup) horizon scheduler).step before ⟨joint, legal⟩).support) :
    CommitInvariant setup runtime leaks bounds horizon scheduler who entry message event sent ready
      candidate raw after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨invariant, fixed, completion⟩ := holds
      have afterInvariant := acceptanceInvariant_transition (runtime := runtime) bounds horizon
        scheduler who entry
        message event sent (some control) after joint legal invariant reached
      cases after with
      | none => exact afterInvariant.elim
      | some next =>
          have kept := (keepsFixedCandidates_step runtime leaks).transition
            (initialLaw setup) horizon scheduler control next joint reached
          refine ⟨afterInvariant, ?_, fun completedNext => ?_⟩
          · rw [kept candidate (by rw [fixed]; exact fun impossible => by cases impossible), fixed]
          · have pending : event ∉ control.execution.application.config.cut.completed := by
              intro done
              obtain ⟨action, member⟩ := completion done
              apply going control rfl
              have rankEq := (ready_iff_rank setup sent rank ordered event).mp ready
              rw [sent.step_cut event ready action _ member]
              exact ordered.complete_at event ready rankEq
            have atSent := invariant.2.2.2.2.2.1 pending
            rcases transition_configStep (initialLaw setup) horizon scheduler
              control next joint
                reached with same | ⟨other, otherReady, action, member⟩
            · rw [same] at completedNext
              exact (pending completedNext).elim
            · revert otherReady member
              rw [atSent]
              intro otherReady member
              rw [atSent] at pending
              rw [sent.step_cut other otherReady action _ member, EventOrder.Cut.mem_complete]
                at completedNext
              rcases completedNext with rfl | earlier
              · exact ⟨action, member⟩
              · exact (pending earlier).elim

/-- Arbitrary early stopping retains the original configuration while the
committed binding is pending. Once it completes, an accepted fixed-value call
gives exactly its successful compiled event step, without a completion contract. -/
theorem committed_until_config
    (certificate : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu runtime leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (extraStop : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).History → Prop)
    {who : Player} {entry : (application setup runtime leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} (ready : sent.cut.Ready event) {rank : Nat}
    (ordered : sent.cut.IsPrefix rank) {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    {candidate : Handle (graph setup)} (call : message.payload.call = .commitment event candidate)
    {value : L.Val payload} (action : (graph setup).Action event)
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      PublicationResult (L.Val payload)) = .success value)
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control)
    (invariant : AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry
      message event
      sent (some control))
    (atSent : control.execution.application.config = sent)
    (fixed : control.execution.application.candidates.lookup candidate =
      .openable ⟨payload, value⟩)
    (settles : ∀ stopped ∈ (((bounds.onePacketMenu runtime leaks).information
        (initialLaw setup) horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup runtime leaks bounds horizon scheduler rank history ∨
          extraStop history) start).support,
      ∀ final, stopped.state = some final → RecordsEntry setup runtime leaks who entry (some
        final) →
        event ∈ final.execution.application.config.cut.completed →
          (message.id, true) ∈ final.execution.receipts) :
    ∀ stop ∈ (((bounds.onePacketMenu runtime leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup runtime leaks bounds horizon scheduler rank history ∨
          extraStop history) start).support,
      ∃ final, stop.state = some final ∧
        (event ∉ final.execution.application.config.cut.completed →
          final.execution.application.config = sent) ∧
        (event ∈ final.execution.application.config.cut.completed →
          final.execution.application.config ∈ (sent.step event ready action).support ∧
            OutputSucceeded final.execution.application.config.store event) := by
  intro stop member
  let menu := bounds.onePacketMenu runtime leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  have holds : CommitInvariant setup runtime leaks bounds horizon scheduler who entry message
    event sent
      ready candidate ⟨payload, value⟩ start.state := by
    rw [current]
    refine ⟨invariant, fixed, fun done => ?_⟩
    rw [atSent] at done
    exact (ready.1 done).elim
  have reachedInvariant := model.runBehavioralUntil_support_closed certificate players
    (fun history => LateStopped setup runtime leaks bounds horizon scheduler rank history ∨
      extraStop history)
    (CommitInvariant setup runtime leaks bounds horizon scheduler who entry message event sent ready
      candidate ⟨payload, value⟩)
    (fun history going _ joint legal target holds reached =>
      commitInvariant_transition (runtime := runtime) ordered history.state target
        (fun control state prefixed => going (Or.inl ⟨control, state, prefixed⟩)) joint legal holds
        reached)
    start holds stop member
  cases state : stop.state with
  | none =>
      rw [state] at reachedInvariant
      exact reachedInvariant.elim
  | some final =>
      rw [state] at reachedInvariant
      obtain ⟨finalInvariant, finalFixed, completion⟩ := reachedInvariant
      obtain ⟨⟨finalTrace⟩, records, emitted, _, _, stable, settled⟩ := finalInvariant
      have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
          scheduler).Trace (some final) :=
        menu.toRawTrace (initialLaw setup) horizon scheduler finalTrace
      refine ⟨final, rfl, stable, fun done => ?_⟩
      obtain ⟨found, stepMember⟩ := completion done
      have receipt := settles stop member final state records done
      have succeeded := settled receipt
      refine ⟨?_, succeeded⟩
      -- The completion's action binds the committed value.
      have facts := legalFacts setup leaks horizon scheduler final rawTrace
      have initialized : initialLaw setup =
          (setup.initialLaw.map setup.eventInputs).map (State.initial (graph := graph setup)) := by
        simp only [initialLaw, serviceInitialLaw, PMF.map_comp, Function.comp_def]
      have bindingTrace := rawTrace
      rw [initialized] at bindingTrace
      have recorded := runtime.bindingReceipts_history leaks
        (setup.initialLaw.map setup.eventInputs) horizon scheduler final bindingTrace
      obtain ⟨published, onLedger, identified, selected⟩ := recorded message.id receipt
      obtain ⟨earlier, later, split⟩ := records
      have output : message ∈ (application setup runtime leaks).outputs
          (final.execution.recall who) := by
        rw [split]
        exact List.mem_filterMap.mpr ⟨entry, by simp, emitted⟩
      rw [← facts.inputs who] at output
      have input := (List.mem_filter.mp output).1
      have samePublished := (facts.unique.inputs message input).ledger published onLedger
        identified
      subst samePublished
      have acceptedEq := selected event candidate call
      have outputs := step_binding_output (outputEq := outputEq) (codeEq := codeEq) stepMember
      generalize resultEq : (cast (congrArg EventGraph.EventField.Action outputEq) found :
        PublicationResult (L.Val payload)) = result at outputs
      cases result with
      | failure =>
          exfalso
          obtain ⟨stored, storedEq, notFailed⟩ := succeeded
          rw [EventGraph.Config.store_output, outputs] at storedEq
          cases Option.some.inj storedEq
          exact notFailed ((isFailure_cast outputEq _).mpr rfl)
      | success read =>
          have reads : (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
              (.binding owner payload)).get? final.execution.application.config.store =
              some (.success read) := by
            change cast _ (final.execution.application.config.outputs event) = _
            rw [outputs]
            exact get_cast outputEq _
          obtain ⟨handle', acceptedHandle, _, meaning⟩ :=
            facts.binding.success_provenance _ read reads
          have handleEq : handle' = candidate :=
            Option.some.inj (acceptedHandle.symm.trans acceptedEq)
          subst handleEq
          rw [finalFixed] at meaning
          injection meaning with rawEq
          injection rawEq with _ valueEq
          subst valueEq
          have actionEq : found = action :=
            (cast_inj _).mp (resultEq.trans successful.symm)
          rw [← actionEq]
          exact stepMember

end Vegas
