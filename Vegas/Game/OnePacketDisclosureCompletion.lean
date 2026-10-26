/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketPrescribedCompletion
import Vegas.Game.ServiceRevealDecode

/-! # Accepted packets and successful resolutions

**The stop after an accepted packet.** Let `who` have recorded a packet for an
event of rank `rank`, sent from a configuration at which the event is ready,
with the acceptance invariant holding. Under play of any profile until a late
stop at that rank or an extra stop, every stop keeps the sending configuration
while the event is pending, and once the event completes it is one step of the
event from the sending configuration with a successful output, provided the
packet settles on that stopped law (`Vegas.accepted_until_config`).

**A successful resolution discloses.** A resolve event completed with a
successful output was completed by the disclosing action
(`Vegas.disclose_of_outputSucceeded`).
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

variable (setup runtime leaks bounds horizon scheduler) in
/-- After a recorded send of message for event from sent: the acceptance
invariant, and, once the event has completed, the configuration is one step of
the event from sent. -/
private def AcceptedInvariant (who : Player) (entry : (application setup runtime leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (sent : (graph setup).Config) (ready : sent.cut.Ready event) :
    (application setup runtime leaks).ProtocolState → Prop
  | none => False
  | some control =>
      AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry message event sent
          (some control) ∧
        (event ∈ control.execution.application.config.cut.completed →
          ∃ action, control.execution.application.config ∈
            (sent.step event ready action).support)

/-- The invariant passes along every transition from a state where the event
of rank rank has not completed. -/
private theorem acceptedInvariant_transition {who : Player}
    {entry : (application setup runtime leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} {ready : sent.cut.Ready event} {rank : Nat}
    (ordered : sent.cut.IsPrefix rank) (before after : (application setup runtime
      leaks).ProtocolState)
    (going : ∀ control, before = some control →
      ¬ control.execution.application.config.cut.IsPrefix (rank + 1))
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Legal before joint)
    (holds : AcceptedInvariant setup runtime leaks bounds horizon scheduler who entry message
      event sent
      ready before)
    (reached : after ∈ (((bounds.onePacketMenu runtime leaks).protocol
      (initialLaw setup) horizon scheduler).step before ⟨joint, legal⟩).support) :
    AcceptedInvariant setup runtime leaks bounds horizon scheduler who entry message event sent
      ready
      after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨invariant, completion⟩ := holds
      have afterInvariant := acceptanceInvariant_transition (runtime := runtime) bounds horizon
        scheduler who entry
        message event sent (some control) after joint legal invariant reached
      cases after with
      | none => exact afterInvariant.elim
      | some next =>
          refine ⟨afterInvariant, fun completedNext => ?_⟩
          have pending : event ∉ control.execution.application.config.cut.completed := by
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

/-- A recorded accepted call retains its sent configuration while pending,
and every completed stopped endpoint performs its successful compiled event
step. Settlement is required only on this actual stopped law. -/
theorem accepted_until_config
    (certificate : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu runtime leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (extraStop : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).History → Prop)
    {who : Player} {entry : (application setup runtime leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} (ready : sent.cut.Ready event) {rank : Nat}
    (ordered : sent.cut.IsPrefix rank)
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup runtime leaks).Control}
    (current : start.state = some control)
    (invariant : AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry
      message event
      sent (some control))
    (atSent : control.execution.application.config = sent)
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
          ∃ action, final.execution.application.config ∈ (sent.step event ready action).support ∧
            OutputSucceeded final.execution.application.config.store event) := by
  intro stop member
  let menu := bounds.onePacketMenu runtime leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  have holds : AcceptedInvariant setup runtime leaks bounds horizon scheduler who entry message
    event sent
      ready start.state := by
    rw [current]
    refine ⟨invariant, fun done => ?_⟩
    rw [atSent] at done
    exact (ready.1 done).elim
  have reachedInvariant := model.runBehavioralUntil_support_closed certificate players
    (fun history => LateStopped setup runtime leaks bounds horizon scheduler rank history ∨
      extraStop history)
    (AcceptedInvariant setup runtime leaks bounds horizon scheduler who entry message event sent
      ready)
    (fun history going _ joint legal target holds reached =>
      acceptedInvariant_transition (runtime := runtime) ordered history.state target
        (fun control state prefixed => going (Or.inl ⟨control, state, prefixed⟩)) joint legal holds
        reached)
    start holds stop member
  cases state : stop.state with
  | none =>
      rw [state] at reachedInvariant
      exact reachedInvariant.elim
  | some final =>
      rw [state] at reachedInvariant
      obtain ⟨finalInvariant, completion⟩ := reachedInvariant
      obtain ⟨⟨finalTrace⟩, records, _, _, _, stable, settled⟩ := finalInvariant
      refine ⟨final, rfl, stable, fun done => ?_⟩
      obtain ⟨action, stepMember⟩ := completion done
      exact ⟨action, stepMember, settled (settles stop member final state records done)⟩

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- A publication's failure read at its own type is a failure. -/
private theorem isFailure_cast_publication {kind : EventGraph.EventField Player L}
    {payload : L.Ty} (kindEq : kind = .publication payload) :
    kind.IsFailure (cast (congrArg EventGraph.EventField.Value kindEq.symm)
      (PublicationResult.failure : PublicationResult (L.Val payload))) := by
  subst kindEq
  rfl

omit [Fintype Player] in
/-- **A successful resolution discloses.** A resolve event completed from a
configuration with a successful output was completed by the disclosing
action. -/
theorem disclose_of_outputSucceeded {before after : (graph setup).Config}
    {event : (graph setup).EventId} {ready : before.cut.Ready event}
    {action : (graph setup).Action event} {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (member : after ∈ (before.step event ready action).support)
    (succeeded : OutputSucceeded after.store event) :
    (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = true := by
  have reach : ConfigReaches setup before after :=
    Relation.ReflTransGen.single (Or.inr ⟨event, ready, action, member⟩)
  have completion : (⟨event, action⟩ : (graph setup).Completion) ∈ after.history := by
    rw [before.step_history event ready action after member]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have output := reach.resolve_output (outputEq := outputEq) (codeEq := codeEq) completion ready.1
  cases disclose : (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) with
  | true => rfl
  | false =>
      exfalso
      rw [disclose] at output
      obtain ⟨stored, storedEq, notFailed⟩ := succeeded
      rw [EventGraph.Config.store_output, output] at storedEq
      unfold EventGraph.EventCode.resolveOutput? at storedEq
      simp only [Bool.false_eq_true, ↓reduceIte, ite_self] at storedEq
      obtain ⟨result, resultEq, rfl⟩ := Option.map_eq_some_iff.mp storedEq
      have failure : result = .failure := by
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at resultEq
        obtain ⟨_, _, _, _, chosen⟩ := resultEq
        exact chosen.symm
      subst failure
      exact notFailed (isFailure_cast_publication outputEq)

end Vegas
