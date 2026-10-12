/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketForced
import Vegas.Source.DisclosureAliases
import Vegas.Pending.ReactiveOnePacketMenu

/-! # The pending pool on forced one-packet histories

**Failed reveals at the decoded point.** A failed reveal persists under every
source step (`Vegas.SourceProgram.ProtocolState.RevealFailed.step`). Completing
a publication event with the withholding action, as expiry does, makes its
owner's reveal fail at the next decoded point
(`Vegas.SourceProgram.ProtocolState.revealFailed_of_decode_withhold`).

**How events complete.** A scheduler command that completes an event either
includes an accepted packet naming it, from its actor, or completes a
publication event with the withholding action
(`Vegas.environment_completion_cause`). So at every legal history of the
default runtime, under arbitrary responses and every scheduler, either some
reveal has failed at the decoded point, or every completed publication event
was completed by an accepted packet of its actor
(`Vegas.publicationRecord_history`).

**The pending pool.** On a history of the one-packet game in a forced state,
every pending packet is a commitment without evidence or an opening of the
currently ready event by its actor, with exactly its own certificate
(`Vegas.onePacket_pending_of_forced`). An opening carries a readiness token, so
its event was ready when it was sent. Had the event completed since, either a
second packet of the actor for it was accepted, which the count verdict
forbids, or the reveal expired, which is a failed reveal and leaves the forced
region. Hence every value disclosed in the pending pool, which the scheduler
and the observation rule read, is the value of the ready event's opening
(`Vegas.onePacket_pending_disclosed_of_forced`).
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

open Vegas

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A failed reveal stays failed under every source step. -/
theorem RevealFailed.step {who : Player} : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → (target : ProtocolState program) →
    RevealFailed who program state → target ∈ (step program state joint).support →
    RevealFailed who program target
  | _, _, .ret _, _, _, _, failed, _ => failed.elim
  | _, _, .sample _ _ _ next, state, joint, target, failed, reached => by
      cases state with
      | inl _ => exact failed.elim
      | inr rest =>
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact RevealFailed.step next rest joint after failed supported
  | _, _, .commit _ _ _ _ next, state, joint, target, failed, reached => by
      cases state with
      | inl _ => exact failed.elim
      | inr rest =>
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact RevealFailed.step next rest joint after failed supported
  | _, _, .reveal _ _ _ _ _ _ next, state, joint, target, failed, reached => by
      cases state with
      | inl _ => exact failed.elim
      | inr rest =>
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases failed with ⟨owned, published⟩ | later
          · exact Or.inl ⟨owned, by rw [base_step next rest joint after supported]; exact published⟩
          · exact Or.inr (RevealFailed.step next rest joint after later supported)

/-- **Withholding fails a reveal.** At a point decoded after `count` events,
stepping with the decoded withholding action of the event at index `count`, a
publication event, makes some player's reveal fail. -/
theorem revealFailed_of_decode_withhold {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (state : ProtocolState program) (bound : count < eventCount program) {payload : L.Ty}
      (outputEq : outputLayout program ⟨count, bound⟩ = .publication payload)
      (target : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history =
          some state →
      target ∈ (step program state (fun _ => decodeEventAction program ⟨count, bound⟩
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) false))).support →
      ∃ who, RevealFailed who program target := by
  induction program with
  | ret _ =>
      intro count _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ _ _ next ih =>
      intro count refs registry revelations outputs store history state bound payload outputEq
        target decoded reached
      cases count with
      | zero => cases outputEq
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) outputEq after
            read supported
  | commit _ _ _ _ next ih =>
      intro count refs registry revelations outputs store history state bound payload outputEq
        target decoded reached
      cases count with
      | zero => cases outputEq
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) outputEq after
            read supported
  | reveal published owner name fresh source unresolved next ih =>
      intro count refs registry revelations outputs store history state bound payload outputEq
        target decoded reached
      cases count with
      | zero =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same : target = Sum.inr (entry next (revealSuccessor published source
              ⟨cells, registry, revelations, history⟩ false)) :=
            (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          refine ⟨owner, Or.inl ⟨rfl, ?_⟩⟩
          rw [base_entry]
          exact disclosureResult_false published source _
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          obtain ⟨who, failed⟩ := ih count _ _ _ _ store history rest
            (Nat.lt_of_succ_lt_succ bound) outputEq after read supported
          exact ⟨who, Or.inr failed⟩

end Vegas.SourceProgram.ProtocolState

namespace Vegas.EventGraphRuntime

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The values a packet discloses to whoever reads it: the value in an opening
or malformed call, and the value of attached evidence. A commitment call
carries a handle and no value. -/
def WitnessedPacket.disclosedValues (packet : WitnessedPacket graph) : List (Raw L) :=
  (match packet.call with
    | .commitment _ _ => []
    | .opening _ _ raw => [raw]
    | .malformed raw => [raw]) ++ (packet.evidence.map OpeningFact.raw).toList

end Vegas.EventGraphRuntime

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Completion

/-- A configuration that completed a ready event differs from the one before. -/
theorem config_ne_of_step {config next : (graph setup).Config} {event : (graph setup).EventId}
    {ready : config.cut.Ready event} {action : (graph setup).Action event}
    (member : next ∈ (config.step event ready action).support) : next ≠ config := by
  intro same
  have completed : event ∈ next.cut.completed := by
    rw [config.step_cut event ready action next member]
    exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)
  rw [same] at completed
  exact ready.1 completed

/-- Two completions reaching one configuration complete the same event with the
same action. -/
theorem step_completion_unique {config next : (graph setup).Config}
    {first second : (graph setup).EventId} {firstReady : config.cut.Ready first}
    {secondReady : config.cut.Ready second} {firstAction : (graph setup).Action first}
    {secondAction : (graph setup).Action second}
    (firstMember : next ∈ (config.step first firstReady firstAction).support)
    (secondMember : next ∈ (config.step second secondReady secondAction).support) :
    (⟨first, firstAction⟩ : (graph setup).Completion) = ⟨second, secondAction⟩ := by
  have firstHistory := config.step_history first firstReady firstAction next firstMember
  have secondHistory := config.step_history second secondReady secondAction next secondMember
  rw [firstHistory] at secondHistory
  exact List.singleton_injective (List.append_cancel_left secondHistory)

/-- **How a scheduler command completes an event.** When an environment step
completes a ready event, either an included packet naming that event was
accepted, by the event's actor, or the action is the withholding action at a
publication event, as at an expired reveal. -/
theorem environment_completion_cause (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    {event : (graph setup).EventId} (ready : execution.application.config.cut.Ready event)
    (action : (graph setup).Action event)
    (member : next.application.config ∈
      (execution.application.config.step event ready action).support) :
    (∃ message ∈ next.network.ledger, (message.id, true) ∈ next.receipts ∧
        message.payload.call.event? (graph setup) = some event ∧
        (graph setup).actor? event = some message.sender) ∨
      ∀ payload (outputEq : (graph setup).outputLayout event = .publication payload),
        action = cast (congrArg EventGraph.EventField.Action outputEq.symm) false := by
  let app := application setup leaks
  have stutter : next.application.config = execution.application.config → False :=
    config_ne_of_step member
  cases command with
  | activate who =>
      exfalso
      apply stutter
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      rw [PMF.support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      rfl
  | wait =>
      exfalso
      apply stutter
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | «include» id =>
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      left
      change (execution.includePending app id).application.config ∈ _ at member
      change ∃ message ∈ (execution.includePending app id).network.ledger,
        (message.id, true) ∈ (execution.includePending app id).receipts ∧ _
      cases found : execution.network.lookup id with
      | none =>
          exact (config_ne_of_step member (by
            simp only [ReactiveApplication.Execution.includePending,
              MessageNetwork.includePending, found])).elim
      | some message =>
          obtain ⟨identified, _, ledgerEq⟩ := includePending_found execution.network
            id message found
          cases accepted : app.handle execution.application message with
          | none =>
              exact (config_ne_of_step member (by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_none])).elim
          | some after =>
              have applicationEq : (execution.includePending app id).application = after := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_some]
              have receiptsEq : (execution.includePending app id).receipts =
                  execution.receipts ++ [(id, true)] := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.isSome_some]
              have networkEq : (execution.includePending app id).network =
                  (execution.network.includePending id).2 := app.includePending_network execution id
              obtain ⟨_, namedEvent, named, namedReady, _, actor⟩ :=
                accepted_inclusion execution.application after message accepted
              obtain ⟨other, otherNamed, otherReady, otherAction, otherMember⟩ :=
                handle_config_mem_step (runtime setup) execution.application after _
                  (reactiveHandle_call accepted)
              have sameNamed : other = _ := Option.some.inj (otherNamed.symm.trans named)
              subst sameNamed
              rw [applicationEq] at member
              have same := step_completion_unique otherMember member
              cases same
              refine ⟨message, ?_, ?_, named, actor⟩
              · rw [networkEq, ledgerEq]
                exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
              · rw [receiptsEq, identified]
                exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  | application command =>
      obtain ⟨changed, _⟩ := applicationStep_facts execution next command reached
      right
      intro payload outputEq
      cases command with
      | advanceClock =>
          exfalso
          apply stutter
          simp only [EventGraphRuntime.environmentStep, PMF.mem_support_pure_iff] at changed
          rw [changed]
      | executeSample sampled =>
          obtain ⟨_, effect⟩ := environmentStep_executeSample_config_activated (runtime setup)
            execution.application next.application sampled changed
          rcases effect with ⟨configEq, _⟩ | ⟨sampledReady, sampledAction, sampledMember, _⟩
          · exact (stutter configEq).elim
          · have same := step_completion_unique sampledMember member
            cases same
            exfalso
            cases view : nodeView (graph setup) event with
            | sample _ _ sampleEq _ => cases sampleEq.symm.trans outputEq
            | bind _ _ bindEq _ => cases bindEq.symm.trans outputEq
            | resolve owner resolved binding checks resolveEq codeEq =>
                rw [environmentStep_executeSample_of_nonsample (runtime setup) _ event ready
                  (fun _ _ _ _ sampled => by rw [view] at sampled; cases sampled),
                  PMF.mem_support_pure_iff] at changed
                exact stutter (congrArg (fun state => state.config) changed)
      | expire expired =>
          obtain ⟨_, effect⟩ := environmentStep_expire_config_activated (runtime setup)
            execution.application next.application expired changed
          rcases effect with ⟨configEq, _⟩ | ⟨expiredReady, expiredAction, expiredMember, _⟩
          · exact (stutter configEq).elim
          · have same := step_completion_unique expiredMember member
            cases same
            cases view : nodeView (graph setup) event with
            | sample _ _ sampleEq _ => cases sampleEq.symm.trans outputEq
            | bind _ _ bindEq _ => cases bindEq.symm.trans outputEq
            | resolve owner resolved binding checks resolveEq codeEq =>
                have samePayload : resolved = payload :=
                  EventGraph.EventField.publication.inj (resolveEq.symm.trans outputEq)
                subst samePayload
                cases activated : execution.application.activatedAt event with
                | none =>
                    rw [environmentStep_expire_of_not_activated (runtime setup) _ event ready
                      activated, PMF.mem_support_pure_iff] at changed
                    exact (stutter (congrArg (fun state => state.config) changed)).elim
                | some entered =>
                    by_cases due : (runtime setup).deadline event ≤
                        execution.application.clock - entered
                    · rw [environmentStep_expire_resolve_eq (runtime setup) _ event ready entered
                        activated due owner resolved binding checks resolveEq codeEq view,
                        PMF.mem_support_pure_iff] at changed
                      have history := execution.application.config.step_history event ready action
                        _ member
                      rw [changed] at history
                      change execution.application.config.history ++
                          [⟨event, cast (congrArg EventGraph.EventField.Action resolveEq.symm)
                            false⟩] = _ at history
                      have completion := List.singleton_injective
                        (List.append_cancel_left history)
                      exact (eq_of_heq (EventGraph.Completion.mk.inj completion).2).symm
                    · rw [environmentStep_expire_of_not_due (runtime setup) _ event ready entered
                        activated due, PMF.mem_support_pure_iff] at changed
                      exact (stutter (congrArg (fun state => state.config) changed)).elim

end Completion

section Record

variable (setup) in
/-- Some player's reveal has failed at a source point. -/
def SomeRevealFailed (point : ProtocolState setup.program) : Prop :=
  ∃ who, ProtocolState.RevealFailed who setup.program point

theorem someRevealFailed_stepClosed : StepClosed setup (SomeRevealFailed setup) :=
  fun state joint target ⟨who, failed⟩ reached =>
    ⟨who, ProtocolState.RevealFailed.step setup.program state joint target failed reached⟩

/-- Every completed publication event was completed by an accepted packet naming
it, sent by the event's actor. -/
def PublicationsAccepted (execution : (application setup leaks).Execution) : Prop :=
  ∀ event ∈ execution.application.config.cut.completed, ∀ payload,
    (graph setup).outputLayout event = .publication payload →
      ∃ message ∈ execution.network.ledger, (message.id, true) ∈ execution.receipts ∧
        message.payload.call.event? (graph setup) = some event ∧
        (graph setup).actor? event = some message.sender

/-- **The publication record.** The configuration decodes at a prefix, and
either some reveal has failed at the decoded point or every completed
publication event was completed by an accepted packet of its actor. -/
def PublicationRecord (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution) : Prop :=
  ∃ rank, Nonempty (SourceResidual setup profile rank execution.application.config) ∧
    (DecodedHolds (SomeRevealFailed setup) rank execution.application.config ∨
      PublicationsAccepted execution)

/-- Scheduler commands only append to the ledger and the receipts. -/
theorem environment_ledger_receipts_grow (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support) :
    (∀ message ∈ execution.network.ledger, message ∈ next.network.ledger) ∧
      ∀ receipt ∈ execution.receipts, receipt ∈ next.receipts := by
  rcases (environmentStep_shape setup leaks execution next command reached).2.2 with
    ⟨receiptsEq, ledgerEq, _⟩ | ⟨id, message, found, networkEq, receiptsEq, _⟩
  · rw [receiptsEq, ledgerEq]
    exact ⟨fun _ kept => kept, fun _ kept => kept⟩
  · rw [networkEq, (includePending_found execution.network id message found).2.2, receiptsEq]
    exact ⟨fun _ kept => List.mem_append_left _ kept, fun _ kept => List.mem_append_left _ kept⟩

/-- The publication record holds at every legal history of the default runtime,
under arbitrary responses and every scheduler. -/
theorem publicationRecord_serviceInvariant (profile : BehavioralProfile setup.program)
    (scheduler : (application setup leaks).Scheduler) :
    (application setup leaks).ServiceInvariant scheduler (PublicationRecord profile) where
  respond execution who action valid := by
    have configEq := ((runtime setup).reactive_respond_application leaks execution who action).1
    have ledgerEq := (application setup leaks).respond_ledger execution who action
    have receiptsEq := (application setup leaks).respond_receipts execution who action
    unfold PublicationRecord PublicationsAccepted at valid ⊢
    rw [configEq, ledgerEq, receiptsEq]
    exact valid
  environment execution next command valid _ reached := by
    obtain ⟨rank, ⟨residual⟩, holds⟩ := valid
    have grows := environment_ledger_receipts_grow execution next command reached
    have kept : PublicationsAccepted execution →
        ∀ event ∈ execution.application.config.cut.completed, ∀ payload,
          (graph setup).outputLayout event = .publication payload →
          ∃ message ∈ next.network.ledger, (message.id, true) ∈ next.receipts ∧
            message.payload.call.event? (graph setup) = some event ∧
            (graph setup).actor? event = some message.sender := by
      intro accepted event completed payload outputEq
      obtain ⟨message, member, receipt, named, actor⟩ := accepted event completed payload outputEq
      exact ⟨message, grows.1 message member, grows.2 _ receipt, named, actor⟩
    rcases environmentStep_configStep setup leaks execution next command reached with
      same | ⟨event, ready, action, member⟩
    · refine ⟨rank, ?_, ?_⟩
      · rw [same]
        exact ⟨residual⟩
      · rcases holds with failed | accepted
        · left
          rw [same]
          exact failed
        · right
          intro event completed payload outputEq
          rw [same] at completed
          exact kept accepted event completed payload outputEq
    · have rankEq : event.val = rank :=
        (ready_iff_rank setup _ rank residual.checkpoint.ordered event).mp ready
      obtain ⟨successor, reachedPoint⟩ := residual.step event ready action _ member
      refine ⟨rank + 1, ⟨successor⟩, ?_⟩
      have decodedNext : ∀ state, sourceServicePrefix? setup (rank + 1)
          next.application.config = some state →
            state = successor.lift (ProtocolState.entry successor.program successor.source) := by
        intro state decoded
        rw [successor.decode] at decoded
        exact (Option.some.inj decoded).symm
      have completedNext : ∀ other ∈ next.application.config.cut.completed,
          other = event ∨ other ∈ execution.application.config.cut.completed := by
        intro other completed
        rw [execution.application.config.step_cut event ready action _ member] at completed
        exact (EventOrder.Cut.mem_complete _ _ _ _).mp completed
      rcases holds with failed | accepted
      · left
        intro state decoded
        rw [decodedNext state decoded]
        exact someRevealFailed_stepClosed _ _ _ (failed _ residual.decode) reachedPoint
      · rcases environment_completion_cause execution next command reached ready action member with
          ⟨message, present, receipt, named, actor⟩ | withheld
        · right
          intro other completed payload outputEq
          rcases completedNext other completed with rfl | earlier
          · exact ⟨message, present, receipt, named, actor⟩
          · exact kept accepted other earlier payload outputEq
        · by_cases publication : ∃ payload, (graph setup).outputLayout event = .publication payload
          · obtain ⟨payload, outputEq⟩ := publication
            left
            intro state decoded
            rw [decodedNext state decoded]
            have actionEq := withheld payload outputEq
            subst actionEq
            have decodedBefore := residual.decode
            generalize residual.lift (ProtocolState.entry residual.program residual.source) =
              point at decodedBefore reachedPoint
            rw [← rankEq] at decodedBefore
            exact ProtocolState.revealFailed_of_decode_withhold setup.program event.val _ _ _ _ _ _
              _ event.isLt outputEq _ decodedBefore reachedPoint
          · right
            intro other completed payload outputEq
            rcases completedNext other completed with rfl | earlier
            · exact (publication ⟨payload, outputEq⟩).elim
            · exact kept accepted other earlier payload outputEq

/-- The publication record holds at every legal history of the default runtime
from its initial law. -/
theorem publicationRecord_history (profile : BehavioralProfile setup.program)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    PublicationRecord profile control.execution :=
  (publicationRecord_serviceInvariant profile scheduler).history (initialLaw setup) horizon
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      let residual := SourceResidual.initial setup profile initial
      refine ⟨0, ⟨residual⟩, Or.inr fun event completed => ?_⟩
      have below := (residual.checkpoint.ordered.2 event).mp completed
      exact absurd below (Nat.not_lt_zero _)) trace

end Record

section PendingPool

/-- At a forced decoded point no player's reveal has failed: the owner's own
failed reveal is excluded outright, and another player's would exclude it. -/
theorem ForcedPoint.not_someRevealFailed {who : Player} {point : ProtocolState setup.program}
    (forced : ForcedPoint setup who point) : ¬ SomeRevealFailed setup point := by
  rintro ⟨other, failed⟩
  by_cases same : other = who
  · subst same
    exact forced.1 failed
  · exact (forced.2 other same).1 (ProtocolState.RevealFailed.excluded setup.program point failed)

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- **The pending pool on forced one-packet histories.** At a history of the
one-packet game in a forced state, every pending packet is either a commitment
carrying no evidence or an opening of the currently ready event by that
event's actor, carrying exactly its own certificate. In particular no pending
packet carries the value of any event other than the ready one: a stale
opening exists only after an expired reveal, which is a failed reveal and
leaves the forced region. -/
theorem onePacket_pending_of_forced (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) (who : Player)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (forced : ForcedState setup leaks who history.state)
    {control : (application setup leaks).Control} (current : history.state = some control)
    (message : Message Player (WitnessedPacket (graph setup)))
    (pending : message ∈ control.execution.network.pending) :
    (∃ event candidate, message.payload.call = .commitment event candidate ∧
        message.payload.evidence = none) ∨
      ∃ event candidate raw, message.payload.call = .opening event candidate raw ∧
        message.payload.evidence = some ⟨candidate, raw⟩ ∧
        control.execution.application.config.cut.Ready event ∧
        (graph setup).actor? event = some message.sender := by
  let app := application setup leaks
  have trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control) :=
    current ▸ (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
      scheduler history.trace
  have clean := (bounds.onePacketMenu_countClean (runtime setup) leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => (runtime setup).countClean_initial leaks state)
    history.trace
  rw [current] at clean forced
  change (runtime setup).CountClean leaks control.execution at clean
  have facts := settledFacts_history (initialLaw setup) horizon scheduler trace
  have distinct := app.idsDistinct_history scheduler (initialLaw setup) horizon trace
  change control.execution.network.IdsDistinct at distinct
  unfold MessageNetwork.IdsDistinct at distinct
  rw [List.map_append, List.nodup_append] at distinct
  have emitted : Emitted setup leaks control.execution message := facts.carried.pending message
    pending
  obtain ⟨tokenValid, correct, first⟩ :=
    (countPermits_eq_true_iff _ _).mp (clean.2 message emitted)
  unfold CountCallCorrect at correct
  cases call : message.payload.call with
  | malformed raw =>
      rw [call] at correct
      exact correct.elim
  | commitment event candidate =>
      rw [call] at correct
      exact Or.inl ⟨event, candidate, rfl, correct.2.1⟩
  | opening event candidate raw =>
      rw [call] at correct
      obtain ⟨certified, owned⟩ := correct
      obtain ⟨certifiedEvent, certifiedCandidate, certifiedRaw, token, shape⟩ :=
        (certifiedOpening_iff _).mp certified
      rw [shape] at call
      cases call
      have evidence : message.payload.evidence = some ⟨candidate, raw⟩ := by rw [shape]
      cases view : nodeView (graph setup) event with
      | bind _ _ _ _ =>
          rw [view] at owned
          exact owned.elim
      | sample _ _ _ _ =>
          rw [view] at owned
          exact owned.elim
      | resolve owner payload binding checks outputEq codeEq =>
          rw [view] at owned
          have actor : (graph setup).actor? event = some message.sender :=
            (nodeView_resolve_actor outputEq codeEq).trans (congrArg some owned.1.symm)
          obtain ⟨tokenEvent, tokenNamed, tokenEq⟩ :=
            (WitnessedPacket.tokenValid_iff _).mp tokenValid
          rw [shape] at tokenNamed
          cases tokenNamed
          have issued := facts.issued message emitted ⟨event⟩ tokenEq
          have open_ : event ∉ control.execution.application.config.cut.completed := by
            intro completed
            obtain ⟨rank, point, ordered, decoded, forcedPoint⟩ := forced
            obtain ⟨recordRank, ⟨residual⟩, record⟩ :=
              publicationRecord_history (failureProfile setup.program) horizon scheduler trace
            have sameRank := isPrefix_unique ordered residual.checkpoint.ordered
            subst sameRank
            rcases record with failed | accepted
            · exact forcedPoint.not_someRevealFailed (failed point decoded)
            · obtain ⟨other, onLedger, _, otherNamed, otherActor⟩ :=
                accepted event completed payload outputEq
              have sameSender : other.sender = message.sender :=
                Option.some.inj (otherActor.symm.trans actor)
              have differentIds : message.id ≠ other.id :=
                distinct.2.2 message.id (List.mem_map_of_mem pending) other.id
                  (List.mem_map_of_mem onLedger)
              have differentSerials : message.id.2 ≠ other.id.2 := by
                intro sameSerial
                apply differentIds
                exact Prod.ext sameSender.symm sameSerial
              have otherEmitted : Emitted setup leaks control.execution other :=
                facts.carried.ledger other onLedger
              obtain ⟨_, _, otherFirst⟩ :=
                (countPermits_eq_true_iff _ _).mp (clean.2 other otherEmitted)
              have messageNamed : message.payload.call.event? (graph setup) = some event := by
                rw [shape]
                rfl
              rcases Nat.lt_or_gt_of_ne differentSerials with lower | upper
              · exact otherFirst message ⟨emitted, sameSender.symm, lower⟩
                  (messageNamed.trans otherNamed.symm)
              · exact first other ⟨otherEmitted, sameSender, upper⟩
                  (otherNamed.trans messageNamed.symm)
          exact Or.inr ⟨event, candidate, raw, rfl, evidence,
            ⟨open_, fun predecessor member => issued predecessor member⟩, actor⟩

/-- **The scheduler and the observation rule read no other unopened value.**
Both read the public environment view and the pending payloads. At a history
of the one-packet game in a forced state, every value a pending packet
discloses is the value of an opening of the currently ready event, the only
ready event of the sequential graph, sent by that event's actor. -/
theorem onePacket_pending_disclosed_of_forced (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) (who : Player)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (forced : ForcedState setup leaks who history.state)
    {control : (application setup leaks).Control} (current : history.state = some control)
    (message : Message Player (WitnessedPacket (graph setup)))
    (pending : message ∈ control.execution.network.pending) :
    ∀ raw ∈ message.payload.disclosedValues, ∃ event candidate,
      message.payload.call = .opening event candidate raw ∧
        control.execution.application.config.cut.Ready event ∧
        (graph setup).actor? event = some message.sender := by
  intro disclosed member
  rcases onePacket_pending_of_forced bounds horizon scheduler who history forced current message
    pending with ⟨event, candidate, call, evidence⟩ |
      ⟨event, candidate, raw, call, evidence, ready, actor⟩
  · simp [WitnessedPacket.disclosedValues, call, evidence] at member
  · have same : disclosed = raw := by
      simpa [WitnessedPacket.disclosedValues, call, evidence] using member
    subst same
    exact ⟨event, candidate, call, ready, actor⟩

end PendingPool

end Vegas
