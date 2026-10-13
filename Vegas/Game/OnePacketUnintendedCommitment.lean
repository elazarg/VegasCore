/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketProjectedDecision
import Vegas.Game.OnePacketSureFailure
import Vegas.Game.OnePacketDisclosureResolves
import Vegas.Source.IntendedForPlayer

/-! # Unintended commitments leave their owner owing

**At the source.** At a point intended for a player, completing an event of
the player with a decoded action outside the intended actions of the player's
view leaves the player owing a failure
(`Vegas.SourceProgram.ProtocolState.owesFailure_of_decode_not_intendedAvailable`):
a failed binding is a failed binding, a binding of a value outside the intended
values is a binding of a value its guard is predicted to reject, and a withheld
disclosure fails the reveal.
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **An unintended completion owes.** At a point intended for `actor`, decoded
after `count` events, stepping with the decoded action of the event of index
`count`, owned by `actor`, when that action is not an intended action of
`actor`'s view, leaves `actor` owing a failure. -/
theorem owesFailure_of_decode_not_intendedAvailable {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (state : ProtocolState program) (bound : count < eventCount program) (actor : Player)
      (action : EventGraph.EventField.Action (outputLayout program ⟨count, bound⟩))
      (target : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history =
          some state →
      IntendedFor actor program state →
      eventOwner? program ⟨count, bound⟩ = some actor →
      target ∈ (step program state
        (fun _ => decodeEventAction program ⟨count, bound⟩ action)).support →
      (∀ act, decodeEventAction program ⟨count, bound⟩ action = some act →
        act ∉ ProtocolView.intendedAvailable actor program (observe actor program state)) →
      OwesFailure actor program target := by
  induction program with
  | ret _ =>
      intro count _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached unintended
      cases count with
      | zero => cases owned
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended owned supported unintended
  | @commit commitCtx commitNames name owner payload fresh guard next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached unintended
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          change PublicationResult (L.Val payload) at action
          change ∀ act, some (OwnAction.commit owner name payload action) = some act → _
            at unintended
          change OwesFailure owner (.commit name owner fresh guard next) (Sum.inr (entry next
            (commitSuccessor name guard ⟨cells, registry, revelations, history⟩
              (OwnAction.binding owner name payload
                (some (OwnAction.commit owner name payload action))))))
          rw [OwnAction.binding_commit]
          cases action with
          | failure =>
              exact Or.inr (failedBinding_entry next _ (intended.failedBinding_commit fresh guard))
          | success value =>
              have outside := unintended _ rfl
              have rejected : guard.predicts (sourceObserve owner cells) value = false := by
                cases predicted : guard.predicts (sourceObserve owner cells) value with
                | false => rfl
                | true =>
                    exact (outside ⟨value, Or.inl
                      ((mem_predictedValues_self guard _ value).mpr predicted), rfl⟩).elim
              exact Or.inl (indebted_entry next _ (intended.indebted_commit fresh guard value
                rejected))
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended owned supported unintended
  | reveal published owner name fresh source unresolved next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached unintended
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          change Bool at action
          change ∀ act, some (OwnAction.reveal owner name action) = some act → _ at unintended
          cases action with
          | true => exact (unintended _ rfl rfl).elim
          | false =>
              refine Or.inl (Or.inl ⟨rfl, ?_⟩)
              rw [base_entry]
              exact disclosureResult_false published source _
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended owned supported unintended with indebted | failed
          · exact Or.inl (Or.inr indebted)
          · exact Or.inr (Or.inr failed)

end Vegas.SourceProgram.ProtocolState

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

variable (setup leaks) in
/-- **The unintended-commitment invariant** after `who` emits, from a recorded
entry, the commitment of its binding event `event` to `candidate`, at a
configuration `start` decoding to `point`: the history is legal, the entry is
recorded, the candidate's meaning is fixed and opens no value whose decoded
action is intended at `who`'s view of `point`; until the event completes the
configuration is `start`, and once it has completed `who` owes a failure at the
decoded point. -/
def UnintendedCommitmentInvariant (profile : BehavioralProfile setup.program) (who : Player)
    (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (candidate : Handle (graph setup)) {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (start : (graph setup).Config) (point : ProtocolState setup.program) :
    (application setup leaks).ProtocolState → Prop
  | none => False
  | some control =>
      Nonempty (((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
        horizon scheduler).Trace (some control)) ∧
      RecordsEntry setup leaks who entry (some control) ∧ entry.emitted = some message ∧
      message.sender = who ∧ message.payload.call = .commitment event candidate ∧
      control.execution.application.candidates.lookup candidate ≠ .fresh ∧
      (∀ value act, control.execution.application.candidates.lookup candidate =
          .openable ⟨payload, value⟩ →
        decodeEventAction setup.program event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            (PublicationResult.success value)) = some act →
        act ∉ ProtocolView.intendedAvailable who setup.program
          (ProtocolState.observe who setup.program point)) ∧
      (event ∉ control.execution.application.config.cut.completed →
        control.execution.application.config = start) ∧
      (event ∈ control.execution.application.config.cut.completed →
        DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program)
          (some control))

private theorem cast_some' {A B : Type} (same : A = B) (value : A) :
    cast (congrArg Option same) (some value) = some (cast same value) := by
  subst same
  rfl

private theorem cast_cast_symm' {A B : Type} (same : A = B) (value : B) :
    cast same (cast same.symm value) = value := by
  subst same
  rfl

/-- **The unintended-commitment invariant persists** under every transition of
the one-packet game, from a configuration decoding to a point intended for
`who` at which `event` is ready. -/
theorem unintendedCommitmentInvariant_transition (profile : BehavioralProfile setup.program)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {candidate : Handle (graph setup)} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {start : (graph setup).Config} {point : ProtocolState setup.program}
    (decoded : decodedPoint setup start = some point)
    (intendedFor : ProtocolState.IntendedFor who setup.program point)
    (startReady : start.cut.Ready event)
    (before after : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (legal : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Legal before joint)
    (holds : UnintendedCommitmentInvariant setup leaks bounds horizon scheduler profile who entry
      message event candidate outputEq start point before)
    (reached : after ∈ (((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).step before ⟨joint, legal⟩).support) :
    UnintendedCommitmentInvariant setup leaks bounds horizon scheduler profile who entry message
      event candidate outputEq start point after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨⟨trace⟩, records, emitted, sender, call, fixed, unintended, pending, settled⟩ :=
        holds
      have afterRecords := recordsEntry_transition who entry (initialLaw setup) horizon scheduler
        _ after joint records reached
      cases after with
      | none => exact afterRecords.elim
      | some next =>
          have nextTrace : ((bounds.onePacketMenu (runtime setup) leaks).protocol
              (initialLaw setup) horizon scheduler).Trace (some next) :=
            .extend trace joint legal reached
          have kept := (keepsFixedCandidates_step (runtime setup) leaks).transition
            (initialLaw setup) horizon scheduler control next joint reached
          have keptStore := (keepsStore_step (runtime setup) leaks).transition
            (initialLaw setup) horizon scheduler control next joint reached
          have lookupEq := kept candidate fixed
          have owned : (graph setup).actor? event = some who := nodeView_bind_actor outputEq codeEq
          by_cases old : event ∈ control.execution.application.config.cut.completed
          · have stillDone : event ∈ next.execution.application.config.cut.completed := by
              rcases transition_configStep (initialLaw setup) horizon scheduler control next joint
                  reached with same | ⟨completed, ready, action, member⟩
              · rw [same]
                exact old
              · rw [control.execution.application.config.step_cut completed ready action _ member,
                  EventOrder.Cut.mem_complete]
                exact Or.inr old
            refine ⟨⟨nextTrace⟩, afterRecords, emitted, sender, call, by rw [lookupEq]; exact fixed,
              fun value act opened => unintended value act (by rw [← lookupEq]; exact opened),
              fun notDone => (notDone stillDone).elim, fun _ => ?_⟩
            exact decodedHolds_transition (owesFailure_stepClosed who) (initialLaw setup)
              horizon scheduler (some control) (some next) joint (settled old) reached
          · have atStart := pending old
            rcases transition_configStep (initialLaw setup) horizon scheduler control next joint
                reached with same | ⟨completed, ready, action, member⟩
            · refine ⟨⟨nextTrace⟩, afterRecords, emitted, sender, call,
                by rw [lookupEq]; exact fixed,
                fun value act opened => unintended value act (by rw [← lookupEq]; exact opened),
                fun _ => same.trans atStart, fun done => ?_⟩
              rw [same] at done
              exact (old done).elim
            · have readyStart : start.cut.Ready completed := atStart ▸ ready
              obtain ⟨rank, ordered, _⟩ := decodedPoint_isPrefix decoded
              have eventEq : completed = event := Fin.ext
                (((ready_iff_rank setup start rank ordered completed).mp readyStart).trans
                  ((ready_iff_rank setup start rank ordered event).mp startReady).symm)
              subst eventEq
              have done : completed ∈ next.execution.application.config.cut.completed := by
                rw [control.execution.application.config.step_cut completed ready action _ member,
                  EventOrder.Cut.mem_complete]
                exact Or.inl rfl
              refine ⟨⟨nextTrace⟩, afterRecords, emitted, sender, call,
                by rw [lookupEq]; exact fixed,
                fun value act opened => unintended value act (by rw [← lookupEq]; exact opened),
                fun notDone => (notDone done).elim, fun _ => ?_⟩
              have output := step_binding_output (outputEq := outputEq) (codeEq := codeEq) member
              have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
                  scheduler).Trace (some control) :=
                (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
                  scheduler trace
              have nextRawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
                  scheduler).Trace (some next) :=
                (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
                  scheduler nextTrace
              have facts := legalFacts setup leaks horizon scheduler _ rawTrace
              have nextFacts := legalFacts setup leaks horizon scheduler _ nextRawTrace
              have read : (⟨.inr completed, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
                  (.binding who payload)).get? next.execution.application.config.store =
                  some (cast (congrArg EventGraph.EventField.Action outputEq) action) := by
                simp only [EventGraph.FieldRef.get?]
                change cast _ (next.execution.application.config.outputs completed) = _
                rw [output, cast_some' (congrArg EventGraph.EventField.Value outputEq),
                  cast_cast_symm']
              obtain ⟨residualRank, ⟨residual⟩⟩ := protocol_sourceResidual profile
                (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler trace control rfl
              obtain ⟨successor, reachedPoint⟩ := residual.step completed ready action _ member
              have decodedBefore : decodedPoint setup control.execution.application.config =
                  some point := atStart ▸ decoded
              have samePoint : residual.lift (ProtocolState.entry residual.program
                  residual.source) = point :=
                Option.some.inj ((decodedPoint_eq residual).symm.trans decodedBefore)
              rw [samePoint] at reachedPoint
              have ownedSource : eventOwner? setup.program ⟨completed.val, completed.isLt⟩ =
                  some who := by
                rw [eventOwner?_eq_actor]
                exact owned
              have owes : ProtocolState.OwesFailure who setup.program
                  (successor.lift (ProtocolState.entry successor.program successor.source)) := by
                cases result : (cast (congrArg EventGraph.EventField.Action outputEq) action :
                    PublicationResult (L.Val payload)) with
                | failure =>
                    have actionEq : action = cast (congrArg EventGraph.EventField.Action
                        outputEq.symm) (PublicationResult.failure :
                          PublicationResult (L.Val payload)) := by
                      rw [← result, cast_cast, cast_eq]
                    have failing := decodeEventAction_failing_binding setup.program completed.val
                      completed.isLt outputEq
                    rw [← actionEq] at failing
                    exact ProtocolState.owesFailure_of_decode_failing setup.program
                      setup.namesNodup completed.val _ _ _ _ _ _ point completed.isLt who _ _
                      (decodedPoint_decode ready decodedBefore) ownedSource failing reachedPoint
                | success value =>
                    rw [result] at read
                    obtain ⟨installed, acceptedAt, _, meaning⟩ :=
                      nextFacts.binding.success_provenance _ value read
                    have vacant : control.execution.application.accepted (.inr completed) =
                        none := by
                      cases present : control.execution.application.accepted (.inr completed) with
                      | none => rfl
                      | some found =>
                          exact (old (facts.binding.toAssociationInvariant.accepted_complete
                            completed found present)).elim
                    have sameCandidate := onePacket_accepted_new bounds horizon scheduler trace
                      records emitted sender call owned vacant joint reached installed acceptedAt
                    subst sameCandidate
                    rw [lookupEq] at meaning
                    have actionEq : action = cast (congrArg EventGraph.EventField.Action
                        outputEq.symm) (PublicationResult.success value) := by
                      rw [← result, cast_cast, cast_eq]
                    exact ProtocolState.owesFailure_of_decode_not_intendedAvailable setup.program
                      completed.val _ _ _ _ _ _ point completed.isLt who action _
                      (decodedPoint_decode ready decodedBefore) intendedFor ownedSource
                      reachedPoint fun act decodedAct => by
                        rw [actionEq] at decodedAct
                        exact unintended value act meaning decodedAct
              refine ⟨residualRank + 1, ⟨successor⟩, fun state decodedState => ?_⟩
              rw [successor.decode] at decodedState
              obtain rfl := Option.some.inj decodedState
              exact owes

end Vegas
