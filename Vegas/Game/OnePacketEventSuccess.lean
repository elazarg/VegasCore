module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketFirstActivation
public import Vegas.Game.SourceServiceCanonicalAcceptance
public import Vegas.Pending.ReactiveAcceptedOutput
public import Vegas.Pending.ReactiveGraphSteps
public import Vegas.EventGraph.ObservationStep
public import Interaction.ReactiveMessageIdentity
public import Interaction.ReactiveReceiptIdentity
public import Vegas.Pending.ReactiveStateInvariant

@[expose] public section


/-! # Exact results of accepted canonical packets

Every transmitting canonical decision certifies its actual graph action and typed result,
including opaque bindings and guard-rejected authentic publications. Later physical
transitions retain the fixed meaning and every recorded decision. While the ready event
is unfinished the sequential graph cannot advance. An accepting receipt then certifies
the exact stored result and an actual decision in the authoritative completion history.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Invariant

variable [Fintype Player] (bounds : MessageBounds (graph setup))
  (horizon : Nat) (scheduler : (application setup timeouts leaks).Scheduler)

variable (setup timeouts leaks) in
/-- A recorded canonical packet retains its actual action and typed result. -/
def AcceptanceInvariant (who : Player) (entry : (application setup timeouts leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (sent : (graph setup).Config) (action : (graph setup).Action event)
    (output : ((graph setup).outputLayout event).Value) :
    (application setup timeouts leaks).ProtocolState → Prop
  | none => False
  | some control =>
      Nonempty (((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
        horizon scheduler).Trace (some control)) ∧
      RecordsEntry setup timeouts leaks who entry (some control) ∧
      entry.emitted = some message ∧
      sent.cut.Ready event ∧
      AcceptanceWitness event message sent action output control.execution.application ∧
      (event ∉ control.execution.application.config.cut.completed →
        control.execution.application.config = sent) ∧
      ((message.id, true) ∈ control.execution.receipts →
        control.execution.application.config.outputs event = some output ∧
          ∃ defaultEvent, (⟨event, some action, defaultEvent⟩ : (graph setup).Completion) ∈
            control.execution.application.config.history)

theorem acceptanceInvariant_transition (who : Player)
    (entry : (application setup timeouts leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (sent : (graph setup).Config) (action : (graph setup).Action event)
    (output : ((graph setup).outputLayout event).Value)
    (before after : (application setup timeouts leaks).ProtocolState)
    (joint : Player → Option (application setup timeouts leaks).Action)
    (legal : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Legal before joint)
    (holds : AcceptanceInvariant setup timeouts leaks bounds horizon scheduler who entry message
      event
      sent action output before)
    (reached : after ∈ (((bounds.onePacketMenu timeouts leaks).protocol
      (initialLaw setup) horizon scheduler).step before ⟨joint, legal⟩).support) :
    AcceptanceInvariant setup timeouts leaks bounds horizon scheduler who entry message event
      sent action output after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨⟨trace⟩, records, emitted, sentReady, witness, stable, settled⟩ := holds
      have afterRecords := recordsEntry_transition (timeouts := timeouts) who entry (initialLaw
        setup) horizon scheduler
        _ after joint records reached
      cases after with
      | none => exact afterRecords.elim
      | some next =>
          have nextTrace : ((bounds.onePacketMenu timeouts leaks).protocol
              (initialLaw setup) horizon scheduler).Trace (some next) :=
            .extend trace joint legal reached
          have kept := (keepsFixedCandidates_step timeouts leaks).transition
            (initialLaw setup) horizon scheduler control next joint reached
          have keptStore := (keepsStore_step timeouts leaks).transition
            (initialLaw setup) horizon scheduler control next joint reached
          have configPath := reactive_protocol_graph_steps timeouts leaks (initialLaw setup)
            horizon scheduler control next joint reached
          have historyKept := EventGraph.Config.Step.path_history_prefix configPath
          have retained (old : (message.id, true) ∈ control.execution.receipts) :
              next.execution.application.config.outputs event = some output ∧
                ∃ defaultEvent, (⟨event, some action, defaultEvent⟩ : (graph setup).Completion) ∈
                  next.execution.application.config.history := by
            obtain ⟨stored, defaultEvent, recorded⟩ := settled old
            exact ⟨keptStore (.inr event) output stored, defaultEvent,
              historyKept.subset recorded⟩
          refine ⟨⟨nextTrace⟩, afterRecords, emitted, sentReady, witness.keep kept, ?_, ?_⟩
          · intro unfinished
            have beforePending : event ∉ control.execution.application.config.cut.completed :=
              fun completed => unfinished
                (EventGraph.completed_subset_of_history_prefix _ _ historyKept completed)
            have beforeSent := stable beforePending
            have ready := beforeSent.symm ▸ sentReady
            exact (EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
              (fun _ otherReady => setup.eventGraph.sequentialize_ready_unique _ otherReady ready)
              unfinished configPath).trans
              beforeSent
          · intro receipt
            -- Which transition added the receipt, if any.
            rcases control with ⟨remaining, current, execution⟩
            have rawTrace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
                scheduler).Trace (some ⟨remaining, current, execution⟩) :=
              (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon
                scheduler trace
            have inputRecall := (application setup timeouts leaks).history_inputRecall
              (initialLaw setup) horizon scheduler rawTrace
            have unique := (application setup timeouts leaks).uniqueIds_history scheduler
              (initialLaw setup) horizon _ rawTrace
            cases current with
            | some responder =>
                cases (PMF.mem_support_pure_iff _ _).mp reached
                exact retained receipt
            | none =>
                cases remaining with
                | zero =>
                    cases (PMF.mem_support_pure_iff _ _).mp reached
                    exact retained receipt
                | succ remaining =>
                    obtain ⟨command, _, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨moved', supported, same⟩ := PMF.support_map .. ▸ moved
                    cases same
                    cases command with
                    | wait =>
                        simp only [ReactiveApplication.Execution.environmentStep,
                          PMF.pure_map] at supported
                        cases (PMF.mem_support_pure_iff _ _).mp supported
                        exact retained receipt
                    | activate activated =>
                        obtain ⟨updated, chosen, rfl⟩ := PMF.support_map .. ▸ supported
                        obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ chosen
                        exact retained receipt
                    | application command =>
                        obtain ⟨updated, chosen, rfl⟩ := PMF.support_map .. ▸ supported
                        obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ chosen
                        exact retained receipt
                    | «include» id =>
                        simp only [ReactiveApplication.Execution.environmentStep,
                          PMF.pure_map] at supported
                        cases (PMF.mem_support_pure_iff _ _).mp supported
                        change (message.id, true) ∈
                          (execution.includePending (application setup timeouts leaks)
                            id).receipts at receipt
                        change (execution.includePending (application setup timeouts leaks)
                            id).application.config.outputs event = some output ∧
                          ∃ defaultEvent, (⟨event, some action, defaultEvent⟩ :
                            (graph setup).Completion) ∈
                            (execution.includePending (application setup timeouts leaks)
                              id).application.config.history
                        unfold ReactiveApplication.Execution.includePending
                          MessageNetwork.includePending at receipt retained ⊢
                        cases found : execution.network.lookup id with
                        | none =>
                            simp only [found] at receipt retained ⊢
                            exact retained receipt
                        | some envelope =>
                            simp only [found] at receipt retained ⊢
                            cases accepted : (application setup timeouts leaks).handle
                                execution.application envelope with
                            | none =>
                                simp only [accepted, Option.getD_none] at receipt retained ⊢
                                rcases List.mem_append.mp receipt with old | new
                                · exact retained old
                                · simp at new
                            | some accepted' =>
                                simp only [accepted, Option.getD_some] at receipt retained ⊢
                                rcases List.mem_append.mp receipt with old | new
                                · exact retained old
                                · obtain ⟨idEq, -⟩ := Prod.mk.inj (List.mem_singleton.mp new)
                                  -- The included envelope is the message.
                                  obtain ⟨earlier, later, split⟩ := records
                                  change execution.logs who = _ at split
                                  have recalledOutput : message ∈
                                      (application setup timeouts leaks).outputs
                                        (execution.logs who) := by
                                    rw [split]
                                    exact List.mem_filterMap.mpr ⟨entry, by simp, emitted⟩
                                  rw [← inputRecall who] at recalledOutput
                                  have member := (List.mem_filter.mp recalledOutput).1
                                  have named : envelope.id = id := by
                                    have spec := List.find?_some found
                                    simpa using spec
                                  have same : envelope = message :=
                                    (unique.inputs message member).lookup id envelope found
                                      (named.trans idEq.symm)
                                  subst same
                                  obtain ⟨native, call, nextEq⟩ := reactiveHandle_call accepted
                                  obtain ⟨named', eventNamed, ready, _⟩ :=
                                    handle_config_mem_step timeouts _ _ _ call
                                  have eventEq : named' = event := by
                                    rcases witness with ⟨_, _, _, _, callEq, _⟩ |
                                      ⟨_, _, _, _, _, _, _, _, _, callEq, _⟩
                                    · change envelope.payload.call.event? (graph setup) =
                                        some named' at eventNamed
                                      rw [callEq] at eventNamed
                                      exact (Option.some.inj eventNamed).symm
                                    · change envelope.payload.call.event? (graph setup) =
                                        some named' at eventNamed
                                      rw [callEq] at eventNamed
                                      exact (Option.some.inj eventNamed).symm
                                  subst named'
                                  refine ⟨?_, witness.reactive_decision timeouts leaks
                                    (stable ready.1) accepted⟩
                                  rw [← nextEq]
                                  exact native.drain_store_of_some (.inr event) output
                                    (witness.output_eq timeouts (stable ready.1) call)


/-- Every transmitting canonical decision starts the invariant for its actual typed result. -/
theorem acceptanceInvariant_respond {remaining : Nat} {who : Player}
    {execution : (application setup timeouts leaks).Execution}
    (trace : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (action : (graph setup).Action event) (material : (application setup timeouts leaks).Submission)
    (submits : ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
      (execution.observe (application setup timeouts leaks) who) event action).transmission =
        some material)
    (after : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, none, execution.respond (application setup timeouts leaks)
        who ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
          (execution.observe (application setup timeouts leaks) who) event action)⟩)) :
    ∃ output, AcceptanceInvariant setup timeouts leaks bounds horizon scheduler who
      (respondEntry setup timeouts leaks execution who ((canonicalServiceDecision timeouts)
        leaks who
        (execution.logs who) (execution.observe (application setup timeouts leaks) who) event
          action))
      (sentEnvelope setup timeouts leaks execution who material) event execution.application.config
      action output (some ⟨remaining, none, execution.respond (application setup timeouts leaks) who
        ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
          (execution.observe (application setup timeouts leaks) who) event action)⟩) := by
  have rawTrace := (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon
    scheduler trace
  have serials := (application setup timeouts leaks).serialsBeforeNext_history scheduler
    (initialLaw setup) horizon rawTrace
  have identifiers := (application setup timeouts leaks).receipt_identifiers_history
    (initialLaw setup) horizon scheduler _ rawTrace
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have respondApplication : (execution.respond (application setup timeouts leaks) who
      ((canonicalServiceDecision timeouts) leaks who (execution.logs who)
        (execution.observe (application setup timeouts leaks) who) event action)).application =
      (application setup timeouts leaks).submit execution.application who material := by
    unfold ReactiveApplication.Execution.respond
    rw [submits]
  obtain ⟨output, witness⟩ := canonical_response_witness execution who event turn action material
    submits
  refine ⟨output, ⟨⟨after⟩,
    recordsEntry_respond (timeouts := timeouts) execution who _ remaining none,
    by rw [respondEntry_of_transmission (timeouts := timeouts) execution who _ material submits],
      ready, ?_, ?_, ?_⟩⟩
  · rw [respondApplication]
    exact witness
  · intro _
    exact ((reactive_respond_application timeouts) leaks execution who _).1
  · intro receipt
    exfalso
    change (_, true) ∈ execution.receipts at receipt
    have member : (who, execution.network.nextSerial who) ∈ execution.receipts.map Prod.fst :=
      List.mem_map.mpr ⟨_, receipt, rfl⟩
    rw [identifiers] at member
    obtain ⟨ledgerMessage, inLedger, sameId⟩ := List.mem_map.mp member
    have lower := serials.ledger ledgerMessage inLedger
    rw [sameId] at lower
    exact Nat.lt_irrefl _ lower

end Invariant

end Vegas
