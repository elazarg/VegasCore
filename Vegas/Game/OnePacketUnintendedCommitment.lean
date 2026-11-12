module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketReplayExists
public import Vegas.Game.OnePacketSlotMasses
public import Vegas.Game.OnePacketSureFailure
public import Vegas.Game.SourceServiceDecodedDebt
public import Vegas.Game.SourceServiceCompletion
public import Vegas.Compile.EventGraphStep
public import Vegas.Game.SourcePrefixPublications
public import Vegas.Game.SourceDebtObservation

@[expose] public section

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
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames)
    (count : Nat) (refs : ContextRefs layout Γ)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : History Player L)
    (defaults : DefaultHistory Player)
    (state : ProtocolState program) (bound : count < eventCount program) (actor : Player)
    (action : EventGraph.EventField.Action (outputLayout program ⟨count, bound⟩))
    (target : ProtocolState program)
    (decoded : decodeSourcePrefix? program refs registry revelations outputs count store history
      defaults = some state)
    (intended : IntendedFor actor program state)
    (owned : eventOwner? program ⟨count, bound⟩ = some actor)
    (reached : target ∈ (step program state
      (fun _ => decodeEventAction program ⟨count, bound⟩ action)).support)
    (unintended : ∀ act, decodeEventAction program ⟨count, bound⟩ action = some act →
      act ∉ ProtocolView.intendedAvailable actor program (observe actor program state)) :
    OwesFailure actor program target := by
  rcases intendedFor_step actor program state
      (fun _ => decodeEventAction program ⟨count, bound⟩ action) target intended reached with
      after | owed
  · obtain ⟨act, actual, allowed⟩ := intendedAvailable_of_decode_intendedFor program count refs
      registry revelations outputs store history defaults state bound actor action target decoded
      intended owned reached after
    exact (unintended act actual allowed).elim
  · exact owed

end Vegas.SourceProgram.ProtocolState

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)

variable (setup timeouts leaks) in
/-- **The unintended-commitment invariant** after `who` emits, from a recorded
entry, the commitment of its binding event `event` to `candidate`, at a
configuration `start` decoding to `point`: the history is legal, the entry is
recorded, the candidate's meaning is fixed and opens no value whose decoded
action is intended at `who`'s view of `point`; until the event completes the
configuration is `start`, and once it has completed `who` owes a failure at the
decoded point. -/
def UnintendedCommitmentInvariant (profile : BehavioralProfile setup.program) (who : Player)
    (entry : (application setup timeouts leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (candidate : Handle (graph setup)) {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (start : (graph setup).Config) (point : ProtocolState setup.program) :
    (application setup timeouts leaks).ProtocolState → Prop
  | none => False
  | some control =>
      Nonempty (((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup)
        horizon scheduler).Trace (some control)) ∧
      RecordsEntry setup timeouts leaks who entry (some control) ∧ entry.emitted = some message ∧
      message.sender = who ∧ message.payload.call = .commitment event candidate ∧
      control.execution.application.candidates.lookup candidate ≠ .fresh ∧
      (∀ value act, control.execution.application.candidates.lookup candidate =
          .openable ⟨payload, value⟩ →
        decodeEventAction setup.program event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            (some (PublicationResult.success value))) = some act →
        act ∉ ProtocolView.intendedAvailable who setup.program
          (ProtocolState.observe who setup.program point)) ∧
      (event ∉ control.execution.application.config.cut.completed →
        control.execution.application.config = start) ∧
      (event ∈ control.execution.application.config.cut.completed →
        DecodedState setup timeouts leaks profile (ProtocolState.OwesFailure who setup.program)
          (some control))

private theorem cast_some' {A B : Type} (same : A = B) (value : A) :
    cast (congrArg Option same) (some value) = some (cast same value) := by
  subst same
  rfl

private theorem cast_cast_symm' {A B : Type} (same : A = B) (value : B) :
    cast same (cast same.symm value) = value := by
  subst same
  rfl

omit [Fintype Player] in
private theorem store_value_of_path {compiled : EventGraph Player L}
    {before after : compiled.Config}
    (path : Relation.ReflTransGen EventGraph.Config.Step before after)
    (field : compiled.Field) (value : (compiled.layout field).Value)
    (stored : before.store field = some value) : after.store field = some value := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact stored
  | @head first middle moved _ ih =>
      obtain ⟨event, ready, action, supported⟩ := moved
      exact ih (first.step_store_of_some middle event ready action supported field value stored)

/-- **The unintended-commitment invariant persists** under every transition of
the one-packet game, from a configuration decoding to a point intended for
`who` at which `event` is ready. -/
theorem unintendedCommitmentInvariant_transition (profile : BehavioralProfile setup.program)
    {who : Player} {entry : (application setup timeouts leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {candidate : Handle (graph setup)} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {start : (graph setup).Config} {point : ProtocolState setup.program}
    (decoded : decodedPoint setup start = some point)
    (intendedFor : ProtocolState.IntendedFor who setup.program point)
    (startReady : start.cut.Ready event)
    (before after : (application setup timeouts leaks).ProtocolState)
    (joint : Player → Option (application setup timeouts leaks).Action)
    (legal : ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Legal before joint)
    (holds : UnintendedCommitmentInvariant setup timeouts leaks bounds horizon scheduler profile
      who entry
      message event candidate outputEq start point before)
    (reached : after ∈ (((bounds.onePacketMenu timeouts leaks).protocol
      (initialLaw setup) horizon scheduler).step before ⟨joint, legal⟩).support) :
    UnintendedCommitmentInvariant setup timeouts leaks bounds horizon scheduler profile who entry
      message
      event candidate outputEq start point after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨⟨trace⟩, records, emitted, sender, call, fixed, unintended, pending, settled⟩ := holds
      have afterRecords := recordsEntry_transition (timeouts := timeouts) who entry (initialLaw
        setup)
        horizon scheduler _ after joint records reached
      cases after with
      | none => exact afterRecords.elim
      | some next =>
          have nextTrace : ((bounds.onePacketMenu timeouts leaks).protocol
              (initialLaw setup) horizon scheduler).Trace (some next) :=
            .extend trace joint legal reached
          have kept := (keepsFixedCandidates_step timeouts leaks).transition
            (initialLaw setup) horizon scheduler control next joint reached
          have lookupEq := kept candidate fixed
          have owned : (graph setup).actor? event = some who := nodeView_bind_actor outputEq codeEq
          have path := reactive_protocol_graph_steps timeouts leaks (initialLaw setup) horizon
            scheduler control next joint reached
          by_cases old : event ∈ control.execution.application.config.cut.completed
          · have stillDone := EventGraph.Config.Step.path_completed_mono path old
            refine ⟨⟨nextTrace⟩, afterRecords, emitted, sender, call, by rw [lookupEq]; exact fixed,
              fun value act opened => unintended value act (by rw [← lookupEq]; exact opened),
              fun notDone => (notDone stillDone).elim, fun _ => ?_⟩
            exact decodedHolds_transition (owesFailure_stepClosed who) (initialLaw setup)
              horizon scheduler (some control) (some next) joint (settled old) reached
          · have atStart := pending old
            rcases path.cases_head with same | ⟨middle, moved, rest⟩
            · have sameConfig := same.symm
              refine ⟨⟨nextTrace⟩, afterRecords, emitted, sender, call,
                by rw [lookupEq]; exact fixed,
                fun value act opened => unintended value act (by rw [← lookupEq]; exact opened),
                fun _ => sameConfig.trans atStart, fun done => ?_⟩
              rw [sameConfig] at done
              exact (old done).elim
            · obtain ⟨completed, ready, action, member⟩ := moved
              have readyEvent : control.execution.application.config.cut.Ready event :=
                atStart.symm ▸ startReady
              have eventEq : completed = event :=
                setup.eventGraph.sequentialize_ready_unique _ ready readyEvent
              subst completed
              have middleDone : event ∈ middle.cut.completed := by
                rw [control.execution.application.config.step_cut event ready action _ member,
                  EventOrder.Cut.mem_complete]
                exact Or.inl rfl
              have done := EventGraph.Config.Step.path_completed_mono rest middleDone
              refine ⟨⟨nextTrace⟩, afterRecords, emitted, sender, call,
                by rw [lookupEq]; exact fixed,
                fun value act opened => unintended value act (by rw [← lookupEq]; exact opened),
                fun notDone => (notDone done).elim, fun _ => ?_⟩
              have rawTrace : ((application setup timeouts leaks).protocol (initialLaw setup)
                horizon
                  scheduler).Trace (some control) :=
                (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon
                  scheduler trace
              have nextRawTrace : ((application setup timeouts leaks).protocol (initialLaw setup)
                  horizon scheduler).Trace (some next) :=
                (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon
                  scheduler nextTrace
              have facts := legalFacts setup leaks horizon scheduler _ rawTrace
              have nextFacts := legalFacts setup leaks horizon scheduler _ nextRawTrace
              have active : who ∉ control.execution.application.config.defaulted :=
                control.execution.application.active_of_ready_owned facts.quiescent ready owned
              let choice : Option (PublicationResult (L.Val payload)) :=
                cast (congrArg EventGraph.EventField.Action outputEq) action
              have actionEq : action =
                  cast (congrArg EventGraph.EventField.Action outputEq.symm) choice := by
                simp only [choice, cast_cast, cast_eq]
              have primaryEq : middle = control.execution.application.config.complete event ready
                  action (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                    (choice.getD .failure)) := by
                have law := commit_step control.execution.application.config event ready outputEq
                  codeEq choice
                rw [← actionEq] at law
                simp only [active, ite_false] at law
                rw [law, PMF.mem_support_pure_iff] at member
                exact member
              have stored : middle.store (.inr event) = some
                  (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                    (choice.getD .failure)) := by
                rw [primaryEq]
                exact Function.update_self ..
              have retained := store_value_of_path rest (.inr event) _ stored
              have read : (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
                  (.binding who payload)).get? next.execution.application.config.store =
                    some (choice.getD .failure) := by
                simp only [EventGraph.FieldRef.get?]
                rw [retained, cast_some' (congrArg EventGraph.EventField.Value outputEq),
                  cast_cast_symm']
              obtain ⟨residualRank, ⟨residual⟩⟩ := SourceResidual.of_rawTrace profile horizon
                scheduler rawTrace control rfl
              obtain ⟨successor, reachedPoint⟩ := residual.step event ready action middle member
              have decodedBefore : decodedPoint setup control.execution.application.config =
                  some point := atStart ▸ decoded
              have samePoint : residual.lift
                  (ProtocolState.entry residual.program residual.source) = point :=
                Option.some.inj ((decodedPoint_eq residual).symm.trans decodedBefore)
              rw [samePoint] at reachedPoint
              have ownedSource : eventOwner? setup.program ⟨event.val, event.isLt⟩ = some who := by
                rw [eventOwner?_eq_actor]
                exact owned
              have owes : ProtocolState.OwesFailure who setup.program
                  (successor.lift (ProtocolState.entry successor.program successor.source)) := by
                cases result : choice.getD .failure with
                | failure =>
                    have failing := decodeEventAction_failing_binding setup.program event.val
                      event.isLt outputEq choice result
                    rw [← actionEq] at failing
                    exact ProtocolState.owesFailure_of_decode_failing setup.program
                      setup.namesNodup event.val _ _ _ _ _ _ _ point event.isLt who _ _
                      (decodedPoint_decode ready decodedBefore) ownedSource failing reachedPoint
                | success value =>
                    rw [result] at read
                    obtain ⟨installed, acceptedAt, _, meaning⟩ :=
                      nextFacts.binding.success_provenance _ value read
                    have vacant : control.execution.application.accepted (.inr event) = none := by
                      cases present : control.execution.application.accepted (.inr event) with
                      | none => rfl
                      | some found =>
                          exact (old (facts.binding.toAssociationInvariant.accepted_complete
                            event found present)).elim
                    have sameCandidate := onePacket_accepted_new (timeouts := timeouts) bounds
                      horizon scheduler trace records emitted sender call owned vacant joint
                      reached
                      installed acceptedAt
                    subst sameCandidate
                    rw [lookupEq] at meaning
                    have optionEq : choice = some (.success value) := by
                      cases eq : choice with
                      | none => simp only [eq, Option.getD_none] at result; cases result
                      | some result' =>
                          have resultEq : result' = .success value := by
                            simpa only [eq, Option.getD_some] using result
                          exact congrArg some resultEq
                    have chosenAction : action =
                        cast (congrArg EventGraph.EventField.Action outputEq.symm)
                          (some (PublicationResult.success value)) :=
                      actionEq.trans (congrArg _ optionEq)
                    exact ProtocolState.owesFailure_of_decode_not_intendedAvailable setup.program
                      event.val _ _ _ _ _ _ _ point event.isLt who action _
                      (decodedPoint_decode ready decodedBefore) intendedFor ownedSource
                      reachedPoint fun act decodedAct => by
                        rw [chosenAction] at decodedAct
                        exact unintended value act meaning decodedAct
              have primaryHolds : DecodedHolds
                  (ProtocolState.OwesFailure who setup.program) (residualRank + 1) middle := by
                intro state decodedState
                rw [successor.decode, Option.some.injEq] at decodedState
                subst state
                exact owes
              exact successor.decodedHolds_path (owesFailure_stepClosed who) primaryHolds rest

/-- **One-packet commitments are well formed.** A transmitting response of the
one-packet menu that commits an event commits a binding event of the
responder to one of its own prepared slots: the count verdict checks the
call. -/
theorem onePacket_commitment_facts {who : Player}
    {past : List (application setup timeouts leaks).PlayerEntry}
    {view : (application setup timeouts leaks).PlayerView} {response : (application setup timeouts
      leaks).Action}
    (member : response ∈ bounds.onePacketActions timeouts leaks who past view)
    {material : (application setup timeouts leaks).Submission}
    (sends : response.transmission = some material) {event : (graph setup).EventId}
    {candidate : Handle (graph setup)}
    (packet : material.call.packet = .commitment event candidate) :
    candidate.1 = who ∧ (∃ serial, candidate.2 = .prepared serial) ∧
      ∃ (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .binding who payload)
        (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes event) = .bind who payload),
        nodeView (graph setup) event = .bind who payload outputEq codeEq := by
  obtain ⟨_, either⟩ := (bounds.mem_onePacketActions timeouts leaks who past view
    response).mp member
  rcases either with silent | ⟨material', transmits, permitted⟩
  · rw [silent] at sends
    cases sends
  have same : material' = material := Option.some.inj (transmits.symm.trans sends)
  subst same
  obtain ⟨_, correct, _⟩ := (countPermits_eq_true_iff _ _).mp permitted
  unfold CountCallCorrect at correct
  have callEq : ((localEnvelope timeouts) leaks who past view material').payload.call =
      .commitment event candidate := packet
  rw [callEq] at correct
  obtain ⟨owned, _, candidateOwner, prepared, _⟩ := correct
  refine ⟨candidateOwner, prepared, ?_⟩
  unfold bindingOwnedBy at owned
  cases node : nodeView (graph setup) event with
  | bind owner payload outputEq codeEq =>
      rw [outputEq] at owned
      have ownerEq : owner = who := of_decide_eq_true owned
      subst ownerEq
      exact ⟨payload, outputEq, codeEq, rfl⟩
  | resolve owner payload binding checks outputEq codeEq =>
      rw [outputEq] at owned
      cases owned
  | sample payload law outputEq codeEq =>
      rw [outputEq] at owned
      cases owned

variable (setup timeouts leaks) in
/-- **A commitment of an intended value.** A choice at a decision input whose
response commits an event to a prepared slot of the player, whose meaning after
the submission opens a value whose decoded source action is in the intended
menu at the projected view. -/
def IntendedCommitment {who : Player}
    (site : (onePacketInformation setup timeouts leaks bounds horizon scheduler).InformationSite
      who)
    (choice : (onePacketInformation setup timeouts leaks bounds horizon scheduler).Choice who
      site.1) :
    Prop :=
  ∃ (past : List (application setup timeouts leaks).PlayerEntry)
    (view : (application setup timeouts leaks).PlayerView) (response : (application setup timeouts
      leaks).Action)
    (material : (application setup timeouts leaks).Submission) (event : (graph setup).EventId)
    (serial : Nat) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding who payload) (value : L.Val payload),
    site.1 = some (past, view) ∧ choice.1 = some response ∧
      response.transmission = some material ∧
      material.call.packet = .commitment event (who, .prepared serial) ∧
      material.call.candidateAfter who view.application.candidates (.prepared serial) =
        .openable ⟨payload, value⟩ ∧
      sourceOfValue setup event outputEq value ∈
        setup.intendedMenu who (projectView setup timeouts leaks who site.1)

end Vegas
