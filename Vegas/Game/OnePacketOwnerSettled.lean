/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnerRecall
import Vegas.Game.OnePacketFailureBridge
import Vegas.Game.OnePacketOwnerGuard
import Vegas.Game.ServiceBlockView
import Vegas.Game.ServiceRevealDecode

/-! # A debt-free late owner is settled

Along a history of the one-packet game at whose decoded point `who` owes no
failure, and at which an event is ready for which `who` has sent nothing, the
application state is settled for `who` with the slots its own packets name
(`Vegas.ownerSettled_of_trace`):

* no field private to `who` stores a failure: a failed binding event makes its
  owner owe a failure (`Vegas.failedBindingRecord_history`), and so does a
  failed initial binding, a pending obligation from the start
  (`Vegas.InputFailureRecord`, `Vegas.inputFailureRecord_of_trace`);
* every completed reveal of `who` disclosed: a withheld reveal publishes a
  failure, which is a failed reveal (`Vegas.revealRecord_history`);
* a named slot is openable: its commitment named an event that is now complete
  (on the sequential graph the only ready event is the one `who` has not sent
  for), whose binding holds a success, so the accepted handle, which only that
  commitment of `who` can name, is openable; a commitment made without a value
  leaves its slot unopenable.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

section Reaches

/-- **The configuration is reached from its initial configuration** along every
history of the one-packet game. -/
theorem configReaches_of_trace {state}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state) :
    ∀ control : (application setup leaks).Control, state = some control →
      ConfigReaches setup
        (EventGraph.Config.initial control.execution.application.config.inputs)
        control.execution.application.config := by
  induction trace with
  | start => intro _ initialized; cases initialized
  | @extend before after prior joint legal realized ih =>
      intro control initialized
      subst initialized
      cases before with
      | none =>
          change some control ∈ ((application setup leaks).transition (initialLaw setup)
            horizon scheduler none joint).support at realized
          rw [ReactiveApplication.transition, PMF.support_map] at realized
          obtain ⟨drawn, drawnMember, drawnEq⟩ := realized
          cases Option.some.inj drawnEq
          have drawnSupport : drawn ∈ (initialLaw setup).support := drawnMember
          rw [initialLaw, serviceInitialLaw, PMF.support_map] at drawnSupport
          obtain ⟨initial, _, rfl⟩ := drawnSupport
          exact Relation.ReflTransGen.refl
      | some current =>
          have previous := ih current rfl
          have step := transition_configStep (initialLaw setup) horizon scheduler current
            control joint realized
          have reach : ConfigReaches setup current.execution.application.config
              control.execution.application.config := Relation.ReflTransGen.single step
          rw [reach.inputs]
          exact previous.tail step

end Reaches

section Inputs

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- Every position of a context is the position of a variable of it. -/
private theorem exists_inputId : ∀ (Γ : SourceCtx Player L) (input : Fin Γ.length),
    ∃ (name : VarId) (kind : CellTy Player L) (source : HasVar Γ name kind),
      inputId source = input
  | [], input => Fin.elim0 input
  | (name, kind) :: Γ, input => by
      cases input using Fin.cases with
      | zero => exact ⟨name, kind, .here, rfl⟩
      | succ input =>
          obtain ⟨other, otherKind, source, rfl⟩ := exists_inputId Γ input
          exact ⟨other, otherKind, .there source, rfl⟩

variable (setup) in
/-- A failed initial binding of `who` among some inputs. -/
def InputFailed (who : Player) (inputs : (graph setup).Inputs) : Prop :=
  ∃ (input : (graph setup).InputId) (payload : L.Ty)
    (layoutEq : (graph setup).inputLayout input = .binding who payload),
    cast (congrArg EventGraph.EventField.Value layoutEq) (inputs input) = .failure

omit [Fintype Player] in
/-- **A failed initial binding is owed from the start.** -/
theorem owesFailure_entry_of_inputFailed {who : Player} (initial : State L setup.context)
    (failed : InputFailed setup who (setup.eventInputs initial)) :
    ProtocolState.OwesFailure who setup.program
      (ProtocolState.entry setup.program (setup.initialConfig initial)) := by
  obtain ⟨input, payload, layoutEq, failedValue⟩ := failed
  obtain ⟨name, kind, source, rfl⟩ := exists_inputId setup.context input
  have kindEq : cellField kind = .binding who payload :=
    (inputLayout_inputId source).symm.trans layoutEq
  cases kind with
  | publicData | privateInput | publication => cases kindEq
  | commitment owner cellPayload =>
      obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj kindEq
      have encoded := encodeInputs_get initial source
      have cellFailed : initial.get source = .failure := by
        rw [← failedValue]
        exact encoded.symm
      refine Or.inr (ProtocolState.failedBinding_entry setup.program _ ⟨setup.namesNodup,
        ⟨name, cellPayload, source, ?_, cellFailed⟩⟩)
      rw [setup.accounts]
      exact mem_commitmentNames source

variable (setup leaks) in
/-- **The input-failure record.** The configuration decodes at a prefix, and a
failed initial binding of `who` makes `who` owe a failure at the decoded
point. -/
def InputFailureRecord (who : Player) (execution : (application setup leaks).Execution) :
    Prop :=
  ∃ rank, Nonempty (SourceResidual setup (failureProfile setup.program) rank
      execution.application.config) ∧
    (InputFailed setup who execution.application.config.inputs →
      DecodedHolds (ProtocolState.OwesFailure who setup.program) rank
        execution.application.config)

omit [Fintype Player] in
/-- The input-failure record holds at every legal history of the default
runtime. -/
theorem inputFailureRecord_serviceInvariant (who : Player)
    (scheduler : (application setup leaks).Scheduler) :
    (application setup leaks).ServiceInvariant scheduler (InputFailureRecord setup leaks who) where
  respond execution actor action valid := by
    have configEq := ((runtime setup).reactive_respond_application leaks execution actor
      action).1
    unfold InputFailureRecord at valid ⊢
    rw [configEq]
    exact valid
  environment execution next command valid _ reached := by
    obtain ⟨rank, ⟨residual⟩, record⟩ := valid
    have step := environmentStep_configStep setup leaks execution next command reached
    have inputsEq : next.application.config.inputs = execution.application.config.inputs :=
      ConfigReaches.inputs (Relation.ReflTransGen.single step)
    rcases step with same | ⟨event, ready, action, member⟩
    · refine ⟨rank, ?_, fun failed => ?_⟩
      · rw [same]
        exact ⟨residual⟩
      · rw [same] at failed ⊢
        exact record failed
    · have rankEq : event.val = rank :=
        (ready_iff_rank setup _ rank residual.checkpoint.ordered event).mp ready
      obtain ⟨successor, _⟩ := residual.step event ready action _ member
      have advanced : next.application.config.cut.IsPrefix (rank + 1) := by
        rw [execution.application.config.step_cut event ready action _ member]
        exact residual.checkpoint.ordered.complete_at event ready rankEq
      refine ⟨rank + 1, ⟨successor⟩, fun failed => ?_⟩
      rw [inputsEq] at failed
      exact residual.decodedHolds_configStep (fun state joint target owing reached =>
        ProtocolState.owesFailure_step who setup.program state joint target owing reached)
        (record failed) (Or.inr ⟨event, ready, action, member⟩) advanced

omit [Fintype Player] in
/-- The input-failure record holds at every legal history of the default
runtime from its initial law. -/
theorem inputFailureRecord_of_trace (who : Player)
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    InputFailureRecord setup leaks who control.execution :=
  (inputFailureRecord_serviceInvariant who scheduler).history (initialLaw setup) horizon
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      let residual := SourceResidual.initial setup (failureProfile setup.program) initial
      refine ⟨0, ⟨residual⟩, fun failed point decoded => ?_⟩
      have decodedEq : sourceServicePrefix? setup 0
          (State.initial (graph := graph setup) (setup.eventInputs initial)).config = some point :=
        decoded
      rw [residual.decode] at decodedEq
      cases Option.some.inj decodedEq
      exact owesFailure_entry_of_inputFailed initial failed) trace

end Inputs

section Settled

omit [Fintype Player] in
private theorem get?_of_some {kind : EventGraph.EventField Player L}
    (ref : EventGraph.FieldRef (graph setup).layout kind)
    {store : EventGraph.Store (graph setup).layout} {value : ((graph setup).layout ref.field).Value}
    (stored : store ref.field = some value) :
    ref.get? store = some (cast (congrArg EventGraph.EventField.Value ref.layout_eq) value) := by
  rcases ref with ⟨field, layoutEq⟩
  subst layoutEq
  simp [EventGraph.FieldRef.get?, stored]

omit [Fintype Player] in
/-- A field private to `who` is a binding or a private input of `who`. -/
private theorem privateTo_cases {who : Player} {field : (graph setup).Field}
    (privateTo : PrivateTo who field) :
    (∃ payload, (graph setup).layout field = .binding who payload) ∨
      ∃ payload, (graph setup).layout field = .privateInput who payload := by
  obtain ⟨visible, notPublic⟩ := privateTo
  unfold EventGraph.fieldVisibleTo at visible
  unfold EventGraph.fieldPublic at notPublic
  generalize (graph setup).layout field = kind at visible notPublic ⊢
  cases kind with
  | publicData | publication => exact (notPublic trivial).elim
  | binding owner payload =>
      change owner = who at visible
      exact Or.inl ⟨payload, by rw [visible]⟩
  | privateInput owner payload =>
      change owner = who at visible
      exact Or.inr ⟨payload, by rw [visible]⟩

omit [Fintype Player] in
/-- A withheld resolution publishes a failure. -/
private theorem resolveOutput?_false_eq {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {store : EventGraph.Store (graph setup).layout} {result : PublicationResult (L.Val payload)}
    (resolved : EventGraph.EventCode.resolveOutput? binding checks false store = some result) :
    result = .failure := by
  unfold EventGraph.EventCode.resolveOutput? at resolved
  cases bound : binding.get? store with
  | none => simp [bound] at resolved
  | some value =>
      cases accepted : EventGraph.GuardCheck.allAccepted? checks store .failure with
      | none => simp [bound, accepted] at resolved
      | some verdict =>
          simp only [bound, accepted, Bool.false_eq_true, ↓reduceIte, Option.pure_def,
            Option.bind_eq_bind, Option.bind_some, ite_self, Option.some.injEq] at resolved
          exact resolved.symm

/-- **No private field of a debt-free owner stores a failure.** -/
theorem noFailure_of_debtFree {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    {who : Player}
    (debtFree : ∀ point, nativeDecodedState setup leaks (some control) = some point →
      ¬ ProtocolState.OwesFailure who setup.program point) :
    ∀ field, PrivateTo who field → ∀ value,
      control.execution.application.config.store field = some value →
        ¬ ((graph setup).layout field).IsFailure value := by
  intro field privateTo value stored failed
  have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  rcases privateTo_cases privateTo with ⟨payload, layoutEq⟩ | ⟨payload, layoutEq⟩
  · have general : ∀ (kind : EventGraph.EventField Player L)
        (kindEq : kind = .binding who payload) (current : kind.Value), kind.IsFailure current →
          cast (congrArg EventGraph.EventField.Value kindEq) current = .failure := by
      rintro _ rfl current isFailure
      exact isFailure
    have castFailed := general _ layoutEq value failed
    cases field with
    | inl input =>
        obtain ⟨rank, ⟨residual⟩, record⟩ := inputFailureRecord_of_trace who rawTrace
        cases Option.some.inj stored
        exact debtFree _ (decodedPoint_eq residual)
          (record ⟨input, payload, layoutEq, castFailed⟩ _ residual.decode)
    | inr event =>
        obtain ⟨rank, ⟨residual⟩, record⟩ := failedBindingRecord_history
          (failureProfile setup.program) horizon scheduler rawTrace
        have present : (control.execution.application.config.outputs event).isSome := by
          change control.execution.application.config.outputs event = some value at stored
          rw [stored]
          rfl
        have done := (control.execution.application.config.output_available event).mp present
        have read := get?_of_some (⟨.inr event, layoutEq⟩ : EventGraph.FieldRef
          (graph setup).layout (.binding who payload)) stored
        rw [castFailed] at read
        exact debtFree _ (decodedPoint_eq residual)
          (record event done who payload layoutEq read _ residual.decode)
  · have general : ∀ (kind : EventGraph.EventField Player L)
        (_ : kind = .privateInput who payload) (current : kind.Value),
          ¬ kind.IsFailure current := by
      rintro _ rfl current isFailure
      exact isFailure
    exact general _ layoutEq value failed

/-- **Every completed reveal of a debt-free owner disclosed.** -/
theorem disclosed_of_debtFree {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    {who : Player}
    (debtFree : ∀ point, nativeDecodedState setup leaks (some control) = some point →
      ¬ ProtocolState.OwesFailure who setup.program point) :
    ∀ completion ∈ control.execution.application.config.history,
      (graph setup).actor? completion.event = some who → ∀ payload
      (outputEq : (graph setup).outputLayout completion.event = .publication payload),
        cast (congrArg EventGraph.EventField.Action outputEq) completion.action = true := by
  rintro ⟨event, action⟩ member own payload outputEq
  change (graph setup).actor? event = some who at own
  change cast _ action = true
  have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  cases view : nodeView (graph setup) event with
  | bind _ _ bindEq _ => cases bindEq.symm.trans outputEq
  | sample _ _ sampleEq _ => cases sampleEq.symm.trans outputEq
  | resolve owner otherPayload binding checks otherEq codeEq =>
      obtain rfl : otherPayload = payload :=
        EventGraph.EventField.publication.inj (otherEq.symm.trans outputEq)
      obtain rfl : owner = who :=
        Option.some.inj ((nodeView_resolve_actor otherEq codeEq).symm.trans own)
      by_contra withheld
      have falseEq : cast (congrArg EventGraph.EventField.Action outputEq) action = false := by
        simpa using withheld
      have reach := configReaches_of_trace trace control rfl
      have done : event ∈ control.execution.application.config.cut.completed :=
        (control.execution.application.config.history_exact event).mp
          (List.mem_map_of_mem (f := EventGraph.Completion.event) member)
      have output := ConfigReaches.resolve_output reach member
        (by simp [EventGraph.Config.initial, EventOrder.Cut.empty]) (outputEq := otherEq)
        (codeEq := codeEq)
      rw [falseEq] at output
      have present := (control.execution.application.config.output_available event).mpr done
      cases resolved : EventGraph.EventCode.resolveOutput? binding checks false
          control.execution.application.config.store with
      | none =>
          rw [resolved, Option.map_none] at output
          rw [output] at present
          cases present
      | some result =>
          have failedResult := resolveOutput?_false_eq resolved
          subst failedResult
          rw [resolved, Option.map_some] at output
          have read := get?_of_some (⟨.inr event, otherEq⟩ : EventGraph.FieldRef
            (graph setup).layout (.publication otherPayload))
            (store := control.execution.application.config.store) output
          simp only [cast_cast] at read
          obtain ⟨rank, ⟨residual⟩, record⟩ := revealRecord_history (failureProfile setup.program)
            rawTrace
          rcases record event done owner otherPayload binding checks otherEq codeEq view .failure
            read
            with ⟨_, bad, _⟩ | failedReveal
          · cases bad
          · exact debtFree _ (decodedPoint_eq residual)
              (Or.inl (ProtocolState.RevealFailed.indebted _ _ (failedReveal _ residual.decode)))

/-- **One own packet per event.** Two packets a player recalls emitting that
name one event are the same packet. -/
theorem ownOutput_eq_of_event {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (who : Player) (event : (graph setup).EventId)
    {first second : Message Player (WitnessedPacket (graph setup))}
    (firstMember : first ∈ (application setup leaks).outputs (control.execution.recall who))
    (secondMember : second ∈ (application setup leaks).outputs (control.execution.recall who))
    (firstNamed : first.payload.call.event? (graph setup) = some event)
    (secondNamed : second.payload.call.event? (graph setup) = some event) : first = second := by
  have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have clean := (bounds.onePacketMenu_countClean (runtime setup) leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => (runtime setup).countClean_initial leaks state)
    trace
  have signed := signedCommitments_history (runtime setup) leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler rawTrace
  obtain ⟨firstEntry, firstEntryMember, firstEmitted⟩ := List.mem_filterMap.mp firstMember
  obtain ⟨secondEntry, secondEntryMember, secondEmitted⟩ := List.mem_filterMap.mp secondMember
  have firstSender := (signed.emissions who firstEntry firstEntryMember first firstEmitted).1
  have secondSender := (signed.emissions who secondEntry secondEntryMember second
    secondEmitted).1
  have sameId : second.id = first.id := by
    by_contra different
    exact onePacket_not_emitsOtherFor bounds trace who event first firstMember firstNamed
      secondEntry secondEntryMember
      ⟨second, secondEmitted, secondSender.trans firstSender.symm, secondNamed, different⟩
  have firstInput := output_mem_inputs_of_trace bounds trace who first firstMember
  have secondInput := output_mem_inputs_of_trace bounds trace who second secondMember
  have nodup := (clean.1.2.2 who) ▸ List.nodup_range
  exact List.inj_on_of_nodup_map nodup
    (List.mem_filter.mpr ⟨firstInput, by simpa using firstSender⟩)
    (List.mem_filter.mpr ⟨secondInput, by simpa using secondSender⟩)
    (congrArg Prod.snd sameId).symm

end Settled

section Openable

/-- **A named slot of a debt-free late owner is openable.** Along a history at
whose decoded point `who` owes no failure, and at which some ready event is
named by none of `who`'s packets, every prepared slot that a packet of `who`
names is openable. -/
theorem openable_of_pending {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    {who : Player}
    (debtFree : ∀ point, nativeDecodedState setup leaks (some control) = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (pending : ∃ event, control.execution.application.config.cut.Ready event ∧
      ∀ message ∈ (application setup leaks).outputs (control.execution.recall who),
        message.payload.call.event? (graph setup) ≠ some event)
    (serial : Nat)
    (named : NamedSlot who ((application setup leaks).outputs (control.execution.recall who))
      serial) :
    ∃ raw, control.execution.application.candidates.lookup (who, .prepared serial) =
      .openable raw := by
  obtain ⟨message, output, event, call⟩ := named
  have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have clean := (bounds.onePacketMenu_countClean (runtime setup) leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => (runtime setup).countClean_initial leaks state)
    trace
  have signed := signedCommitments_history (runtime setup) leaks (initialLaw setup)
    (serviceInitialLaw_initialized setup) horizon scheduler rawTrace
  obtain ⟨entry, entryMember, entryEmitted⟩ := List.mem_filterMap.mp output
  obtain ⟨k, inside, entryEq⟩ := List.getElem_of_mem entryMember
  obtain ⟨_, _, _, _, _, recorded⟩ := recallRecord_of_trace trace control rfl who k inside
  rw [entryEq] at recorded
  have sender := (signed.emissions who entry entryMember message entryEmitted).1
  rcases entry with ⟨view, ⟨transmission⟩, emitted⟩
  cases transmission with
  | none =>
      change emitted = none at recorded
      change emitted = some message at entryEmitted
      rw [recorded] at entryEmitted
      cases entryEmitted
  | some submission =>
      obtain ⟨other, sent, packetEq, _, prepared⟩ := recorded
      change emitted = some other at sent
      change emitted = some message at entryEmitted
      rw [sent] at entryEmitted
      cases entryEmitted
      change PreparationRecorded who control.execution.application submission.call at prepared
      unfold PreparationRecorded at prepared
      rw [← packetEq, call] at prepared
      obtain ⟨other, handleEq, meaning⟩ := prepared
      cases handleEq
      cases opening : submission.call.opening with
      | some raw =>
          refine ⟨raw, ?_⟩
          rw [meaning, opening]
          rfl
      | none =>
          exfalso
          rw [opening] at meaning
          change control.execution.application.candidates.lookup (who, .prepared serial) =
            .unopenable at meaning
          -- The committed event is complete.
          have input := output_mem_inputs_of_trace bounds trace who message output
          have permitted := (countPermits_eq_true_iff _ _).mp (clean.2 message input)
          obtain ⟨tokenEvent, tokenNamed, tokenEq⟩ :=
            (WitnessedPacket.tokenValid_iff _).mp permitted.1
          rw [call] at tokenNamed
          cases Option.some.inj tokenNamed
          obtain ⟨emittedMessage, emittedEq, _, tokens⟩ := ownedRequestsEmitted_history bounds
            trace who _ entryMember submission rfl
          change emitted = some emittedMessage at emittedEq
          rw [sent] at emittedEq
          cases emittedEq
          have predecessors := tokens event tokenEq
          have done : event ∈ control.execution.application.config.cut.completed := by
            by_contra notDone
            obtain ⟨pendingEvent, pendingReady, unsent⟩ := pending
            have same := setup.eventGraph.sequentialize_ready_unique
              control.execution.application.config.cut ⟨notDone, predecessors⟩ pendingReady
            apply unsent message output
            rw [call, ← same]
            rfl
          -- The committed event is a binding of `who` storing a success.
          have correct := permitted.2.1
          unfold CountCallCorrect at correct
          rw [call] at correct
          have owned := correct.1
          rw [sender] at owned
          obtain ⟨payload, layoutEq⟩ : ∃ payload,
              (graph setup).outputLayout event = .binding who payload := by
            unfold bindingOwnedBy at owned
            revert owned
            cases (graph setup).outputLayout event with
            | binding owner payload =>
                intro owned
                exact ⟨payload, by rw [of_decide_eq_true owned]⟩
            | publicData | privateInput | publication => intro owned; cases owned
          have present := (control.execution.application.config.output_available event).mpr done
          obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp present
          have privateTo : PrivateTo who (.inr event) := privateTo_of_binding layoutEq
          have notFailed := noFailure_of_debtFree trace debtFree (.inr event) privateTo value
            stored
          let ref : EventGraph.FieldRef (graph setup).layout (.binding who payload) :=
            ⟨.inr event, layoutEq⟩
          have read := get?_of_some ref (store := control.execution.application.config.store)
            stored
          have general : ∀ (kind : EventGraph.EventField Player L)
              (kindEq : kind = .binding who payload) (current : kind.Value),
                ¬ kind.IsFailure current → ∃ bound,
                  cast (congrArg EventGraph.EventField.Value kindEq) current = .success bound := by
            rintro _ rfl current notFailure
            cases current with
            | failure => exact (notFailure rfl).elim
            | success bound => exact ⟨bound, rfl⟩
          obtain ⟨bound, success⟩ := general _ layoutEq value notFailed
          change ref.get? control.execution.application.config.store =
            some (cast (congrArg EventGraph.EventField.Value layoutEq) value) at read
          rw [success] at read
          have valid : control.execution.application.BindingInvariant :=
            ((runtime setup).reactiveBindingInvariant leaks).history (initialLaw setup) horizon
              scheduler (fun state member => by
                obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
                exact State.initial_bindingInvariant _) rawTrace
          obtain ⟨handle, accepted, handleOwner, lookup⟩ := valid.success_provenance ref bound read
          obtain ⟨committed, committedOutput, committedCall⟩ :=
            signed.acceptedSigned event handle accepted
          rw [handleOwner] at committedOutput
          have sameMessage := ownOutput_eq_of_event trace who event output committedOutput
            (by rw [call]; rfl) (by rw [committedCall]; rfl)
          subst sameMessage
          rw [call] at committedCall
          cases committedCall
          rw [meaning] at lookup
          cases lookup

/-- **A debt-free late owner is settled.** Along a history of the one-packet
game at whose decoded point `who` owes no failure, and at which some ready event
is named by none of `who`'s packets, the application state is settled for
`who` with the slots its own packets name. -/
theorem ownerSettled_of_trace {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    {who : Player}
    (debtFree : ∀ point, nativeDecodedState setup leaks (some control) = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (pending : ∃ event, control.execution.application.config.cut.Ready event ∧
      ∀ message ∈ (application setup leaks).outputs (control.execution.recall who),
        message.payload.call.event? (graph setup) ≠ some event) :
    OwnerSettled who (NamedSlot who ((application setup leaks).outputs
      (control.execution.recall who))) control.execution.application where
  noFailure := noFailure_of_debtFree trace debtFree
  bindAction completion member owner payload outputEq codeEq :=
    ConfigReaches.binding_output (configReaches_of_trace trace control rfl) member
      (by simp [EventGraph.Config.initial]) outputEq codeEq
  disclosed := disclosed_of_debtFree trace debtFree
  fresh := freshExact_of_trace trace who
  openable := openable_of_pending trace debtFree pending
  initial input := initialCandidates_of_trace trace control rfl who input

end Openable

end Vegas
