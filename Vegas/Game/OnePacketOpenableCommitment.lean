/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSureFailure
import Vegas.Game.OnePacketLateSuccess
import Vegas.Compile.EventGraphStep
import Vegas.Game.OnePacketEventFailure
import Vegas.Game.OnePacketBindingSite
import Vegas.Pending.ExclusionInvariant

/-! # Persistent openable binding output and native completion

An unfinished binding retains its original graph configuration. Its first
completion stores either failure, or the committed value in a primitive
completion followed by the runtime's automatic drain. The guarded intended
completion reader identifies the primitive source target because intended
endpoints have no public defaults.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

variable (setup runtime leaks) in
/-- The submitted candidate remains fixed, the unfinished configuration stays
at the original binding, and completion retains either an actual failed output
or a successful primary step followed by native automatic service. -/
def OpenableCommitmentInvariant (who : Player) (entry : (application setup runtime
  leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (candidate : Handle (graph setup)) {payload : L.Ty}
    (_outputEq : (graph setup).outputLayout event = .binding who payload) (value : L.Val payload)
    (sent : (graph setup).Config) (ready : sent.cut.Ready event)
    (action : (graph setup).Action event) :
    (application setup runtime leaks).ProtocolState → Prop
  | none => False
  | some control =>
      Nonempty (((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
        horizon scheduler).Trace (some control)) ∧
      RecordsEntry setup runtime leaks who entry (some control) ∧ entry.emitted = some message ∧
      message.sender = who ∧ message.payload.call = .commitment event candidate ∧
      control.execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
      (event ∉ control.execution.application.config.cut.completed →
        control.execution.application.config = sent) ∧
      (event ∈ control.execution.application.config.cut.completed →
        StoreEventFailed control.execution.application.config.store event ∨
          ∃ primary : EventGraphRuntime.State (graph setup),
            primary.config ∈ (sent.step event ready action).support ∧
              control.execution.application.config = primary.drain.config)

omit [DecidableEq Player] [IExpr.ResultTypes L] [Fintype Player] in
private theorem cast_some_value {A B : Type} (same : A = B) (value : A) :
    cast (congrArg Option same) (some value) = some (cast same value) := by
  cases same
  rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] [Fintype Player] in
private theorem cast_cast_back {A B : Type} (same : A = B) (value : B) :
    cast same (cast same.symm value) = value := by
  cases same
  rfl

/-- An unfinished openable binding retains its failure output or its exact
successful primary completion followed by automatic service. -/
theorem openableCommitmentInvariant_transition {who : Player}
    {entry : (application setup runtime leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {candidate : Handle (graph setup)} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {value : L.Val payload} {sent : (graph setup).Config} {ready : sent.cut.Ready event}
    {action : (graph setup).Action event}
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      Option (PublicationResult (L.Val payload))) = some (.success value))
    (before after : (application setup runtime leaks).ProtocolState)
    (unfinished : ∀ control, before = some control →
      event ∉ control.execution.application.config.cut.completed)
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Legal before joint)
    (holds : OpenableCommitmentInvariant setup runtime leaks bounds horizon scheduler who entry
      message event candidate outputEq value sent ready action before)
    (reached : after ∈ (((bounds.onePacketMenu runtime leaks).protocol
      (initialLaw setup) horizon scheduler).step before ⟨joint, legal⟩).support) :
    OpenableCommitmentInvariant setup runtime leaks bounds horizon scheduler who entry message event
      candidate outputEq value sent ready action after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨⟨trace⟩, records, emitted, sender, call, fixed, frozen, _⟩ := holds
      have pending := unfinished control rfl
      have atSent := frozen pending
      have afterRecords := recordsEntry_transition (runtime := runtime) who entry (initialLaw
        setup) horizon scheduler _ after joint records reached
      cases after with
      | none => exact afterRecords.elim
      | some next =>
          have nextTrace : ((bounds.onePacketMenu runtime leaks).protocol
              (initialLaw setup) horizon scheduler).Trace (some next) :=
            .extend trace joint legal reached
          have kept := (keepsFixedCandidates_step runtime leaks).transition
            (initialLaw setup) horizon scheduler control next joint reached
          have lookupEq := kept candidate (by
            rw [fixed]
            exact fun impossible => by cases impossible)
          have owned : (graph setup).actor? event = some who := nodeView_bind_actor outputEq codeEq
          have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
            horizon scheduler trace
          have nextRawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
            horizon scheduler nextTrace
          have facts := legalFacts setup leaks horizon scheduler _ rawTrace
          have nextFacts := legalFacts setup leaks horizon scheduler _ nextRawTrace
          rcases reactive_protocol_primary_or_stutter runtime leaks (initialLaw setup) horizon
            scheduler control next joint facts.quiescent reached with
            same | ⟨completed, completedReady, found, primary, member, drained⟩
          · refine ⟨⟨nextTrace⟩, afterRecords, emitted, sender, call, lookupEq.trans fixed,
              fun _ => same.trans atSent, fun done => ?_⟩
            rw [same] at done
            exact (pending done).elim
          · have readyEvent : control.execution.application.config.cut.Ready event :=
              atSent.symm ▸ ready
            have eventEq : completed = event :=
              setup.eventGraph.sequentialize_ready_unique _ completedReady readyEvent
            subst completed
            have primaryDone : event ∈ primary.config.cut.completed := by
              rw [control.execution.application.config.step_cut event completedReady found _
                member, EventOrder.Cut.mem_complete]
              exact Or.inl rfl
            have done : event ∈ next.execution.application.config.cut.completed := by
              rw [drained]
              exact EventGraph.Config.Step.path_completed_mono primary.drain_graph_steps primaryDone
            refine ⟨⟨nextTrace⟩, afterRecords, emitted, sender, call, lookupEq.trans fixed,
              fun undone => (undone done).elim, fun _ => ?_⟩
            have active : who ∉ control.execution.application.config.defaulted :=
              control.execution.application.active_of_ready_owned facts.quiescent completedReady
                owned
            let choice : Option (PublicationResult (L.Val payload)) :=
              cast (congrArg EventGraph.EventField.Action outputEq) found
            have foundEq : found =
                cast (congrArg EventGraph.EventField.Action outputEq.symm) choice := by
              simp only [choice, cast_cast, cast_eq]
            have primaryEq : primary.config =
                control.execution.application.config.complete event completedReady found
                  (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                    (choice.getD .failure)) := by
              have law := commit_step control.execution.application.config event completedReady
                outputEq codeEq choice
              rw [← foundEq] at law
              simp only [active, ite_false] at law
              exact (PMF.mem_support_pure_iff _ _).mp (law ▸ member)
            have primaryStored : primary.config.store (.inr event) = some
                (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                  (choice.getD .failure)) := by
              rw [primaryEq]
              exact Function.update_self ..
            have retained : next.execution.application.config.store (.inr event) = some
                (cast (congrArg EventGraph.EventField.Value outputEq.symm)
                  (choice.getD .failure)) := by
              rw [drained]
              exact primary.drain_store_of_some (.inr event) _ primaryStored
            have reads : (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
                (.binding who payload)).get? next.execution.application.config.store =
                some (choice.getD .failure) := by
              simp only [EventGraph.FieldRef.get?]
              rw [retained, cast_some_value (congrArg EventGraph.EventField.Value outputEq),
                cast_cast_back]
            cases result : choice.getD .failure with
            | failure =>
                left
                rw [result] at reads
                exact storeEventFailed_of_ref _ event ⟨.inr event, outputEq⟩ rfl reads rfl
            | success read =>
                right
                rw [result] at reads
                obtain ⟨installed, acceptedAt, _, meaning⟩ :=
                  nextFacts.binding.success_provenance _ read reads
                have vacant : control.execution.application.accepted (.inr event) = none := by
                  cases present : control.execution.application.accepted (.inr event) with
                  | none => rfl
                  | some present' =>
                      exact (pending (facts.binding.toAssociationInvariant.accepted_complete
                        event present' present)).elim
                have same := onePacket_accepted_new (runtime := runtime) bounds horizon scheduler
                  trace records emitted sender call owned vacant joint reached installed acceptedAt
                subst same
                rw [lookupEq, fixed] at meaning
                injection meaning with rawEq
                injection rawEq with _ valueEq
                have optionEq : choice = some (.success read) := by
                  cases eq : choice with
                  | none => simp only [eq, Option.getD_none] at result; cases result
                  | some result' =>
                      have resultEq : result' = .success read := by
                        simpa only [eq, Option.getD_some] using result
                      exact congrArg some resultEq
                have actionEq : found = action := by
                  apply (cast_inj (congrArg EventGraph.EventField.Action outputEq)).mp
                  change choice = _
                  rw [optionEq, successful, valueEq]
                refine ⟨primary, ?_, drained⟩
                rw [← actionEq]
                simpa only [atSent] using member


/-- Native first-completion classification at the monotone target stop. -/
theorem openableCommitment_stop (bounds : MessageBounds (graph setup)) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    (certificate : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
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
      Option (PublicationResult (L.Val payload))) = some (.success value))
    {rank : Nat} (ordered : sent.cut.IsPrefix rank)
    (terminalCompleted : ∀ (final : (application setup runtime leaks).Control),
      ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some final) →
      (application setup runtime leaks).terminal (some final) →
      final.execution.application.config = sent →
      event ∈ final.execution.application.config.cut.completed)
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (holds : OpenableCommitmentInvariant setup runtime leaks bounds horizon scheduler who entry
      message
      event candidate outputEq value sent ready action start.state) :
    ∀ stop ∈ (((bounds.onePacketMenu runtime leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (LateStopped setup runtime leaks bounds horizon scheduler rank) start).support,
      ∃ final, stop.state = some final ∧
        (StoreEventFailed final.execution.application.config.store event ∨
          ∃ primary : EventGraphRuntime.State (graph setup),
            primary.config ∈ (sent.step event ready action).support ∧
              final.execution.application.config = primary.drain.config) := by
  intro stop member
  let menu := bounds.onePacketMenu runtime leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  have rankEq := (ready_iff_rank setup sent rank ordered event).mp ready
  have unfinishedOf : ∀ history : (menu.protocol (initialLaw setup) horizon scheduler).History,
      ¬ LateStopped setup runtime leaks bounds horizon scheduler rank history →
      ∀ control, history.state = some control →
        event ∉ control.execution.application.config.cut.completed := by
    intro history going control state done
    exact going ⟨control, state, event, done, rankEq⟩
  have reachedInvariant := model.runBehavioralUntil_support_closed certificate players
    (LateStopped setup runtime leaks bounds horizon scheduler rank)
    (OpenableCommitmentInvariant setup runtime leaks bounds horizon scheduler who entry message
      event candidate outputEq value sent ready action)
    (fun history going _ joint legal target holds reached =>
      openableCommitmentInvariant_transition (runtime := runtime) bounds horizon scheduler codeEq
        successful history.state target (unfinishedOf history going) joint legal holds reached)
    start holds stop member
  have ends := model.mem_support_runBehavioralUntil certificate players _ start stop member
  cases state : stop.state with
  | none =>
      rw [state] at reachedInvariant
      exact reachedInvariant.elim
  | some final =>
      rw [state] at reachedInvariant
      obtain ⟨⟨finalTrace⟩, _, _, _, _, _, frozen, completion⟩ := reachedInvariant
      refine ⟨final, rfl, completion ?_⟩
      by_contra pending
      have atSent := frozen pending
      rcases ends with ⟨other, otherState, completed, done, sameRank⟩ | ended
      · rw [state] at otherState
        cases Option.some.inj otherState
        have sameEvent : completed = event := Fin.ext (sameRank.trans rankEq.symm)
        subst completed
        exact pending done
      · rw [state] at ended
        exact pending (terminalCompleted final finalTrace ended atSent)


/-- Every completed output is the committed value or a persistent failure. -/
theorem openableCommitmentInvariant_output {who : Player}
    {entry : (application setup runtime leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {candidate : Handle (graph setup)} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {value : L.Val payload} {sent : (graph setup).Config} {ready : sent.cut.Ready event}
    {action : (graph setup).Action event}
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      Option (PublicationResult (L.Val payload))) = some (.success value))
    {control : (application setup runtime leaks).Control}
    (holds : OpenableCommitmentInvariant setup runtime leaks bounds horizon scheduler who entry
      message event candidate outputEq value sent ready action (some control))
    (completed : event ∈ control.execution.application.config.cut.completed) :
    StoreEventFailed control.execution.application.config.store event ∨
      control.execution.application.config.store (.inr event) =
        some (cast (congrArg EventGraph.EventField.Value outputEq.symm)
          (PublicationResult.success value)) := by
  rcases holds.2.2.2.2.2.2.2 completed with failed | ⟨primary, member, drained⟩
  · exact Or.inl failed
  · have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
        (some (PublicationResult.success value)) := by
      rw [← successful]
      simp only [cast_cast, cast_eq]
    let result : PublicationResult (L.Val payload) :=
      (if who ∈ sent.defaulted then none else some (.success value)).getD .failure
    have law := commit_step sent event ready outputEq codeEq (some (.success value))
    rw [← actionEq] at law
    rw [law, PMF.mem_support_pure_iff] at member
    have stored : primary.config.store (.inr event) =
        some (cast (congrArg EventGraph.EventField.Value outputEq.symm) result) := by
      rw [member]
      exact Function.update_self ..
    have retained : control.execution.application.config.store (.inr event) =
        some (cast (congrArg EventGraph.EventField.Value outputEq.symm) result) := by
      rw [drained]
      exact primary.drain_store_of_some (.inr event) _ stored
    by_cases inactive : who ∈ sent.defaulted
    · left
      simp only [result, inactive, ite_true, Option.getD_none] at retained
      apply storeEventFailed_of_ref _ event ⟨.inr event, outputEq⟩ rfl _ rfl
      simp only [EventGraph.FieldRef.get?]
      rw [retained, cast_some_value (congrArg EventGraph.EventField.Value outputEq),
        cast_cast_back]
    · right
      simpa only [result, inactive, ite_false, Option.getD_some] using retained

omit [Fintype Player] in
/-- A configuration one step of the ready event of rank `rank` from a prefix of
`rank` events is a prefix of `rank + 1` events. -/
theorem isPrefix_succ_of_mem_step {sent after : (graph setup).Config} {rank : Nat}
    (ordered : sent.cut.IsPrefix rank) {event : (graph setup).EventId}
    (ready : sent.cut.Ready event) {action : (graph setup).Action event}
    (member : after ∈ (sent.step event ready action).support) :
    after.cut.IsPrefix (rank + 1) := by
  rw [sent.step_cut event ready action _ member]
  exact ordered.complete_at event ready ((ready_iff_rank setup sent rank ordered event).mp ready)

/-- **A slot commitment sets up the invariant.** Along a history of the
one-packet game, at a decision of `who` at its pending binding `event`,
committing at a slot the count verdict permits a source choice encoded as an
action binding the successful value `value` leaves the openable-commitment
invariant, from the configuration of the decision, at the state it reaches. -/
theorem openableCommitmentInvariant_slot {remaining : Nat} {who : Player}
    {execution : (application setup runtime leaks).Execution}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    {event : (graph setup).EventId} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (ready : execution.application.config.cut.Ready event) (slot : Nat)
    (choice : Option (OwnAction Player L)) (action : (graph setup).Action event)
    (encoded : choice.bind (encodeEventAction? setup.program event) = some action)
    {value : L.Val payload}
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      Option (PublicationResult (L.Val payload))) = some (.success value))
    (permitted : countPermits ((application setup runtime leaks).outputs (execution.recall who))
      (slotEnvelope setup runtime leaks who (execution.recall who)
        (execution.observe (application setup runtime leaks) who) event slot) = true)
    (afterTrace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
      horizon scheduler).Trace (some ⟨remaining, none, execution.respond (application setup
        runtime leaks)
        who (slotResponse setup runtime leaks who (execution.recall who)
          (execution.observe (application setup runtime leaks) who) event slot choice)⟩)) :
    ∃ entry message, OpenableCommitmentInvariant setup runtime leaks bounds horizon scheduler who
      entry
      message event (who, .prepared slot) outputEq value execution.application.config ready
      action (some ⟨remaining, none, execution.respond (application setup runtime leaks) who
        (slotResponse setup runtime leaks who (execution.recall who)
          (execution.observe (application setup runtime leaks) who) event slot choice)⟩) := by
  let response := slotResponse setup runtime leaks who (execution.recall who)
    (execution.observe (application setup runtime leaks) who) event slot choice
  obtain ⟨material, transmits, envelope⟩ := slotResponse_transmission setup runtime leaks who
    (execution.recall who) (execution.observe (application setup runtime leaks) who) event node slot
    choice action encoded (by rw [successful]; rfl)
  have call : material.call.packet = .commitment event (who, .prepared slot) :=
    congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
      message.payload.call) envelope
  have sends : response.transmission = some material := transmits
  have bound := slotResponse_of_bind setup runtime leaks who (execution.recall who)
    (execution.observe (application setup runtime leaks) who) event node slot choice action encoded
  rw [successful] at bound
  rw [bound] at transmits
  have materialEq := Option.some.inj transmits.symm
  have submitted : (application setup runtime leaks).submit execution.application who material =
      (execution.respond (application setup runtime leaks) who
        ⟨some ⟨⟨.commitment event (who, .prepared slot), some ⟨payload, value⟩⟩,
          .none⟩⟩).application := by
    rw [materialEq]
    change (application setup runtime leaks).submit execution.application who
      ((runtime.reactiveNormalization leaks).normalize who
        ((application setup runtime leaks).observePlayer execution.application who)
        (ReactiveApplication.ResponseMenu.knownPackets (execution.recall who)
          (execution.observe (application setup runtime leaks) who))
        ⟨⟨.commitment event (who, .prepared slot), some ⟨payload, value⟩⟩, .none⟩) = _
    rw [(runtime.reactiveNormalization leaks).submit]
    rfl
  have fresh : execution.application.candidates.lookup (who, .prepared slot) = .fresh :=
    onePacket_permitted_fresh (runtime := runtime) (control := ⟨remaining, some who, execution⟩)
      trace who event slot
      permitted
  have responded : (execution.respond (application setup runtime leaks) who response).application =
      (application setup runtime leaks).submit execution.application who material := by
    unfold ReactiveApplication.Execution.respond
    rw [sends]
  have sameConfig : (execution.respond (application setup runtime leaks) who
      response).application.config = execution.application.config :=
    (runtime.reactive_respond_application leaks execution who response).1
  refine ⟨respondEntry setup runtime leaks execution who response, sentEnvelope setup runtime
    leaks execution who
    material, ⟨afterTrace⟩, recordsEntry_respond (runtime := runtime) execution who response
      remaining none, ?_, rfl,
    call, ?_, fun _ => sameConfig, fun done => ?_⟩
  · change response.transmission.map (sentEnvelope setup runtime leaks execution who) = _
    rw [sends]
    rfl
  · rw [responded, submitted]
    change (submitStep (Submission.register
      ⟨.commitment event (who, .prepared slot), some ⟨payload, value⟩⟩
      execution.application who) who
      (.commitment event (who, .prepared slot))).candidates.lookup (who, .prepared slot) = _
    simp [submitStep, Submission.register, fresh, CommitmentCandidates.lookup_freeze_self,
      CommitmentCandidates.lookup_prepare_self]
  · rw [sameConfig] at done
    exact (ready.1 done).elim

end Vegas
