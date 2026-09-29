/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterTraffic
import Interaction.ReactiveTrafficState

/-! # Conforming traffic at every retained roster history

The auditor admits all known replays, including copies of the current pending
opening. Authenticity is attributed to the original signed author; sampling
and rebroadcasting do not require a new author identity.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

private theorem roster_opening_permitted
    (execution : (application setup leaks).Execution)
    (owner : Player) (event : (graph setup).EventId)
    (grant : execution.application.serviceGrant = some event)
    (actor : (graph setup).actor? event = some owner)
    (ready : execution.application.config.cut.Ready event)
    (timely : execution.application.WithinDeadline (runtime setup) event)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks owner event
      (execution.observe (application setup leaks) owner) = some (candidate, raw))
    (serial : Nat)
    (counted : serial =
      execution.network.ledger.countP (fun message => message.sender = owner)) :
    permittedRosterEnvelope setup leaks
      ⟨execution.application.publicView, execution.network.ledger,
        ⟨(owner, serial), ⟨.opening event candidate raw, some ⟨candidate, raw⟩⟩⟩⟩ = true := by
  apply (permittedRosterEnvelope_iff setup leaks
    ⟨execution.application.publicView, execution.network.ledger,
      ⟨owner, ⟨(owner, serial), ⟨.opening event candidate raw, some ⟨candidate, raw⟩⟩⟩⟩⟩ rfl).mpr
  refine Or.inr ⟨counted, ?_⟩
  generalize viewEq : execution.observe (application setup leaks) owner = view at opening
  unfold rosterOpening? at opening
  cases node : nodeView (graph setup) event with
  | bind | sample => simp only [node] at opening; cases opening
  | resolve actual payload binding checks outputEq codeEq =>
      have actors := congrArg EventCode.actor codeEq
      rw [EventCode.actor_cast outputEq ((graph setup).nodes event)] at actors
      change (graph setup).actor? event = some actual at actors
      rw [actor] at actors
      cases Option.some.inj actors
      rw [node] at opening
      change (match EventCode.resolveOutput? binding checks true
          view.application.observation.store with
        | none => none
        | some .failure => none
        | some (.success value) => do
            let handle ← view.application.publicView.accepted binding.field
            if handle.1 ≠ owner then none else some (handle, ⟨payload, value⟩)) =
              some (candidate, raw) at opening
      split at opening
      · cases opening
      · cases opening
      · obtain ⟨actual, associated, opening⟩ := Option.bind_eq_some_iff.mp opening
        rw [← viewEq] at associated
        split at opening
        · cases opening
        · rename_i owned
          cases Option.some.inj opening
          change execution.application.serviceGrant = some event ∧
            execution.application.publicView.EventReady event ∧
            execution.application.WithinDeadline (runtime setup) event ∧ _ ∧ _
          refine ⟨grant, (execution.application.publicView_eventReady event).mpr ready,
            timely, rfl, ?_⟩
          rw [node]
          exact ⟨rfl, rfl, not_not.mp owned, associated, rfl⟩

variable [Fintype Player]

/-- Every envelope actually known at a retained activation passes the current
phase checker. The envelope may still be pending and may have a different author. -/
theorem roster_known_permitted (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (message : Message Player (WitnessedPacket (graph setup)))
    (known : message ∈ control.execution.network.known who) :
    permittedRosterEnvelope setup leaks
      ⟨control.execution.application.publicView, control.execution.network.ledger, message⟩ =
        true := by
  let menu := rosterMenu setup leaks bounds rosters
  let profile : BehavioralProfile setup.program :=
    fun owner => RevealOnly.uniformPolicy owner setup.program reveals
  obtain ⟨event, slot, granted, prior, sample, initial, state, selected, initialSupport,
      related, _, grant, offset, serials, published, reached, activated,
      unchanged, _⟩ :=
    roster_decision_phase setup leaks bounds rosters network reveals openable
      who control trace active
  obtain ⟨owner, ownedEvent⟩ := source_owner setup reveals event
  have data := owner_choices_at_prefix setup leaks bounds profile owner initial initialSupport
    setup.program reveals profile (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputEmbedding setup.program)
    (initialRefsBefore setup.program) 0 (CompiledPolicySuffix.whole setup.program profile)
    event.val event.isLt state granted related event (by omega) ownedEvent grant
  obtain ⟨candidate, raw, opening, owned, valid, _, _⟩ := data.2.2
  have covered : ∀ player past view response,
      response ∈ (menu.uniformResponses player past view).support →
        response ∈ rosterActions setup leaks bounds rosters player past view := by
    intro player past view response supported
    exact (menu.uniformResponses_support player past view response).mp supported
  have within : ((rosters event).take slot).count owner ≤ (rosters event).count owner := by
    have counts : (rosters event).count owner = ((rosters event).take slot).count owner +
        ((rosters event).drop slot).count owner := by
      rw [← List.count_append, List.take_append_drop]
    omega
  obtain ⟨chosen, frame, _, _, _⟩ := roster_window_posterior setup leaks bounds rosters
    granted event owner grant ownedEvent candidate raw opening owned valid (offset owner) serials
    published menu.uniformResponses covered network ((rosters event).take slot) within prior reached
  have packets : control.execution.network.Satisfies fun packet =>
      packet.id ∈ granted.network.ledger.map Message.id ∨
        packet = (runtime setup).windowEnvelope leaks owner event candidate raw granted := by
    rw [activated]
    exact frame.packets.learn who sample
  have ledger : control.execution.network.ledger = granted.network.ledger := by
    rw [activated]
    exact frame.ledger
  rcases packets.known who message known with published | canonical
  · apply permittedRosterEnvelope_published setup leaks
      ⟨control.execution.application.publicView, control.execution.network.ledger,
        ⟨who, message⟩⟩
    rwa [ledger]
  · subst message
    obtain ⟨context, source, refs, checkpoint⟩ := related.checkpoint setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) (outputRef setup.program) 0 event.val state granted
    have ready : granted.application.config.cut.Ready event := by
      simpa only [Nat.zero_add, Fin.eta] using checkpoint.ordered.ready (by omega)
    have timely := checkpoint.timely event (by omega) (by rw [ownedEvent]; rfl)
    have admitted := roster_opening_permitted setup leaks granted owner event grant ownedEvent
      ready timely candidate raw opening (granted.network.nextSerial owner)
      (checkpoint.serial_eq_ledger_count setup leaks owner)
    change permittedRosterEnvelope setup leaks
      ⟨control.execution.application.publicView, control.execution.network.ledger,
        (runtime setup).windowEnvelope leaks owner event candidate raw granted⟩ = true
    rw [unchanged, ledger]
    exact admitted

/-- A fresh admitted response creates its authentic current opening with the
publicly expected serial. -/
theorem roster_fresh_traffic (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (response : (application setup leaks).Action)
    (fresh : rosterFresh? setup leaks rosters who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) = some response) :
    ∀ record ∈ (application setup leaks).trafficStep (some control)
      (some ⟨control.remaining, none,
        control.execution.respond (application setup leaks) who response⟩),
      permittedRosterEnvelope setup leaks (envelopeEvidence setup leaks record) = true := by
  let app := application setup leaks
  obtain ⟨event, _, granted, _, _, initial, state, _, initialSupport,
      related, _, grant, _, _, _, _, _, unchanged, _⟩ :=
    roster_decision_phase setup leaks bounds rosters network reveals openable
      who control trace active
  obtain ⟨sentEvent, candidate, raw, sentGrant, ownedEvent, opening, rfl, _⟩ :=
    rosterFresh?_shape setup leaks rosters who _ _ response fresh
  change control.execution.application.serviceGrant = some sentEvent at sentGrant
  rw [unchanged, grant] at sentGrant
  cases Option.some.inj sentGrant
  let profile : BehavioralProfile setup.program :=
    fun owner => RevealOnly.uniformPolicy owner setup.program reveals
  have data := owner_choices_at_prefix setup leaks bounds profile who initial initialSupport
    setup.program reveals profile (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputEmbedding setup.program)
    (initialRefsBefore setup.program) 0 (CompiledPolicySuffix.whole setup.program profile)
    event.val event.isLt state granted related event (by omega) ownedEvent grant
  obtain ⟨expected, expectedRaw, priorOpening, owned, valid, _, _⟩ := data.2.2
  have same := rosterOpening?_application_eq setup leaks who event control.execution granted
    unchanged
  rw [opening, priorOpening] at same
  cases Option.some.inj same
  obtain ⟨context, source, refs, checkpoint⟩ := related.checkpoint setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputRef setup.program) 0 event.val state granted
  have ready : control.execution.application.config.cut.Ready event := by
    rw [unchanged]
    simpa only [Nat.zero_add, Fin.eta] using checkpoint.ordered.ready (by omega)
  have timely : control.execution.application.WithinDeadline (runtime setup) event := by
    rw [unchanged]
    exact checkpoint.timely event (by omega) (by rw [ownedEvent]; rfl)
  have currentGrant : control.execution.application.serviceGrant = some event := by
    rw [unchanged, grant]
  have counted := (roster_fresh_iff_serial setup leaks bounds rosters network reveals openable
    who control trace active event currentGrant ownedEvent candidate raw opening).mp fresh
  have admitted := roster_opening_permitted setup leaks control.execution who event currentGrant
    ownedEvent ready timely candidate raw opening (control.execution.network.nextSerial who) counted
  have packet := (runtime setup).windowOpening_packet leaks who event candidate raw
    control.execution.application (control.execution.network.known who) owned
      (by rw [unchanged]; exact valid)
  have step : app.trafficStep (some control)
      (some ⟨control.remaining, none, control.execution.respond app who
        ((runtime setup).windowOpening leaks event candidate raw)⟩) =
      [⟨control.execution.application.publicView, control.execution.network.ledger,
        ⟨who, ⟨(who, control.execution.network.nextSerial who),
          ⟨.opening event candidate raw, some ⟨candidate, raw⟩⟩⟩⟩⟩] := by
    have actual := app.trafficStep_submit control.execution control.remaining who
      (disclosureSubmission (.opening event candidate raw))
    change _ = [(⟨_, _, ⟨_, ⟨_, app.packet control.execution.application who
      (control.execution.network.known who)
        (disclosureSubmission (.opening event candidate raw))⟩⟩⟩ : app.TrafficRecord)] at actual
    rw [packet] at actual
    exact actual
  intro record member
  rw [step, List.mem_singleton] at member
  subst record
  exact admitted

/-- Every actual retained response emits only permitted signed envelopes. -/
theorem roster_response_traffic (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (response : (application setup leaks).Action)
    (allowed : response ∈ (rosterMenu setup leaks bounds rosters).actions who
      (control.execution.recall who) (control.execution.observe (application setup leaks) who)) :
    ∀ record ∈ (application setup leaks).trafficStep (some control)
      (some ⟨control.remaining, none,
        control.execution.respond (application setup leaks) who response⟩),
      permittedRosterEnvelope setup leaks (envelopeEvidence setup leaks record) = true := by
  let app := application setup leaks
  rcases roster_response_cases setup leaks bounds rosters who _ _ response allowed with
    replay | fresh
  · rcases app.replayPolicy_cases _ _ response replay with rfl | ⟨id, rfl⟩
    · have quiet := app.trafficStep_silent control.execution control.remaining who
      intro record member
      change record ∈ app.trafficStep (some ⟨control.remaining, some who, control.execution⟩)
        (some ⟨control.remaining, none, control.execution.respond app who ⟨none⟩⟩) at member
      rw [quiet] at member
      cases member
    · have found : ∃ message, (control.execution.network.known who).find?
          (fun packet => packet.id = id) = some message := by
        have effective := rosterMenu_in_effective setup leaks bounds rosters who _ _ allowed
        have recalled := app.history_inputRecall (initialLaw setup)
          (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
          ((rosterMenu setup leaks bounds rosters).toRawTrace (initialLaw setup)
            (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) trace)
        have known := ((bounds.menu_mem (runtime setup) leaks who _ _ _).mp effective).1
        obtain ⟨message, member, identified⟩ :=
          (ReactiveApplication.SubmissionNormalization.replayKnown_iff
            (app := app) control.execution who recalled id).mp known
        apply Option.isSome_iff_exists.mp
        exact List.find?_isSome.mpr ⟨message, member, by simp only [identified, decide_true]⟩
      obtain ⟨message, found⟩ := found
      have known := List.mem_of_find?_eq_some found
      have step := app.trafficStep_replay control.execution control.remaining who id message found
      intro record member
      change record ∈ app.trafficStep (some ⟨control.remaining, some who, control.execution⟩)
        (some ⟨control.remaining, none, control.execution.respond app who ⟨some (.replay id)⟩⟩)
          at member
      rw [step, List.mem_singleton] at member
      subst record
      exact roster_known_permitted setup leaks bounds rosters network reveals openable
        who control trace active message known
  · exact roster_fresh_traffic setup leaks bounds rosters network reveals openable
      who control trace active response fresh

/-- Player and environment transitions preserve traffic conformance. -/
theorem roster_step_traffic (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (history : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History)
    (joint : Player → Option (application setup leaks).Action)
    (legal : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Legal
        history.state joint)
    (next : (application setup leaks).ProtocolState)
    (reached : next ∈ (((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).step
        history.state ⟨joint, legal⟩).support) :
    ∀ record ∈ (application setup leaks).trafficStep history.state next,
      permittedRosterEnvelope setup leaks (envelopeEvidence setup leaks record) = true := by
  let app := application setup leaks
  change next ∈ (app.transition (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) history.state joint).support at reached
  cases state : history.state with
  | none => simp only [ReactiveApplication.trafficStep, List.not_mem_nil,
      IsEmpty.forall_iff, implies_true]
  | some control =>
      rw [state] at reached
      cases actor : control.actor with
      | some who =>
          have chosen := legal.2 who
          rw [state] at chosen
          cases selected : joint who with
          | none =>
              rw [selected] at chosen
              exact (chosen actor).elim
          | some response =>
              rw [selected] at chosen
              have allowed := chosen.2
              change response ∈ (rosterMenu setup leaks bounds rosters).actions who
                (control.execution.recall who) (control.execution.observe app who) at allowed
              simp only [ReactiveApplication.transition, actor, selected,
                Option.getD_some, PMF.mem_support_pure_iff _ _] at reached
              subst next
              exact roster_response_traffic setup leaks bounds rosters network reveals openable
                who control (state ▸ history.trace) actor response allowed
      | none =>
          cases countEq : control.remaining with
          | zero =>
              apply (legal.1 _).elim
              rw [state]
              exact ⟨countEq, actor⟩
          | succ remaining =>
              simp only [ReactiveApplication.transition, actor, countEq,
                PMF.support_bind] at reached
              obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp reached
              obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
              have noTraffic := app.trafficStep_environment control.execution updated command
                supported remaining
              cases control with
              | mk count owner execution =>
                  simp only at actor countEq
                  subst count owner
                  rw [noTraffic]
                  simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]

/-- Every authentic partial sample of a retained history contains only
permitted envelopes. In particular, off-path retained histories are not framed. -/
theorem roster_history_traffic (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (history : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).History) :
    ∀ record ∈ (application setup leaks).stateTraffic history.state,
      permittedRosterEnvelope setup leaks (envelopeEvidence setup leaks record) = true := by
  let menu := rosterMenu setup leaks bounds rosters
  rw [← menu.trafficAudit_eq_stateTraffic (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) history]
  rcases history with ⟨state, trace⟩
  induction trace with
  | start => simp only [ReactiveApplication.ResponseMenu.trafficAudit,
      ReactiveApplication.ResponseMenu.toRawTrace, ReactiveApplication.trafficAudit,
      List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | @extend source target prior joint legal realized ih =>
      change ∀ record ∈ menu.trafficAudit (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network) ⟨source, prior⟩ ++
          (application setup leaks).trafficStep source target, _
      intro record member
      rcases List.mem_append.mp member with previous | added
      · exact ih record previous
      · exact roster_step_traffic setup leaks bounds rosters network reveals openable
          ⟨source, prior⟩ joint legal target realized record added

end Vegas
