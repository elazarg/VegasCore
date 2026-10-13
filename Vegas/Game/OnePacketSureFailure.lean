/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketEventSuccess
import Vegas.Game.ServiceWithheldForfeit
import Vegas.Game.ServiceRevealDecode
import Vegas.Game.OnePacketActorRecord

/-! # Events that fail on every continuation

**Readout.** On a completed configuration of the default runtime, a failure in
the output of a disclosure owned by `who` is recorded by the typed readout: the
disclosure is a reveal cell of `who` reading that output, so the readout
records a failed reveal of `who` and a failure of the disclosure
(`Vegas.eventFailedReadout_of_publicationFailure`). Every binding event is a
commitment cell of the terminal context
(`Vegas.terminalRefsWith_commitmentCell`), so a failed binding output together
with a failed reveal of `who` is an event-level failed readout
(`Vegas.eventFailedReadout_of_bindingFailure`).

**Doomed disclosures.** A disclosure whose resolution of an opening already
publishes a failure on the store at which it is ready, because the bound value
failed or a deferred check rejects it, publishes a failure whatever completes
it: a refusal always fails, and the fields the resolution reads are fixed once
it is ready (`Vegas.doomedDisclosure_output_failure`). So, under a scheduler
that completes play, every terminal continuation of a history at which such a
disclosure of `who` is pending is an event-level failed history of `who` for
it, whatever anyone plays (`Vegas.doomedDisclosure_eventFailedHistory`), and
every local law at a site whose belief holds only such histories fails surely
(`Vegas.doomedDisclosure_localFailure_eq_one`). The site-level form asks for
the condition at every history of the belief; deferred checks read only the
author's own commitments and public data, so for a disclosure of the site's
own player the condition is read from that player's information.

**Failing commitments.** The one-packet menu sends no malformed packet
(`Vegas.onePacket_not_malformed`), and a commitment it sends names a prepared
slot of its sender never committed before. When such a commitment of a binding
event leaves its candidate with a fixed meaning that is not openable at the
bound type, as a commitment carrying no value does, the event fails surely:
the owner's one packet is the only commitment the contract can install at the
event (`Vegas.onePacket_accepted_new`), so the event's output is a failure
whether that packet is accepted or the event expires, and the failing decoded
completion makes the owner owe a failure at the decoded point
(`Vegas.FailingCommitmentInvariant`,
`Vegas.failingCommitmentInvariant_transition`). Every terminal continuation is
then an event-level failed history of the owner
(`Vegas.failingCommitment_eventFailedHistory`,
`Vegas.failingCommitment_commit_failed`), and the choice has event-level failure
one at its site (`Vegas.failingCommitment_localFailure_eq_one`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

omit [DecidableEq Player] in
private theorem cast_some {A B : Type} (same : A = B) (value : A) :
    cast (congrArg Option same) (some value) = some (cast same value) := by
  cases same
  rfl

omit [DecidableEq Player] in
private theorem cast_cast_symm {A B : Type} (same : A = B) (value : B) :
    cast same (cast same.symm value) = value := by
  cases same
  rfl

/-- **Every commitment is a terminal cell.** Each binding event of a program
is a commitment cell of its terminal context, owned by the event's owner, whose
terminal reference reads the event's output. -/
theorem terminalRefsWith_commitmentCell {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (event : Fin (eventCount program)) {owner : Player} {payload : L.Ty},
      outputLayout program event = .binding owner payload →
      ∃ (name : VarId) (cell : HasVar program.terminalCtx name (.commitment owner payload)),
        ((terminalRefsWith program refs outputs).get cell).field = (outputs event).field
  | _, _, .ret _, _, _, event, _, _, _ => nomatch event
  | _, _, .sample _ _ _ next, refs, outputs, event, owner, payload, layoutEq => by
      refine Fin.cases (fun layoutEq => ?_) (fun later layoutEq => ?_) event layoutEq
      · simp [outputLayout] at layoutEq
      · exact terminalRefsWith_commitmentCell next _ (fun tailEvent => outputs (Fin.succ tailEvent))
          later layoutEq
  | _, _, .commit name commitOwner _ _ next, refs, outputs, event, owner, payload, layoutEq => by
      refine Fin.cases (fun layoutEq => ?_) (fun later layoutEq => ?_) event layoutEq
      · change EventGraph.EventField.binding commitOwner _ = _ at layoutEq
        obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj layoutEq
        exact ⟨name, terminalRef next .here, congrArg EventGraph.FieldRef.field
          (terminalRefsWith_get_terminalRef next _ _ .here)⟩
      · exact terminalRefsWith_commitmentCell next _ (fun tailEvent => outputs (Fin.succ tailEvent))
          later layoutEq
  | _, _, .reveal _ _ _ _ _ _ next, refs, outputs, event, owner, payload, layoutEq => by
      refine Fin.cases (fun layoutEq => ?_) (fun later layoutEq => ?_) event layoutEq
      · simp [outputLayout] at layoutEq
      · exact terminalRefsWith_commitmentCell next _ (fun tailEvent => outputs (Fin.succ tailEvent))
          later layoutEq

variable (setup leaks) in
/-- **A failed disclosure is an event-level failed readout.** On a completed
configuration, if the output of a disclosure owned by `who` is a failure, the
typed readout records a failed reveal of `who` and a failure of the
disclosure. -/
theorem eventFailedReadout_of_publicationFailure (control : (application setup leaks).Control)
    (terminal : control.execution.application.config.cut.Terminal) {who : Player}
    {event : (graph setup).EventId} (owned : (graph setup).actor? event = some who)
    {payload : L.Ty} (outputEq : (graph setup).outputLayout event = .publication payload)
    (failed : (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
      (.publication payload)).get? control.execution.application.config.store =
        some .failure) :
    sourceReadout setup leaks (some control) ∈ EventFailedReadout setup who event := by
  have available : ∀ field,
      (control.execution.application.config.store field).isSome = true := by
    intro field
    cases field with
    | inl input => rfl
    | inr other =>
        exact (control.execution.application.config.output_available other).mpr
          (by rw [terminal]; exact Finset.mem_univ _)
  obtain ⟨source, decoded⟩ := Option.isSome_iff_exists.mp
    (decodeState?_isSome_of_available (terminalRefs setup.program)
      control.execution.application.config.store available)
  have agree : (terminalRefs setup.program).Agrees source
      control.execution.application.config.store :=
    decodeState?_agrees _ _ _ decoded
  obtain ⟨cell, member, cellOwned, field⟩ := terminalRefsWith_revealCell setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
    event (payload := payload) outputEq
  have ownerIs : cell.owner = who := by
    rw [eventOwner?_eq_actor] at cellOwned
    exact Option.some.inj (cellOwned.symm.trans owned)
  have read := agree cell.cell
  obtain ⟨cellOwner, cellPayload, cellName, cellRef⟩ := cell
  dsimp only at read field ownerIs
  change ((terminalRefs setup.program).get cellRef).field = .inr event at field
  have layoutEq := ((terminalRefs setup.program).get cellRef).layout_eq
  rw [field] at layoutEq
  change (graph setup).outputLayout event = _ at layoutEq
  rw [outputEq] at layoutEq
  cases layoutEq
  have same : (terminalRefs setup.program).get cellRef =
      (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
        (.publication payload)) := by
    cases selected : (terminalRefs setup.program).get cellRef with
    | mk selectedField selectedLayout =>
        rw [selected] at field
        cases field
        rfl
  rw [same, failed] at read
  have cellFailed : source.get cellRef = .failure := (Option.some.inj read).symm
  refine ⟨source, (sourceReadout_eq_decode setup leaks control).trans decoded, ?_, ?_⟩
  · exact failedReveals_pos_of_failure setup.program who source
      ⟨cellOwner, payload, cellName, cellRef⟩ member ownerIs cellFailed
  · refine ⟨cellName, .publication payload, cellRef, field, ?_⟩
    change cellValue (source.get cellRef) = PublicationResult.failure
    exact cellFailed

variable (setup leaks) in
/-- **A failed binding with a failed reveal is an event-level failed readout.**
On a completed configuration, if the output of a binding event is a failure and
the readout records a failed reveal of `who`, the readout is an event-level
failed readout of `who` for the binding. -/
theorem eventFailedReadout_of_bindingFailure (control : (application setup leaks).Control)
    (terminal : control.execution.application.config.cut.Terminal) {who : Player}
    {event : (graph setup).EventId} {owner : Player} {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (failed : (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
      (.binding owner payload)).get? control.execution.application.config.store =
        some .failure)
    (revealed : ∀ source, sourceReadout setup leaks (some control) = some source →
      1 ≤ failedReveals setup.program who (publicOutcome setup.program source)) :
    sourceReadout setup leaks (some control) ∈ EventFailedReadout setup who event := by
  have available : ∀ field,
      (control.execution.application.config.store field).isSome = true := by
    intro field
    cases field with
    | inl input => rfl
    | inr other =>
        exact (control.execution.application.config.output_available other).mpr
          (by rw [terminal]; exact Finset.mem_univ _)
  obtain ⟨source, decoded⟩ := Option.isSome_iff_exists.mp
    (decodeState?_isSome_of_available (terminalRefs setup.program)
      control.execution.application.config.store available)
  have read := (sourceReadout_eq_decode setup leaks control).trans decoded
  have agree : (terminalRefs setup.program).Agrees source
      control.execution.application.config.store :=
    decodeState?_agrees _ _ _ decoded
  obtain ⟨name, cellRef, field⟩ := terminalRefsWith_commitmentCell setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
    event outputEq
  change ((terminalRefs setup.program).get cellRef).field = .inr event at field
  have same : (terminalRefs setup.program).get cellRef =
      (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
        (.binding owner payload)) := by
    cases selected : (terminalRefs setup.program).get cellRef with
    | mk selectedField selectedLayout =>
        rw [selected] at field
        cases field
        rfl
  have cellRead := agree cellRef
  rw [same, failed] at cellRead
  refine ⟨source, read, revealed source read, name, .commitment owner payload, cellRef, field, ?_⟩
  change cellValue (source.get cellRef) = PublicationResult.failure
  exact (Option.some.inj cellRead).symm

/-- **A doomed disclosure publishes a failure.** Along a run from a
configuration at which a disclosure is ready and the resolution of an opening
publishes a failure, the disclosure, once completed, has a failure as its
output, whatever action completed it. -/
theorem doomedDisclosure_output_failure {before after : (graph setup).Config}
    (reach : ConfigReaches setup before after) {event : (graph setup).EventId}
    (ready : before.cut.Ready event) {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (doomed : EventGraph.EventCode.resolveOutput? binding checks true before.store =
      some .failure)
    (done : event ∈ after.cut.completed) :
    (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
      (.publication payload)).get? after.store = some .failure := by
  have reads : ((graph setup).nodes event).readFields =
      insert binding.field (EventGraph.GuardCheck.listReadFields checks) :=
    (EventGraph.EventCode.readFields_cast outputEq ((graph setup).nodes event)).symm.trans
      (congrArg EventGraph.EventCode.readFields codeEq)
  have available : ∀ field ∈ insert binding.field (EventGraph.GuardCheck.listReadFields checks),
      (before.store field).isSome = true := fun field read =>
    before.read_available ready (by rw [reads]; exact read)
  have agree : EventGraph.Store.AgreeOn before.store after.store
      (insert binding.field (EventGraph.GuardCheck.listReadFields checks)) := by
    intro field read
    cases field with
    | inl input =>
        rw [EventGraph.Config.store_input, EventGraph.Config.store_input, reach.inputs]
    | inr producer =>
        have present := available (.inr producer) read
        rw [EventGraph.Config.store_output, before.output_available] at present
        rw [EventGraph.Config.store_output, EventGraph.Config.store_output,
          (reach.output_completed present).2]
  have failure (disclose : Bool) : EventGraph.EventCode.resolveOutput? binding checks disclose
      after.store = some .failure := by
    rw [← EventGraph.EventCode.resolveOutput?_congr binding checks disclose _ _ agree]
    cases disclose with
    | false =>
        exact EventGraph.EventCode.resolveOutput?_false_eq_failure binding checks _ available
    | true => exact doomed
  obtain ⟨completion, member, eventEq⟩ := List.mem_map.mp ((after.history_exact event).mpr done)
  obtain ⟨completed, action⟩ := completion
  dsimp only at eventEq
  subst eventEq
  have output := reach.resolve_output member ready.1 (outputEq := outputEq) (codeEq := codeEq)
  simp only [EventGraph.FieldRef.get?]
  change cast _ (after.outputs completed) = _
  rw [output, failure, Option.map_some, cast_some (congrArg EventGraph.EventField.Value outputEq),
    cast_cast_symm]

/-- One protocol transition from an initialized state reaches an initialized
state by one configuration step. -/
private theorem transition_reaches (initial : PMF (application setup leaks).State)
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (before : (application setup leaks).Control) (after : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (reached : after ∈ ((application setup leaks).transition initial horizon scheduler
      (some before) joint).support) :
    ∃ next, after = some next ∧ ConfigStep setup before.execution.application.config
      next.execution.application.config := by
  have stays : ∃ next, after = some next := by
    rcases before with ⟨remaining, current, execution⟩
    cases current with
    | some who => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached⟩
    | none =>
        cases remaining with
        | zero => exact ⟨_, (PMF.mem_support_pure_iff _ _).mp reached⟩
        | succ remaining =>
            obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
            obtain ⟨next, _, same⟩ := PMF.support_map .. ▸ moved
            exact ⟨_, same.symm⟩
  obtain ⟨next, rfl⟩ := stays
  exact ⟨next, rfl, transition_configStep initial horizon scheduler before next joint reached⟩

section OnePacket

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- **A doomed disclosure fails on every continuation.** Under a scheduler that
completes play, let a disclosure of `owner` be ready at a history of the
one-packet game, with the resolution of an opening publishing a failure on its
store. Every terminal history of terminal play from it, under any players, is
an event-level failed history of `owner` for the disclosure. -/
theorem doomedDisclosure_eventFailedHistory
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ who, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    {control : (application setup leaks).Control} (current : history.state = some control)
    {event : (graph setup).EventId} (ready : control.execution.application.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (doomed : EventGraph.EventCode.resolveOutput? binding checks true
      control.execution.application.config.store = some .failure) :
    ∀ final ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralTerminalFrom certificate players history).support,
      final ∈ EventFailedHistory setup leaks bounds horizon scheduler owner event := by
  intro final supported
  let menu := bounds.onePacketMenu (runtime setup) leaks
  have reaches := (menu.information (initialLaw setup) horizon
    scheduler).runBehavioralTerminalFrom_support_closed certificate players
    (fun state => ∃ next, state = some next ∧ ConfigReaches setup
      control.execution.application.config next.execution.application.config)
    (fun state joint _ target holds reached => by
      obtain ⟨before, rfl, reach⟩ := holds
      obtain ⟨next, rfl, step⟩ := transition_reaches (initialLaw setup) horizon scheduler before
        target joint reached
      exact ⟨next, rfl, reach.tail step⟩)
    history ⟨control, current, Relation.ReflTransGen.refl⟩ final supported
  obtain ⟨finalControl, state, reach⟩ := reaches
  have stopped := (menu.information (initialLaw setup) horizon
    scheduler).runBehavioralTerminalFrom_support_terminal certificate players history final
    supported
  rw [state] at stopped
  have trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some finalControl) :=
    state ▸ menu.toRawTrace (initialLaw setup) horizon scheduler final.trace
  have terminal := completes finalControl trace stopped
  have done : event ∈ finalControl.execution.application.config.cut.completed := by
    rw [terminal]
    exact Finset.mem_univ _
  have failed := doomedDisclosure_output_failure reach ready (outputEq := outputEq)
    (codeEq := codeEq) doomed done
  change sourceReadout setup leaks final.state ∈ EventFailedReadout setup owner event
  rw [state]
  exact eventFailedReadout_of_publicationFailure setup leaks finalControl terminal
    (nodeView_resolve_actor outputEq codeEq) outputEq failed

/-- **A doomed disclosure fails surely at a site.** Under a scheduler that
completes play, at a site whose belief holds only histories at which a
disclosure of `owner` is ready with the resolution of an opening publishing a
failure, every local law has event-level failure one for that disclosure. -/
theorem doomedDisclosure_localFailure_eq_one
    [∀ who, DecidableEq (((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).InfoState who)]
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (assessment : ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
      horizon scheduler).BehavioralAssessment)
    {who : Player} (site : ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).InformationSite who)
    (law : PMF (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
      horizon scheduler).Choice who site.1))
    {event : (graph setup).EventId} {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (doomedAt : ∀ history ∈ (assessment.belief who site).support,
      ∃ control, history.1.state = some control ∧
        control.execution.application.config.cut.Ready event ∧
        EventGraph.EventCode.resolveOutput? binding checks true
          control.execution.application.config.store = some .failure) :
    InformationModel.localFailure (2 * horizon + 1) assessment site
      (EventFailedHistory setup leaks bounds horizon scheduler owner event) law = 1 := by
  let model := (bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
    horizon scheduler
  have bounded := (bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup)
    horizon scheduler
  let certificate := bounded.wellFoundedHistories
  apply InformationModel.localFailure_eq_one_of_support
  intro final supported
  rw [InformationModel.localRun_eq_bind, PMF.mem_support_bind_iff] at supported
  obtain ⟨history, inBelief, reached⟩ := supported
  obtain ⟨control, current, ready, doomed⟩ := doomedAt history inBelief
  change final ∈ (model.runBehavioralFrom _ (2 * horizon + 1) history.1).support at reached
  rw [← model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded]
    at reached
  exact doomedDisclosure_eventFailedHistory bounds horizon scheduler completes certificate _
    history.1 current ready outputEq codeEq doomed final reached

end OnePacket

section OnePacketCommitment

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- **Only the owner's one packet can fill a vacant binding.** At a history of
the one-packet game whose binding event `event` of `who` has no accepted
handle, and whose recall of `who` holds an entry emitting the commitment of
`event` to `candidate`, one protocol transition installs, if anything, that
candidate at the event. -/
theorem onePacket_accepted_new {control next : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))}
    (records : RecordsEntry setup leaks who entry (some control))
    (emitted : entry.emitted = some message) (sender : message.sender = who)
    {event : (graph setup).EventId} {candidate : Handle (graph setup)}
    (call : message.payload.call = .commitment event candidate)
    (owned : (graph setup).actor? event = some who)
    (vacant : control.execution.application.accepted (.inr event) = none)
    (joint : Player → Option (application setup leaks).Action)
    (reached : some next ∈ ((application setup leaks).transition (initialLaw setup) horizon
      scheduler (some control) joint).support) :
    ∀ handle, next.execution.application.accepted (.inr event) = some handle →
      handle = candidate := by
  intro installed filled
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have facts := legalFacts setup leaks horizon scheduler _ rawTrace
  have unchanged (same : next.execution.application.accepted (.inr event) =
      control.execution.application.accepted (.inr event)) : installed = candidate := by
    rw [same, vacant] at filled
    cases filled
  rcases control with ⟨remaining, current, execution⟩
  cases current with
  | some responder =>
      cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
      exact unchanged (congrFun (congrArg PublicView.accepted
        ((runtime setup).reactive_respond_application leaks execution responder _).2) _)
  | none =>
      cases remaining with
      | zero =>
          cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
          exact unchanged rfl
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨moved', supported, same⟩ := PMF.support_map .. ▸ moved
          cases Option.some.inj same
          cases command with
          | wait =>
              simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at supported
              cases (PMF.mem_support_pure_iff _ _).mp supported
              exact unchanged rfl
          | activate activated =>
              obtain ⟨updated, chosen, rfl⟩ := PMF.support_map .. ▸ supported
              obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ chosen
              exact unchanged rfl
          | application command =>
              obtain ⟨updated, chosen, rfl⟩ := PMF.support_map .. ▸ supported
              obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ chosen
              exact unchanged (congrFun
                (environmentStep_tables (runtime setup) _ _ command changed).1 _)
          | «include» id =>
              simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at supported
              cases (PMF.mem_support_pure_iff _ _).mp supported
              change (execution.includePending (application setup leaks)
                id).application.accepted (.inr event) = some installed at filled
              unfold ReactiveApplication.Execution.includePending
                MessageNetwork.includePending at filled
              cases found : execution.network.lookup id with
              | none =>
                  simp only [found] at filled
                  exact absurd (filled.symm.trans vacant) (by simp)
              | some envelope =>
                  simp only [found] at filled
                  cases acceptedEq : (application setup leaks).handle execution.application
                      envelope with
                  | none =>
                      simp only [acceptedEq, Option.getD_none] at filled
                      exact absurd (filled.symm.trans vacant) (by simp)
                  | some after =>
                      simp only [acceptedEq, Option.getD_some] at filled
                      have handled := reactiveHandle_call acceptedEq
                      rcases handle_tables_cases (runtime setup) _ _ _ handled with
                        ⟨named, chosen, payloadEq, _, acceptedTable, _⟩ | ⟨acceptedTable, _⟩
                      · change envelope.payload.call = .commitment named chosen at payloadEq
                        by_cases sameEvent : named = event
                        · subst sameEvent
                          rw [acceptedTable, Function.update_self] at filled
                          cases Option.some.inj filled
                          -- The envelope is the owner's one packet for the event.
                          have envelopeSender : envelope.sender = who := by
                            have acts := handle_sender_actor (runtime setup) _ _ _ handled named
                              (by rw [payloadEq]; rfl)
                            exact Option.some.inj (acts.symm.trans owned)
                          have pending := (includePending_found execution.network id envelope
                            found).2.1
                          obtain ⟨other, otherMember, _, _, otherEmitted, _⟩ :=
                            facts.provenance.pending envelope pending
                          rw [envelopeSender] at otherMember
                          obtain ⟨earlier, later, split⟩ := records
                          change execution.recall who = _ at split
                          have output : message ∈ (application setup leaks).outputs
                              (execution.recall who) := by
                            rw [split]
                            exact List.mem_filterMap.mpr ⟨entry, by simp, emitted⟩
                          have named' : message.payload.call.event? (graph setup) = some named := by
                            rw [call]
                            rfl
                          have sameId : envelope.id = message.id := by
                            by_contra different
                            exact onePacket_not_emitsOtherFor bounds trace who named message output
                              named' other otherMember ⟨envelope, otherEmitted,
                                envelopeSender.trans sender.symm, by rw [payloadEq]; rfl,
                                different⟩
                          rw [← facts.inputs who] at output
                          have inInputs := (List.mem_filter.mp output).1
                          have sameEnvelope : envelope = message :=
                            (facts.unique.inputs message inInputs).pending envelope pending sameId
                          rw [sameEnvelope, call] at payloadEq
                          cases payloadEq
                          rfl
                        · rw [acceptedTable, Function.update_of_ne
                            (fun same => sameEvent (Sum.inr.inj same).symm)] at filled
                          exact absurd (filled.symm.trans vacant) (by simp)
                      · rw [acceptedTable] at filled
                        exact absurd (filled.symm.trans vacant) (by simp)

variable (setup leaks) in
/-- **The failing-commitment invariant** after `who` emits, from a recorded
entry, the commitment of its binding event `event` to `candidate`, whose fixed
meaning is not openable at the bound type: the history is legal, the entry is
recorded, and once the event has completed its output is a failure and `who`
owes a failure at the decoded point. -/
def FailingCommitmentInvariant (profile : BehavioralProfile setup.program) (who : Player)
    (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (candidate : Handle (graph setup)) {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding who payload) :
    (application setup leaks).ProtocolState → Prop
  | none => False
  | some control =>
      Nonempty (((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
        horizon scheduler).Trace (some control)) ∧
      RecordsEntry setup leaks who entry (some control) ∧ entry.emitted = some message ∧
      message.sender = who ∧ message.payload.call = .commitment event candidate ∧
      control.execution.application.candidates.lookup candidate ≠ .fresh ∧
      (∀ value, control.execution.application.candidates.lookup candidate ≠
        .openable ⟨payload, value⟩) ∧
      (event ∈ control.execution.application.config.cut.completed →
        (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
          (.binding who payload)).get? control.execution.application.config.store =
            some .failure ∧
        DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program)
          (some control))

/-- **The failing-commitment invariant persists** under every transition of
the one-packet game. -/
theorem failingCommitmentInvariant_transition (profile : BehavioralProfile setup.program)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {candidate : Handle (graph setup)} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    (before after : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (legal : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Legal before joint)
    (holds : FailingCommitmentInvariant setup leaks bounds horizon scheduler profile who entry
      message event candidate outputEq before)
    (reached : after ∈ (((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).step before ⟨joint, legal⟩).support) :
    FailingCommitmentInvariant setup leaks bounds horizon scheduler profile who entry message
      event candidate outputEq after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨⟨trace⟩, records, emitted, sender, call, fixed, notOpenable, settled⟩ := holds
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
          refine ⟨⟨nextTrace⟩, afterRecords, emitted, sender, call, by rw [lookupEq]; exact fixed,
            fun value => by rw [lookupEq]; exact notOpenable value, fun done => ?_⟩
          have owned : (graph setup).actor? event = some who := nodeView_bind_actor outputEq codeEq
          by_cases old : event ∈ control.execution.application.config.cut.completed
          · obtain ⟨failedOutput, owed⟩ := settled old
            refine ⟨?_, decodedHolds_transition (owesFailure_stepClosed who) (initialLaw setup)
              horizon scheduler (some control) (some next) joint owed reached⟩
            obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
              ((control.execution.application.config.output_available event).mpr old)
            rw [← failedOutput]
            exact EventGraph.FieldRef.get?_congr _ _ _
              ((keptStore (.inr event) value stored).trans stored.symm)
          · rcases transition_configStep (initialLaw setup) horizon scheduler control next joint
              reached with same | ⟨completed, ready, action, member⟩
            · rw [same] at done
              exact (old done).elim
            have eventEq : completed = event := by
              rw [control.execution.application.config.step_cut completed ready action _ member,
                EventOrder.Cut.mem_complete] at done
              rcases done with same | earlier
              · exact same.symm
              · exact (old earlier).elim
            subst eventEq
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
              rw [output, cast_some (congrArg EventGraph.EventField.Value outputEq),
                cast_cast_symm]
            have failedResult : (cast (congrArg EventGraph.EventField.Action outputEq) action :
                PublicationResult (L.Val payload)) = .failure := by
              cases result : (cast (congrArg EventGraph.EventField.Action outputEq) action :
                  PublicationResult (L.Val payload)) with
              | failure => rfl
              | success value =>
                  exfalso
                  rw [result] at read
                  obtain ⟨installed, acceptedAt, _, meaning⟩ :=
                    nextFacts.binding.success_provenance _ value read
                  have vacant : control.execution.application.accepted (.inr completed) = none := by
                    cases present : control.execution.application.accepted (.inr completed) with
                    | none => rfl
                    | some found =>
                        exact (old (facts.binding.toAssociationInvariant.accepted_complete
                          completed found present)).elim
                  have same := onePacket_accepted_new bounds horizon scheduler trace records
                    emitted sender call owned vacant joint reached installed acceptedAt
                  subst same
                  rw [lookupEq] at meaning
                  exact notOpenable value meaning
            refine ⟨read.trans (congrArg some failedResult), ?_⟩
            have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
                (PublicationResult.failure : PublicationResult (L.Val payload)) := by
              rw [← failedResult, cast_cast, cast_eq]
            have failing := decodeEventAction_failing_binding setup.program completed.val
              completed.isLt outputEq
            rw [← actionEq] at failing
            obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual profile
              (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler trace control rfl
            have rankEq : completed.val = rank :=
              (ready_iff_rank setup _ rank residual.checkpoint.ordered completed).mp ready
            obtain ⟨successor, reachedPoint⟩ := residual.step completed ready action _ member
            refine ⟨rank + 1, ⟨successor⟩, fun state decoded => ?_⟩
            rw [successor.decode] at decoded
            obtain rfl := Option.some.inj decoded
            have decodedBefore := residual.decode
            generalize residual.lift (ProtocolState.entry residual.program residual.source) =
              point at decodedBefore reachedPoint
            rw [← rankEq] at decodedBefore
            have ownedSource : eventOwner? setup.program ⟨completed.val, completed.isLt⟩ =
                some who := by
              rw [eventOwner?_eq_actor]
              exact owned
            exact ProtocolState.owesFailure_of_decode_failing setup.program setup.namesNodup
              completed.val _ _ _ _ _ _ point completed.isLt who _ _ decodedBefore ownedSource
              failing reachedPoint

/-- **A failing commitment fails on every continuation.** Under a scheduler
that completes play, let `who`, at its turn at a binding event of the
one-packet game, respond with a commitment of that event to a candidate whose
meaning after the response is fixed and not openable at the bound type, such as
a commitment carrying no value. Every terminal history of terminal play from
the state that response reaches, under any players, is an event-level failed
history of `who` for the event: the event's output is a failure, and `who` owes
a failure, so its readout records a failed reveal of `who`. -/
theorem failingCommitment_eventFailedHistory (profile : BehavioralProfile setup.program)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    {event : (graph setup).EventId}
    (turn : execution.application.publicView.ownTurn? who = some event) {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    (response : (application setup leaks).Action) (material : (application setup leaks).Submission)
    (submits : response.transmission = some material) {candidate : Handle (graph setup)}
    (call : (sentEnvelope setup leaks execution who material).payload.call =
      .commitment event candidate)
    (fixed : (execution.respond (application setup leaks) who
      response).application.candidates.lookup candidate ≠ .fresh)
    (notOpenable : ∀ value, (execution.respond (application setup leaks) who
      response).application.candidates.lookup candidate ≠ .openable ⟨payload, value⟩)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (current : history.state = some ⟨remaining, none,
      execution.respond (application setup leaks) who response⟩) :
    ∀ final ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralTerminalFrom certificate players history).support,
      final ∈ EventFailedHistory setup leaks bounds horizon scheduler who event := by
  intro final supported
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  have afterTrace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩) :=
    current ▸ history.trace
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  have start : FailingCommitmentInvariant setup leaks bounds horizon scheduler profile who
      (respondEntry setup leaks execution who response)
      (sentEnvelope setup leaks execution who material) event candidate outputEq
      history.state := by
    rw [current]
    refine ⟨⟨afterTrace⟩, recordsEntry_respond execution who response remaining none,
      by rw [respondEntry_of_transmission execution who response material submits], rfl, call,
      fixed, notOpenable, fun done => ?_⟩
    rw [((runtime setup).reactive_respond_application leaks execution who response).1] at done
    exact (ready.1 done).elim
  have reachedInvariant := model.runBehavioralTerminalFrom_support_closed certificate players _
    (fun state joint legal target holds reached =>
      failingCommitmentInvariant_transition bounds horizon scheduler profile codeEq state target
        joint legal holds reached)
    history start final supported
  have stopped := model.runBehavioralTerminalFrom_support_terminal certificate players history
    final supported
  cases state : final.state with
  | none =>
      rw [state] at reachedInvariant
      exact reachedInvariant.elim
  | some control =>
      have owedState := reachedInvariant
      rw [state] at reachedInvariant stopped
      obtain ⟨⟨finalTrace⟩, _, _, _, _, _, _, settled⟩ := reachedInvariant
      have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
          scheduler).Trace (some control) :=
        menu.toRawTrace (initialLaw setup) horizon scheduler finalTrace
      have terminal := completes control rawTrace stopped
      have done : event ∈ control.execution.application.config.cut.completed := by
        rw [terminal]
        exact Finset.mem_univ _
      obtain ⟨failedOutput, owed⟩ := settled done
      have self : final ∈ (model.runBehavioralTerminalFrom certificate players final).support := by
        have terminalFinal : (menu.protocol (initialLaw setup) horizon scheduler).terminal
            final.state := by
          rw [state]
          exact stopped
        rw [InformationModel.runBehavioralTerminalFrom,
          (menu.protocol (initialLaw setup) horizon scheduler).randomizedBackwardLaw_of_terminal
            terminalFinal]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl
      rw [← state] at owed
      obtain ⟨readout, read, revealed⟩ := decoded_owesFailure_failedReveals menu horizon scheduler
        completes certificate players who final owed final self
      change sourceReadout setup leaks final.state ∈ EventFailedReadout setup who event
      rw [state] at read ⊢
      exact eventFailedReadout_of_bindingFailure setup leaks control terminal outputEq failedOutput
        fun source sourceRead => by
          rw [read] at sourceRead
          cases Option.some.inj sourceRead
          exact revealed

open Classical in
/-- **Committing to a failing commitment fails the event surely.** Under a
scheduler that completes play, at a decision history of `who` at its turn at a
binding event, committing to a response that commits the event to a candidate
whose meaning after the response is fixed and not openable at the bound type,
play for the horizon from the history, under any other policies, reaches only
event-level failed histories of `who` for the event. -/
theorem failingCommitment_commit_failed (profile : BehavioralProfile setup.program)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    {event : (graph setup).EventId}
    (turn : execution.application.publicView.ownTurn? who = some event) {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    (response : (application setup leaks).Action) (material : (application setup leaks).Submission)
    (submits : response.transmission = some material) {candidate : Handle (graph setup)}
    (call : (sentEnvelope setup leaks execution who material).payload.call =
      .commitment event candidate)
    (fixed : (execution.respond (application setup leaks) who
      response).application.candidates.lookup candidate ≠ .fresh)
    (notOpenable : ∀ value, (execution.respond (application setup leaks) who
      response).application.candidates.lookup candidate ≠ .openable ⟨payload, value⟩)
    (info : ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
      horizon scheduler).InfoState who)
    (observed : ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
      horizon scheduler).infoOf who history.trace = info)
    (choice : ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
      horizon scheduler).Choice who info)
    (selected : choice.1 = some response) :
    ∀ final ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralFrom
        (Profile.update (sig := ((bounds.onePacketMenu (runtime setup) leaks).information
          (initialLaw setup) horizon scheduler).behavioralSignature) players who
          ((players who).commit info choice)) (2 * horizon + 1) history).support,
      final ∈ EventFailedHistory setup leaks bounds horizon scheduler who event := by
  subst observed
  intro final supported
  let model := (bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
    horizon scheduler
  let committed := Profile.update (sig := model.behavioralSignature) players who
    ((players who).commit (model.infoOf who history.trace) choice)
  have bounded := (bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup)
    horizon scheduler
  let certificate := bounded.wellFoundedHistories
  have longer : final ∈ (model.runBehavioralFrom committed (1 + (2 * horizon + 1))
      history).support := by
    rw [Nat.add_comm, model.runBehavioralFrom_add committed (2 * horizon + 1) 1 history,
      PMF.mem_support_bind_iff]
    refine ⟨final, supported, ?_⟩
    have terminal : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
        horizon scheduler).terminal final.state := by
      rw [← model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded]
        at supported
      exact model.runBehavioralTerminalFrom_support_terminal certificate committed history final
        supported
    rw [model.runBehavioralFrom_of_terminal committed 1 terminal]
    exact PMF.mem_support_pure_iff _ _ |>.mpr rfl
  rw [model.runBehavioralFrom_add committed 1 (2 * horizon + 1) history,
    PMF.mem_support_bind_iff] at longer
  obtain ⟨middle, stepped, rest⟩ := longer
  have middleState : middle.state = some ⟨remaining, none,
      execution.respond (application setup leaks) who response⟩ := by
    have committedStep := (bounds.onePacketMenu (runtime setup) leaks).run_commit_response
      (initialLaw setup) horizon scheduler players history who remaining execution current
      choice _ selected
    have member : middle.state ∈ (PMF.pure (α := (application setup leaks).ProtocolState)
        (some ⟨remaining, none, execution.respond (application setup leaks) who
          response⟩)).support := by
      rw [← committedStep, PMF.support_map]
      exact ⟨middle, stepped, rfl⟩
    exact (PMF.mem_support_pure_iff _ _).mp member
  rw [← model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded]
    at rest
  exact failingCommitment_eventFailedHistory bounds horizon scheduler profile completes turn
    outputEq codeEq response material submits call fixed notOpenable certificate committed
    middle middleState final rest

open Classical in
/-- **A failing commitment fails surely at a site.** Under a scheduler that
completes play, at a site of `who` whose information is a decision at its turn
at a binding event, if at every history of the site's belief the response of a
choice commits the event to a candidate whose meaning after the response is
fixed and not openable at the bound type, that choice has event-level failure
one. -/
theorem failingCommitment_localFailure_eq_one (profile : BehavioralProfile setup.program)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (assessment : ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
      horizon scheduler).BehavioralAssessment)
    {who : Player} (site : ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).InformationSite who)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId}
    (turn : view.application.publicView.ownTurn? who = some event) {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    (response : (application setup leaks).Action) (material : (application setup leaks).Submission)
    (submits : response.transmission = some material) {candidate : Handle (graph setup)}
    (failingAt : ∀ (execution : (application setup leaks).Execution),
      execution.recall who = past → execution.observe (application setup leaks) who = view →
        (sentEnvelope setup leaks execution who material).payload.call =
          .commitment event candidate ∧
        (execution.respond (application setup leaks) who
          response).application.candidates.lookup candidate ≠ .fresh ∧
        ∀ value, (execution.respond (application setup leaks) who
          response).application.candidates.lookup candidate ≠ .openable ⟨payload, value⟩)
    (choice : ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
      horizon scheduler).Choice who site.1)
    (selected : choice.1 = some response) :
    InformationModel.localFailure (2 * horizon + 1) assessment site
      (EventFailedHistory setup leaks bounds horizon scheduler who event) (PMF.pure choice) =
        1 := by
  apply InformationModel.localFailure_eq_one_of_support
  intro final supported
  rw [InformationModel.localRun_eq_bind, PMF.mem_support_bind_iff] at supported
  obtain ⟨⟨history, observed⟩, _, reached⟩ := supported
  have infoEq := observed
  rw [atSite] at infoEq
  change ((bounds.onePacketMenu (runtime setup) leaks).signals (initialLaw setup) horizon
    scheduler).infoOf who history.trace = _ at infoEq
  rw [(bounds.onePacketMenu (runtime setup) leaks).info] at infoEq
  cases state : history.state with
  | none =>
      rw [state] at infoEq
      cases infoEq
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      rw [state] at infoEq
      by_cases active : actor = some who
      · subst active
        simp only [ReactiveApplication.observe, ↓reduceIte] at infoEq
        obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj infoEq)
        obtain ⟨call, fixed, notOpenable⟩ := failingAt execution pastEq viewEq
        subst pastEq
        subst viewEq
        have localTurn : execution.application.publicView.ownTurn? who = some event := by
          rw [← turn]
          rfl
        exact failingCommitment_commit_failed bounds horizon scheduler profile completes
          assessment.strategy history state localTurn outputEq codeEq response material submits
          call fixed notOpenable site.1 observed choice selected final reached
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at infoEq
        cases infoEq

/-- **The one-packet menu sends no malformed packet.** Every transmitting
response of the one-packet menu is permitted by the count verdict, whose call
check rejects a malformed packet. -/
theorem onePacket_not_malformed {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {response : (application setup leaks).Action}
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who past view)
    {material : (application setup leaks).Submission}
    (submits : response.transmission = some material) (raw : Raw L) :
    material.call.packet ≠ .malformed raw := by
  intro malformed
  rcases ((bounds.mem_onePacketActions (runtime setup) leaks who past view response).mp
      member).2 with silent | ⟨sent, transmits, permitted⟩
  · rw [submits] at silent
    cases silent
  · rw [submits] at transmits
    cases Option.some.inj transmits
    have correct := ((countPermits_eq_true_iff _ _).mp permitted).2.1
    change CountCallCorrect _ ⟨_, ⟨material.call.packet, _, _⟩⟩ at correct
    unfold CountCallCorrect at correct
    simp only [malformed] at correct

end OnePacketCommitment

end Vegas
