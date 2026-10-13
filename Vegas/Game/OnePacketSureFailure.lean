/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketEventSuccess
import Vegas.Game.ServiceWithheldForfeit
import Vegas.Game.ServiceRevealDecode
import Vegas.Game.OnePacketActorRecord

/-! # Disclosures that fail on every continuation

**Readout.** On a completed configuration of the default runtime, a failure in
the output of a disclosure owned by `who` is recorded by the typed readout: the
disclosure is a reveal cell of `who` reading that output, so the readout
records a failed reveal of `who` and a failure of the disclosure
(`Vegas.eventFailedReadout_of_publicationFailure`).

**Doomed disclosures.** A disclosure whose resolution of an opening already
publishes a failure on the store at which it is ready, because the bound value
failed or a deferred check rejects it, publishes a failure whatever completes
it: a refusal always fails, and the fields the resolution reads are fixed once
it is ready (`Vegas.doomedDisclosure_output_failure`). So, under a scheduler
that completes play, every terminal continuation of a history at which such a
disclosure of `who` is pending is an event-level failed history of `who` for
it, whatever anyone plays (`Vegas.doomedDisclosure_eventFailedHistory`), and
every local law at a site whose belief holds only such histories fails surely
(`Vegas.doomedDisclosure_localFailure_eq_one`).
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

end OnePacketCommitment

end Vegas
