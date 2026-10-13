/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketEventSuccess
import Vegas.Game.ServiceWithheldForfeit
import Vegas.Game.ServiceRevealDecode

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

end Vegas
