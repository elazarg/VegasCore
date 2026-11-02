/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCompletionCases
import Vegas.Game.OnePacketReplayExists
import Vegas.Game.OnePacketOwnSubmissions
import Vegas.Game.OnePacketIntendedProjection
import Vegas.Game.SourceServiceDecodedDebt
import Vegas.Pending.ExclusionEvidence
import Vegas.Game.SourcePrefixPublications

/-! # Regular histories with public default evidence

A public record says every foreign owner remains active. This public property
reaches back along native transitions. On initialized histories it entails
accepted handles at completed foreign bindings and absence of failed foreign
source publications.

Intended focal prefixes supply the focal owner's activity. Together with the
public record this places a regular endpoint in the clear region, where the
native finite-path executor stutters or performs one primitive completion.
Actual owned records and positive intended content then preserve the source
intended predicate. No general restriction to one native completion is assumed.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- **Withheld reveals fail.** At a decoded state at a reveal of `who`, a step
with a failing decision makes `who`'s reveal fail. -/
theorem revealFailed_of_decode_failing {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (defaults : DefaultHistory Player) (state : ProtocolState program) (bound : count <
        eventCount program) (who : Player)
      (payload : L.Ty) (choice : Option (OwnAction Player L)) (target : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history defaults =
          some state →
      eventOwner? program ⟨count, bound⟩ = some who →
      outputLayout program ⟨count, bound⟩ = .publication payload → Failing choice →
      target ∈ (step program state (fun _ => choice)).support →
      RevealFailed who program target := by
  induction program with
  | ret _ =>
      intro count _ _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro count refs registry revelations outputs store history defaults state bound who
        payload choice
        target decoded owned layout failing reached
      cases count with
      | zero => cases owned
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history defaults rest (Nat.lt_of_succ_lt_succ bound) who
            payload
            choice after read owned layout failing supported
  | commit name owner fresh guard next ih =>
      intro count refs registry revelations outputs store history defaults state bound who
        payload choice
        target decoded owned layout failing reached
      cases count with
      | zero => cases layout
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history defaults rest (Nat.lt_of_succ_lt_succ bound) who
            payload
            choice after read owned layout failing supported
  | reveal published owner name fresh source unresolved next ih =>
      intro count refs registry revelations outputs store history defaults state bound who
        payload choice
        target decoded owned layout failing reached
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same : target = Sum.inr (entry next (revealSuccessor published source
              ⟨cells, registry, revelations, history, defaults⟩ (OwnAction.disclosure choice))) :=
            (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          refine Or.inl ⟨rfl, ?_⟩
          rw [base_entry, failing.2]
          exact disclosureResult_false published source _
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact Or.inr (ih count _ _ _ _ store history defaults rest (Nat.lt_of_succ_lt_succ
            bound) who
            payload choice after read owned layout failing supported)

end ProtocolState

end Vegas.SourceProgram

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}

/-- **Intended points are forced** for every player. -/
theorem forcedPoint_of_intended (who : Player) {point : ProtocolState setup.program}
    (intended : ProtocolState.Intended setup.program point) : ForcedPoint setup who point :=
  ⟨fun failed => ProtocolState.Intended.not_owesFailure who setup.program point intended
      (Or.inl (ProtocolState.RevealFailed.indebted setup.program point failed)),
    fun other _ => ⟨ProtocolState.not_excluded_of_intended other setup.program point intended,
      ProtocolState.Intended.not_owesFailure other setup.program point intended⟩⟩

/-- A binding event's graph actor is its owner. -/
theorem actor_of_binding {event : (graph setup).EventId} {owner : Player} {payload : L.Ty}
    (layout : (graph setup).outputLayout event = .binding owner payload) :
    (graph setup).actor? event = some owner := by
  cases view : nodeView (graph setup) event with
  | bind owner' payload' outputEq codeEq =>
      rw [nodeView_bind_actor outputEq codeEq]
      rw [outputEq] at layout
      cases layout
      rfl
  | resolve _ _ _ _ outputEq _ =>
      rw [outputEq] at layout
      cases layout
  | sample _ _ outputEq _ =>
      rw [outputEq] at layout
      cases layout

variable (setup runtime) in
/-- Every foreign owner's authoritative public default status is clear. -/
def PublicRecord {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (who : Player) (control : (application setup runtime leaks).Control) : Prop :=
  ∀ other, other ≠ who → other ∉ control.execution.application.config.defaulted

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

omit [Fintype Player] in
/-- Public defaults are permanent, so a later public record holds earlier. -/
theorem publicRecord_of_transition {who : Player}
    {current next : (application setup runtime leaks).Control}
    (joint : Player → Option (application setup runtime leaks).Action)
    (realized : some next ∈ ((application setup runtime leaks).transition (initialLaw setup) horizon
      scheduler (some current) joint).support)
    (record : PublicRecord setup runtime who next) : PublicRecord setup runtime who current := by
  intro other different excluded
  exact record other different (runtime.reactive_protocol_defaulted_mono leaks (initialLaw setup)
    horizon scheduler current next joint realized excluded)

omit [Fintype Player] in
/-- A forced source decoding has no publicly defaulted foreign owner. -/
theorem publicRecord_of_forced (who : Player)
    (control : (application setup runtime leaks).Control)
    (forced : ForcedState setup runtime leaks who (some control)) :
    PublicRecord setup runtime who control := by
  obtain ⟨point, decoded, forcedPoint⟩ :=
    (forcedState_iff_decodedPoint (runtime := runtime) control).mp forced
  intro other different excluded
  apply (forcedPoint.2 other different).1
  change other ∈ ProtocolState.defaulted setup.program point
  rw [ProtocolState.defaulted_eq_defaults, decodedPoint_defaults decoded]
  exact excluded

/-- A completed foreign binding has an accepted handle at an initialized public record. -/
theorem PublicRecord.bindingAccepted {who : Player}
    {control : (application setup runtime leaks).Control}
    (record : PublicRecord setup runtime who control)
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (layout : (graph setup).outputLayout event = .binding owner payload)
    (different : owner ≠ who) (completed : event ∈
      control.execution.application.config.cut.completed) :
    control.execution.application.accepted (.inr event) ≠ none := by
  intro missing
  have raw := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  change ((runtime.reactiveApplication leaks).protocol (serviceInitialLaw setup .sequential)
    horizon scheduler).Trace (some control) at raw
  rw [serviceInitialLaw_eq_inputs setup] at raw
  have valid := ExclusionEvidence.history runtime leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler raw
  apply record owner different
  exact (valid.defaulted_zero owner).mpr ⟨event, actor_of_binding layout,
    Or.inl ((control.execution.application.publicView_missedBinding event owner payload layout).mpr
      ⟨completed, missing⟩)⟩

/-- An initialized public record rules out every failed foreign source publication. -/
theorem PublicRecord.not_revealFailed {who other : Player}
    {control : (application setup runtime leaks).Control}
    (record : PublicRecord setup runtime who control)
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (different : other ≠ who) {point : ProtocolState setup.program}
    (decoded : decodedPoint setup control.execution.application.config = some point) :
    ¬ ProtocolState.RevealFailed other setup.program point := by
  intro failed
  obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime)
    (failureProfile setup.program) (bounds.onePacketMenu runtime leaks) horizon scheduler trace
      control rfl
  have same := Option.some.inj ((decodedPoint_eq residual).symm.trans decoded)
  have valid := publicationsDefaulted_of_decode
    (⟨some control, trace⟩ : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).History)
    control rfl residual.checkpoint.ordered residual.decode
  have excluded := ProtocolState.RevealFailed.excluded setup.program point (same ▸ valid) failed
  apply record other different
  change other ∈ ProtocolState.defaulted setup.program point at excluded
  rw [ProtocolState.defaulted_eq_defaults, decodedPoint_defaults decoded] at excluded
  exact excluded

/-- **Regular histories stay intended.** For a well-formed setup, along a
regular history ending at a public record for `who`, along which `who`'s own
completions decode to intended actions, the decoded point is a point of the
intended game. -/
theorem intended_of_regular (wellFormed : setup.WellFormed)
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) : ∀ {state}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state)
    (control : (application setup runtime leaks).Control), state = some control →
    PublicRecord setup runtime who control →
    RegularTrace setup runtime leaks bounds horizon scheduler assessment who trace →
    OwnCompletionsIntended (runtime := runtime) (bounds := bounds) (horizon := horizon) (scheduler
      := scheduler)
      who trace →
    ∃ point, decodedPoint setup control.execution.application.config = some point ∧
      ProtocolState.Intended setup.program point
  | _, .start, _, current, _, _, _ => by cases current
  | _, .extend (source := before) prior joint legal realized, control, current, record, regular,
      ownIntended => by
      have regularPrior := regular.1
      have ownPrior := ownIntended.1
      have recursive := fun next same recordNext =>
        intended_of_regular wellFormed assessment who prior next same recordNext regularPrior
          ownPrior
      subst current
      have realizedRaw : some control ∈ ((application setup runtime leaks).transition
        (initialLaw setup) horizon scheduler before joint).support := realized
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state => some
            (⟨horizon, none, ReactiveApplication.Execution.initial (application setup runtime leaks)
              state⟩ : (application setup runtime leaks).Control)).support at realizedRaw
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realizedRaw
          cases Option.some.inj same
          obtain ⟨initial, initialMem, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨_, decodedPoint_initial initial, ProtocolState.intended_entry setup.program _
            (setup.initialConfig_intended wellFormed initialMem)
            (wellFormed.guardsSatisfiable initial initialMem)⟩
      | some current =>
          have recordCurrent := publicRecord_of_transition joint realizedRaw record
          obtain ⟨point, decodedCurrent, intended⟩ := recursive current rfl recordCurrent
          have forcedCurrent : ForcedState setup runtime leaks who (some current) :=
            (forcedState_iff_decodedPoint (runtime := runtime) current).mpr
              ⟨point, decodedCurrent, forcedPoint_of_intended who intended⟩
          obtain ⟨rank, ⟨afterResidual⟩⟩ := protocol_sourceResidual (runtime := runtime)
            (failureProfile setup.program) (bounds.onePacketMenu runtime leaks) horizon scheduler
              (prior.extend joint legal realized) control rfl
          have decodedAfter := decodedPoint_eq afterResidual
          have focalActive := ProtocolState.not_excluded_of_intendedFor who setup.program _
            (ownIntended.current control rfl _ decodedAfter)
          have clear : control.execution.application.config.defaulted = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro player excluded
            by_cases same : player = who
            · subst player
              apply focalActive
              rw [ProtocolState.defaulted_eq_defaults, decodedPoint_defaults decodedAfter]
              exact excluded
            · exact record player same excluded
          have priorClear : current.execution.application.config.defaulted = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro player excluded
            have later := runtime.reactive_protocol_defaulted_mono leaks (initialLaw setup)
              horizon scheduler current control joint realizedRaw excluded
            rw [clear] at later
            exact Finset.notMem_empty player later
          cases acting : current.actor with
          | some actor =>
              rw [transition_respond (runtime := runtime) current acting joint,
                PMF.mem_support_pure_iff] at realizedRaw
              cases Option.some.inj realizedRaw
              refine ⟨point, ?_, intended⟩
              change decodedPoint setup (current.execution.respond (application setup runtime leaks)
                actor ((joint actor).getD ⟨none⟩)).application.config = _
              rw [(runtime.reactive_respond_application leaks current.execution actor
                ((joint actor).getD ⟨none⟩)).1]
              exact decodedCurrent
          | none =>
              obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (runtime := runtime)
                (failureProfile setup.program) (bounds.onePacketMenu runtime leaks)
                  horizon scheduler prior current rfl
              rcases runtime.reactive_protocol_config_eq_or_step_of_clear leaks (initialLaw setup)
                  horizon scheduler current control joint realizedRaw clear with
                    same | ⟨event, ready, action, member⟩
              · exact ⟨point, by rw [same]; exact decodedCurrent, intended⟩
              obtain ⟨before', target, beforeEq, afterEq, reached⟩ :=
                decodedPoint_step residual event ready action _ member
              rw [decodedCurrent, Option.some.injEq] at beforeEq
              subst beforeEq
              refine ⟨target, afterEq, ProtocolState.intended_step_of_actors setup.program
                point _ target intended (fun player acts => ?_) reached⟩
              have rawPrior := (bounds.onePacketMenu runtime leaks).toRawTrace
                (initialLaw setup) horizon scheduler prior
              rw [decodedPoint_actor_of_history player rawPrior ready decodedCurrent] at acts
              by_cases own : player = who
              · subst player
                exact ProtocolState.intendedAvailable_of_decode_intendedFor setup.program
                  event.val _ _ _ _ _ _ _ point event.isLt who action target
                  (decodedPoint_decode ready decodedCurrent)
                  (ownPrior.current current rfl point decodedCurrent)
                  ((eventOwner?_eq_actor setup.program event).trans acts) reached
                  (ownIntended.current control rfl target afterEq)
              rcases transition_idle_cases (runtime := runtime) (initialLaw setup) horizon
                  scheduler current acting joint realizedRaw with sameExecution | ⟨command, moved⟩
              · exact (config_ne_of_step member (by rw [sameExecution])).elim
              have active : player ∉ current.execution.application.config.defaulted := by
                rw [priorClear]
                exact Finset.notMem_empty _
              obtain ⟨value, _output, recorded⟩ :=
                current.execution.application.config.step_completion event ready action _ member
              let completion := EventGraph.completion (graph setup) event
                (current.execution.application.config.actualDecision event action) value
              have fresh : completion ∉ current.execution.application.config.history := by
                intro present
                exact ready.1 ((current.execution.application.config.history_exact event).mp
                  (List.mem_map.mpr ⟨completion, present, rfl⟩))
              have present : completion ∈ control.execution.application.config.history := by
                rw [recorded]
                exact List.mem_append_right _ (List.mem_singleton_self completion)
              have chosen : completion.decision.bind
                  (decodeEventAction setup.program completion.event) =
                    decodeEventAction setup.program event action := by
                change (current.execution.application.config.actualDecision event action).bind _ = _
                rw [current.execution.application.config.actualDecision_of_active event player acts
                  active action, Option.bind_some]
                rfl
              rcases completion_cases (runtime := runtime) current.execution control.execution
                command
                  moved completion fresh present acts with accepted | expired | automatic
              · obtain ⟨message, onLedger, sender, named, content, owned, _accepted⟩ := accepted
                rw [chosen] at content
                have invariant := periodInvariant (runtime := runtime) assessment who prior
                  current rfl forcedCurrent
                have positive := unsettledContent_pos (runtime := runtime) assessment who prior
                  regularPrior
                have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace
                  (initialLaw setup) horizon scheduler (prior.extend joint legal realized)
                have facts := legalFacts setup leaks horizon scheduler control rawTrace
                have inputsEq := transition_idle_inputs (runtime := runtime) (initialLaw setup)
                  horizon scheduler current acting joint realizedRaw
                have carried : message ∈ current.execution.network.inputs := by
                  rw [← inputsEq]
                  obtain ⟨entry, entryPresent, material, _transmission, emitted, _packet⟩ :=
                    facts.provenance.ledger message onLedger
                  have recalled : message ∈ (application setup runtime leaks).outputs
                      (control.execution.logs message.sender) :=
                    List.mem_filterMap.mpr ⟨entry, entryPresent, emitted⟩
                  rw [← facts.inputs message.sender] at recalled
                  exact (List.mem_filter.mp recalled).1
                rcases invariant.settled event ready player acts own with ⟨_, nothing⟩ |
                    ⟨recorded, recordedPresent, recordedSender, recordedNamed, sent, keep, fixed,
                      eq⟩
                · exact (nothing message carried sender named).elim
                · have sameMessage := invariant.unique recorded recordedPresent message carried
                    (recordedSender ▸ own) (recordedSender.trans sender.symm) event recordedNamed
                    named
                  subst sameMessage
                  rw [eq, ← callContent_keep keep _ fun named' handle call =>
                    fixed named' handle call (owned named' handle call), ← content,
                    decodedCurrent] at positive
                  refine intendedAvailable_of_pos assessment
                    ((decodedPoint_actor_of_history player rawPrior ready decodedCurrent).trans
                      acts) ?_
                  intro zero
                  rw [zero, ENNReal.toReal_zero] at positive
                  exact lt_irrefl 0 positive
              · obtain ⟨tables, failing⟩ := expired
                rw [chosen] at failing
                exfalso
                have owned : eventOwner? setup.program ⟨event.val, event.isLt⟩ = some player :=
                  (eventOwner?_eq_actor setup.program event).trans acts
                cases view : nodeView (graph setup) event with
                | bind owner payload outputEq codeEq =>
                    have sameOwner : owner = player :=
                      Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans acts)
                    subst owner
                    have vacant : current.execution.application.accepted (.inr event) = none := by
                      cases accepted : current.execution.application.accepted (.inr event) with
                      | none => rfl
                      | some candidate =>
                          have valid := (legalFacts setup leaks horizon scheduler current
                            rawPrior).binding.toAssociationInvariant
                          exact (ready.1 (valid.accepted_complete event candidate accepted)).elim
                    have completedNow : event ∈
                      control.execution.application.config.cut.completed :=
                      (control.execution.application.config.history_exact event).mp
                        (List.mem_map.mpr ⟨completion, present, rfl⟩)
                    apply record.bindingAccepted (prior.extend joint legal realized)
                      event player payload outputEq own completedNow
                    rw [tables]
                    exact vacant
                | resolve owner payload binding checks outputEq codeEq =>
                    exact record.not_revealFailed (prior.extend joint legal realized) own afterEq
                      (ProtocolState.revealFailed_of_decode_failing setup.program event.val _ _ _
                        _ _ _ _ point event.isLt player payload _ target
                        (decodedPoint_decode ready decodedCurrent) owned outputEq failing reached)
                | sample _ _ outputEq codeEq =>
                    rw [nodeView_sample_actor outputEq codeEq] at acts
                    cases acts
              · obtain ⟨_failing, native, drained, _fresh, _origin, _silent, _default, excluded⟩ :=
                  automatic
                have later : player ∈ control.execution.application.config.defaulted := by
                  rw [← drained, native.drain_defaulted]
                  exact excluded
                rw [clear] at later
                exact (Finset.notMem_empty player later).elim

/-- **Regular histories of a forced site are forced.** For a well-formed setup,
every regular history of a forced decision site of `who`, along which `who`'s own
completions decode to intended actions, ends in a forced state of `who`. The
forced history of the site gives a public record, which `who`'s view carries
over to every history of the site. -/
theorem forcedState_of_regular (wellFormed : setup.WellFormed)
    (assessment : setup.intendedModel.BehavioralAssessment) {who : Player}
    {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} (decision : site.1 = some (past, view))
    (forced : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw
      setup) horizon
      scheduler who site.1)
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1)
    (regular : RegularTrace setup runtime leaks bounds horizon scheduler assessment who
      history.1.trace)
    (ownIntended : OwnCompletionsIntended (runtime := runtime) (bounds := bounds) (horizon :=
      horizon)
      (scheduler := scheduler) who history.1.trace) :
    ForcedState setup runtime leaks who history.1.state := by
  obtain ⟨witness, witnessInfo, witnessForced⟩ := forced
  obtain ⟨control, stateEq, viewEq⟩ := state_of_decision (runtime := runtime) history decision
  obtain ⟨witnessControl, witnessStateEq, witnessViewEq⟩ :=
    state_of_decision (runtime := runtime) (site := site) ⟨witness, witnessInfo⟩ decision
  obtain ⟨⟨state, trace⟩, info⟩ := history
  change state = some control at stateEq
  subst stateEq
  obtain ⟨witnessState, witnessTrace⟩ := witness
  change witnessState = some witnessControl at witnessStateEq
  subst witnessStateEq
  have witnessRecord := publicRecord_of_forced (runtime := runtime) who witnessControl witnessForced
  have sameView : control.execution.observe (application setup runtime leaks) who =
      witnessControl.execution.observe (application setup runtime leaks) who :=
    viewEq.trans witnessViewEq.symm
  have samePublic : control.execution.application.publicView =
      witnessControl.execution.application.publicView :=
    congrArg (fun observed : (application setup runtime leaks).PlayerView =>
      observed.application.publicView) sameView
  have sameDefaulted : control.execution.application.config.defaulted =
      witnessControl.execution.application.config.defaulted :=
    congrArg (fun publicView : PublicView (graph setup) => publicView.observation.defaulted)
      samePublic
  have record : PublicRecord setup runtime who control := by
    intro player different excluded
    exact witnessRecord player different (sameDefaulted ▸ excluded)
  obtain ⟨point, decoded, intended⟩ := intended_of_regular (runtime := runtime) wellFormed
    assessment who trace
    control rfl record regular ownIntended
  exact (forcedState_iff_decodedPoint (runtime := runtime) control).mpr
    ⟨point, decoded, forcedPoint_of_intended who intended⟩

section Assembly

variable {who : Player}
  {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
  {sourceSite : setup.intendedModel.InformationSite who}
  {past : List (application setup runtime leaks).PlayerEntry}
  {view : (application setup runtime leaks).PlayerView}

open Classical in
/-- **Forced-belief inputs at an own-turn site.** For a well-formed setup, at a
forced decision site of `who` whose view shows `who`'s own ready event and
whose projected view is an intended site, under a fully mixed intended
assessment at stage `n`, the replay projection supplies the source weights of
`Vegas.ForcedBeliefInputs` as soon as `who`'s own completions along every
regular history of the site decode to intended actions. The common fibers and
the honest counterparts remain inputs. -/
def ForcedBeliefInputs.ofRegularHistories
    {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
    {profiles : ℕ → ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player}
    {steps : OperationalSteps setup runtime leaks bounds horizon scheduler sequence profiles who}
    [Fintype ((onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1)]
    [DecidableEq (setup.intendedModel.InformationHistory who sourceSite.1)]
    {scale floors : ℕ → ℝ} {depth : ℕ} {slack : ℝ} {n : ℕ} (wellFormed : setup.WellFormed)
    (forced : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw
      setup) horizon
      scheduler who site.1)
    (decision : site.1 = some (past, view)) {event : (graph setup).EventId}
    (turn : view.application.publicView.ownTurn? who = some event)
    (projected : sourceSite.1 = projectView setup runtime leaks who site.1)
    (mixed : (sequence n).IsFullyMixed)
    (ownIntended : ∀ history : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).InformationHistory who site.1,
      RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who history.1.trace →
      OwnCompletionsIntended (runtime := runtime) (bounds := bounds) (horizon := horizon)
        (scheduler := scheduler)
        who history.1.trace)
    (fiberMass : ℝ)
    (fiber : ∀ point, ∑ history with RegularTrace setup runtime leaks bounds horizon scheduler
        (sequence n) who history.1.trace ∧
        replayProjection setup runtime leaks bounds horizon scheduler sourceSite site decision
          projected
          history = point,
      operationalWeight setup runtime leaks who (steps.mass n)
        (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace) =
          fiberMass)
    (counterpart : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory
        who site.1 →
      (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationHistory who
        site.1)
    (commonWeight : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who site.1 → ℝ)
    (counterpart_regular : ∀ history, ¬ RegularTrace setup runtime leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who
        (counterpart history).1.trace)
    (irregular_le : ∀ history, ¬ RegularTrace setup runtime leaks bounds horizon scheduler
      (sequence n)
        who history.1.trace →
      ((onePacketInformation setup runtime leaks bounds horizon scheduler).historyReachWeight
          (profiles n) history.1).toReal ≤ scale n ^ 3 * commonWeight history)
    (counterpart_ge : ∀ history, ¬ RegularTrace setup runtime leaks bounds horizon scheduler
        (sequence n) who history.1.trace →
      scale n ^ 2 * floors n ^ depth * commonWeight history ≤
        slack * ((onePacketInformation setup runtime leaks bounds horizon
          scheduler).historyReachWeight
          (profiles n) (counterpart history).1).toReal) :
    ForcedBeliefInputs setup runtime leaks bounds horizon scheduler sequence profiles steps site
      sourceSite (replayProjection setup runtime leaks bounds horizon scheduler sourceSite site
        decision
        projected) scale floors depth slack n :=
  ForcedBeliefInputs.ofForcedHistories (runtime := runtime) forced decision turn projected mixed
    (fun history regular => forcedState_of_regular (runtime := runtime) wellFormed (sequence n)
      decision forced history
      regular (ownIntended history regular))
    ownIntended fiberMass fiber counterpart commonWeight counterpart_regular irregular_le
      counterpart_ge

end Assembly

end Vegas
