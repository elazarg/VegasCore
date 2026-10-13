/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCompletionCases
import Vegas.Game.OnePacketOwnSubmissions

/-! # Regular histories of a forced site are forced

**Intended points are forced.** At a point of the intended game nobody owes a
failure or is excluded, so it is forced for every player
(`Vegas.forcedPoint_of_intended`).

**Withheld reveals fail.** Stepping a decoded point at a reveal with a
failing decision makes the revealing player's reveal fail
(`Vegas.SourceProgram.ProtocolState.revealFailed_of_decode_failing`).

**The public record.** At a native state, a *public record* for `who` says that
every completed binding event of another player has an accepted handle, and
that no other player's reveal has failed at the decoded point
(`Vegas.PublicRecord`). Both are read from `who`'s view: the table of accepted
handles is part of the public contract view, and failed reveals are public. A
public record reaches back along every transition (`Vegas.publicRecord_of_transition`)
and holds at every history ending in a forced state of `who`
(`Vegas.publicRecord_of_forced`).

**Forced regular histories.** For a well-formed setup, along a regular history
ending at a public record for `who`, along which `who`'s own completions are
intended, the decoded point stays a point of the intended game: chance and own
completions are intended steps; a completion of another player's event cannot
be an expiry, which would leave a binding without an accepted handle or fail a
reveal, so it includes the player's single packet for the event, whose content
has positive intended mass (`Vegas.intended_of_regular`). So every regular
history of a forced site, along which `who`'s own completions are intended,
ends in a forced state of `who` (`Vegas.forcedState_of_regular`).
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- A point of the intended game excludes nobody. -/
theorem Intended.not_excluded (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    Intended program state → ¬ Excluded who program state
  | _, _, .ret _, _, intended => fun ⟨_, _, cell, failure⟩ => by
      obtain ⟨value, success⟩ := intended.bound cell
      rw [success] at failure
      cases failure
  | _, _, .sample _ _ _ next, state, intended => by
      cases state with
      | inl _ =>
          rintro ⟨_, _, cell, failure⟩
          obtain ⟨value, success⟩ := intended.1.bound cell
          rw [success] at failure
          cases failure
      | inr rest => exact Intended.not_excluded who next rest intended
  | _, _, .commit _ _ _ _ next, state, intended => by
      cases state with
      | inl _ =>
          rintro ⟨_, _, cell, failure⟩
          obtain ⟨value, success⟩ := intended.1.bound cell
          rw [success] at failure
          cases failure
      | inr rest => exact Intended.not_excluded who next rest intended
  | _, _, .reveal _ _ _ _ _ _ next, state, intended => by
      cases state with
      | inl _ =>
          rintro ⟨_, _, cell, failure⟩
          obtain ⟨value, success⟩ := intended.1.bound cell
          rw [success] at failure
          cases failure
      | inr rest =>
          rintro (⟨_, failure⟩ | excluded)
          · obtain ⟨value, success⟩ := intended.1
            rw [success] at failure
            cases failure
          · exact Intended.not_excluded who next rest intended.2 excluded

/-- **Withheld reveals fail.** At a decoded state at a reveal of `who`, a step
with a failing decision makes `who`'s reveal fail. -/
theorem revealFailed_of_decode_failing {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (state : ProtocolState program) (bound : count < eventCount program) (who : Player)
      (payload : L.Ty) (choice : Option (OwnAction Player L)) (target : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history =
          some state →
      eventOwner? program ⟨count, bound⟩ = some who →
      outputLayout program ⟨count, bound⟩ = .publication payload → Failing choice →
      target ∈ (step program state (fun _ => choice)).support →
      RevealFailed who program target := by
  induction program with
  | ret _ =>
      intro count _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro count refs registry revelations outputs store history state bound who payload choice
        target decoded owned layout failing reached
      cases count with
      | zero => cases owned
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) who payload
            choice after read owned layout failing supported
  | commit name owner fresh guard next ih =>
      intro count refs registry revelations outputs store history state bound who payload choice
        target decoded owned layout failing reached
      cases count with
      | zero => cases layout
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) who payload
            choice after read owned layout failing supported
  | reveal published owner name fresh source unresolved next ih =>
      intro count refs registry revelations outputs store history state bound who payload choice
        target decoded owned layout failing reached
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same : target = Sum.inr (entry next (revealSuccessor published source
              ⟨cells, registry, revelations, history⟩ (OwnAction.disclosure choice))) :=
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
          exact Or.inr (ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) who
            payload choice after read owned layout failing supported)

end ProtocolState

end Vegas.SourceProgram

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- **Intended points are forced** for every player. -/
theorem forcedPoint_of_intended (who : Player) {point : ProtocolState setup.program}
    (intended : ProtocolState.Intended setup.program point) : ForcedPoint setup who point :=
  ⟨fun failed => ProtocolState.Intended.not_owesFailure who setup.program point intended
      (Or.inl (ProtocolState.RevealFailed.indebted setup.program point failed)),
    fun other _ => ⟨ProtocolState.Intended.not_excluded other setup.program point intended,
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

variable (setup) in
/-- **The public record** of an observer `who` at a native control state: every
completed binding event of another player has an accepted handle, and no other
player's reveal has failed at the decoded point. -/
def PublicRecord {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (who : Player) (control : (application setup leaks).Control) : Prop :=
  (∀ event owner payload, (graph setup).outputLayout event = .binding owner payload →
    owner ≠ who → event ∈ control.execution.application.config.cut.completed →
      control.execution.application.accepted (.inr event) ≠ none) ∧
  ∀ other, other ≠ who → ∀ point,
    decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.RevealFailed other setup.program point

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- **The public record reaches back** along every transition. -/
theorem publicRecord_of_transition {who : Player} {current next : (application setup leaks).Control}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some current))
    (joint : Player → Option (application setup leaks).Action)
    (realized : some next ∈ ((application setup leaks).transition (initialLaw setup) horizon
      scheduler (some current) joint).support)
    (record : PublicRecord setup who next) : PublicRecord setup who current := by
  refine ⟨fun event owner payload layout other completed => ?_,
    fun player other point decoded failed => ?_⟩
  · have later := record.1 event owner payload layout other
      (completed_transition leaks joint realized completed)
    rcases acceptedKept_transition leaks (initialLaw setup) horizon scheduler current next joint
        realized event with same | ⟨ready, _, _⟩
    · rw [← same]
      exact later
    · exact (ready.1 completed).elim
  · obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
      (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler prior current rfl
    rcases transition_configStep (initialLaw setup) horizon scheduler current next joint realized
        with same | ⟨event, ready, action, member⟩
    · exact record.2 player other point (by rw [same]; exact decoded) failed
    · obtain ⟨before, target, beforeEq, afterEq, reached⟩ :=
        decodedPoint_step residual event ready action _ member
      rw [decoded, Option.some.injEq] at beforeEq
      subst beforeEq
      exact record.2 player other target afterEq
        (ProtocolState.revealFailed_step player setup.program point _ target failed reached)

/-- **Forced states have a public record.** Along a history ending in a forced
state of `who`, every completed binding event of another player was completed
by an accepted commitment, since an expiry would leave that player owing a
failure. -/
theorem publicRecord_of_forced (who : Player) : ∀ {state}
    (_ : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    (control : (application setup leaks).Control), state = some control →
    ForcedState setup leaks who (some control) → PublicRecord setup who control
  | _, .start, _, current, _ => by cases current
  | _, .extend (source := before) prior joint _ realized, control, current, forced => by
      have recursive := fun next same forcedNext =>
        publicRecord_of_forced who prior next same forcedNext
      subst current
      change some control ∈ ((application setup leaks).transition (initialLaw setup) horizon
        scheduler before joint).support at realized
      obtain ⟨found, foundDecoded, foundForced⟩ := (forcedState_iff_decodedPoint control).mp forced
      refine ⟨fun event owner payload layout other completed => ?_,
        fun player other point decoded failed => ?_⟩
      · cases before with
        | none =>
            change some control ∈ ((initialLaw setup).map fun state => some
              (⟨horizon, none, ReactiveApplication.Execution.initial (application setup leaks)
                state⟩ : (application setup leaks).Control)).support at realized
            obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realized
            cases Option.some.inj same
            obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
            have ordered := (SourceResidual.initial setup (failureProfile setup.program)
              initial).checkpoint.ordered
            exact absurd ((ordered.2 event).mp completed) (Nat.not_lt_zero _)
        | some current =>
            have forcedCurrent := forcedState_of_transition prior joint realized forced
            have earlier := recursive current rfl forcedCurrent
            by_cases before_ : event ∈ current.execution.application.config.cut.completed
            · have kept := earlier.1 event owner payload layout other before_
              rcases acceptedKept_transition leaks (initialLaw setup) horizon scheduler current
                  control joint realized event with same | ⟨ready, _, _⟩
              · rw [same]
                exact kept
              · exact (ready.1 before_).elim
            · rcases transition_configStep (initialLaw setup) horizon scheduler current control
                  joint realized with same | ⟨completedEvent, ready, action, member⟩
              · rw [same] at completed
                exact (before_ completed).elim
              · have which : event = completedEvent := by
                  rw [current.execution.application.config.step_cut completedEvent ready action _
                    member, EventOrder.Cut.mem_complete] at completed
                  exact completed.resolve_right before_
                subst which
                have idle : current.actor = none := by
                  cases acting : current.actor with
                  | none => rfl
                  | some actor =>
                      exfalso
                      rw [transition_respond current acting joint, PMF.mem_support_pure_iff]
                        at realized
                      cases Option.some.inj realized
                      exact config_ne_of_step member
                        ((runtime setup).reactive_respond_application leaks current.execution
                          actor _).1
                rcases transition_idle_cases (initialLaw setup) horizon scheduler current idle
                    joint realized with sameExecution | ⟨command, moved⟩
                · exact (config_ne_of_step member (by rw [sameExecution])).elim
                · rcases completion_cases current.execution control.execution command moved ready
                      action member (actor_of_binding layout) with
                    ⟨_, _, _, _, _, _, table⟩ | ⟨_, failing⟩
                  · exact table owner payload layout
                  · exfalso
                    obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual
                      (failureProfile setup.program) (bounds.onePacketMenu (runtime setup) leaks)
                      horizon scheduler prior current rfl
                    obtain ⟨point, target, decodedCurrent, decodedNext, reached⟩ :=
                      decodedPoint_step residual event ready action _ member
                    have owned : eventOwner? setup.program ⟨event.val, event.isLt⟩ =
                        some owner := by
                      rw [eventOwner?_eq_actor]
                      exact actor_of_binding layout
                    have owes := ProtocolState.owesFailure_of_decode_failing setup.program
                      setup.namesNodup event.val _ _ _ _ _ _ point event.isLt owner _ target
                      (decodedPoint_decode ready decodedCurrent) owned failing reached
                    rw [decodedNext, Option.some.injEq] at foundDecoded
                    subst foundDecoded
                    exact (foundForced.2 owner other).2 owes
      · rw [foundDecoded, Option.some.injEq] at decoded
        subst decoded
        exact (foundForced.2 player other).1
          (ProtocolState.RevealFailed.excluded setup.program _ failed)

/-- **Regular histories stay intended.** For a well-formed setup, along a
regular history ending at a public record for `who`, along which `who`'s own
completions decode to intended actions, the decoded point is a point of the
intended game. -/
theorem intended_of_regular (wellFormed : setup.WellFormed)
    (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) : ∀ {state}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace state)
    (control : (application setup leaks).Control), state = some control →
    PublicRecord setup who control →
    RegularTrace setup leaks bounds horizon scheduler assessment who trace →
    OwnCompletionsIntended (bounds := bounds) (horizon := horizon) (scheduler := scheduler)
      who trace →
    ∃ point, decodedPoint setup control.execution.application.config = some point ∧
      ProtocolState.Intended setup.program point
  | _, .start, _, current, _, _, _ => by cases current
  | _, .extend (source := before) prior joint legal realized, control, current, record, regular,
      ownIntended => by
      obtain ⟨regularPrior, _⟩ := regular
      obtain ⟨ownPrior, ownStep⟩ := ownIntended
      have recursive := fun next same recordNext =>
        intended_of_regular wellFormed assessment who prior next same recordNext regularPrior
          ownPrior
      subst current
      have realizedRaw : some control ∈ ((application setup leaks).transition (initialLaw setup)
          horizon scheduler before joint).support := realized
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state => some
            (⟨horizon, none, ReactiveApplication.Execution.initial (application setup leaks)
              state⟩ : (application setup leaks).Control)).support at realizedRaw
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realizedRaw
          cases Option.some.inj same
          obtain ⟨initial, initialMem, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨_, decodedPoint_initial initial, ProtocolState.intended_entry setup.program _
            (setup.initialConfig_intended wellFormed initialMem)
            (wellFormed.guardsSatisfiable initial initialMem)⟩
      | some current =>
          have recordCurrent := publicRecord_of_transition prior joint realizedRaw record
          obtain ⟨point, decodedCurrent, intended⟩ := recursive current rfl recordCurrent
          have forcedCurrent : ForcedState setup leaks who (some current) :=
            (forcedState_iff_decodedPoint current).mpr
              ⟨point, decodedCurrent, forcedPoint_of_intended who intended⟩
          cases acting : current.actor with
          | some actor =>
              rw [transition_respond current acting joint, PMF.mem_support_pure_iff]
                at realizedRaw
              cases Option.some.inj realizedRaw
              refine ⟨point, ?_, intended⟩
              change decodedPoint setup (current.execution.respond (application setup leaks) actor
                ((joint actor).getD ⟨none⟩)).application.config = _
              rw [((runtime setup).reactive_respond_application leaks current.execution actor
                ((joint actor).getD ⟨none⟩)).1]
              exact decodedCurrent
          | none =>
              obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
                (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler prior current rfl
              rcases transition_configStep (initialLaw setup) horizon scheduler current control
                  joint realizedRaw with same | ⟨event, ready, action, member⟩
              · exact ⟨point, by rw [same]; exact decodedCurrent, intended⟩
              obtain ⟨before', target, beforeEq, afterEq, reached⟩ :=
                decodedPoint_step residual event ready action _ member
              rw [decodedCurrent, Option.some.injEq] at beforeEq
              subst beforeEq
              refine ⟨target, afterEq, ProtocolState.intended_step_of_actors setup.program
                point _ target intended (fun player acts => ?_) reached⟩
              rw [decodedPoint_actor player ready decodedCurrent] at acts
              by_cases own : player = who
              · subst own
                exact ownStep current control rfl rfl acting event ready action member acts
                  point decodedCurrent
              rcases transition_idle_cases (initialLaw setup) horizon scheduler current acting
                  joint realizedRaw with sameExecution | ⟨command, moved⟩
              · exact (config_ne_of_step member (by rw [sameExecution])).elim
              rcases completion_cases current.execution control.execution command moved ready
                  action member acts with
                ⟨message, onLedger, sender, named, content, owned, _⟩ | ⟨tables, failing⟩
              · have invariant := periodInvariant assessment who prior current rfl forcedCurrent
                have positive := unsettledContent_pos assessment who prior regularPrior
                have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace
                  (initialLaw setup) horizon scheduler (prior.extend joint legal realized)
                have facts := settledFacts_history (initialLaw setup) horizon scheduler rawTrace
                have inputsEq := transition_idle_inputs (initialLaw setup) horizon scheduler
                  current acting joint realizedRaw
                have present : message ∈ current.execution.network.inputs := by
                  rw [← inputsEq]
                  exact facts.carried.ledger message onLedger
                rcases invariant.settled event ready player acts own with ⟨_, nothing⟩ |
                    ⟨recorded, recordedPresent, recordedSender, recordedNamed, sent, keep, fixed,
                      eq⟩
                · exact (nothing message present sender named).elim
                · have sameMessage := invariant.unique recorded recordedPresent message present
                    (recordedSender ▸ own) (recordedSender.trans sender.symm) event
                    recordedNamed named
                  subst sameMessage
                  rw [eq, ← callContent_keep keep _ fun named' handle call =>
                    fixed named' handle call (owned named' handle call), ← content,
                    decodedCurrent] at positive
                  refine intendedAvailable_of_pos assessment
                    ((decodedPoint_actor player ready decodedCurrent).trans acts) ?_
                  intro zero
                  rw [zero, ENNReal.toReal_zero] at positive
                  exact lt_irrefl 0 positive
              · exfalso
                have owned : eventOwner? setup.program ⟨event.val, event.isLt⟩ = some player := by
                  rw [eventOwner?_eq_actor]
                  exact acts
                cases view : nodeView (graph setup) event with
                | bind owner payload outputEq codeEq =>
                    have sameOwner : owner = player :=
                      Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans acts)
                    subst sameOwner
                    have vacant : current.execution.application.accepted (.inr event) = none := by
                      by_contra present
                      exact ready.1 (accepted_completed leaks prior current rfl event present)
                    have completedNow :
                        event ∈ control.execution.application.config.cut.completed := by
                      rw [current.execution.application.config.step_cut event ready action _
                        member]
                      exact (EventOrder.Cut.mem_complete _ _ ready _).mpr (Or.inl rfl)
                    apply record.1 event owner payload outputEq own completedNow
                    rw [tables]
                    exact vacant
                | resolve owner payload binding checks outputEq codeEq =>
                    exact record.2 player own target afterEq
                      (ProtocolState.revealFailed_of_decode_failing setup.program event.val _ _ _
                        _ _ _ point event.isLt player payload _ target
                        (decodedPoint_decode ready decodedCurrent) owned outputEq failing reached)
                | sample _ _ outputEq codeEq =>
                    rw [nodeView_sample_actor outputEq codeEq] at acts
                    cases acts

/-- **Regular histories of a forced site are forced.** For a well-formed setup,
every regular history of a forced decision site of `who`, along which `who`'s own
completions decode to intended actions, ends in a forced state of `who`. The
forced history of the site gives a public record, which `who`'s view carries
over to every history of the site. -/
theorem forcedState_of_regular (wellFormed : setup.WellFormed)
    (assessment : setup.intendedModel.BehavioralAssessment) {who : Player}
    {site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (decision : site.1 = some (past, view))
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who site.1)
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1)
    (regular : RegularTrace setup leaks bounds horizon scheduler assessment who history.1.trace)
    (ownIntended : OwnCompletionsIntended (bounds := bounds) (horizon := horizon)
      (scheduler := scheduler) who history.1.trace) :
    ForcedState setup leaks who history.1.state := by
  obtain ⟨witness, witnessInfo, witnessForced⟩ := forced
  obtain ⟨control, stateEq, viewEq⟩ := state_of_decision history decision
  obtain ⟨witnessControl, witnessStateEq, witnessViewEq⟩ :=
    state_of_decision (site := site) ⟨witness, witnessInfo⟩ decision
  obtain ⟨⟨state, trace⟩, info⟩ := history
  change state = some control at stateEq
  subst stateEq
  obtain ⟨witnessState, witnessTrace⟩ := witness
  change witnessState = some witnessControl at witnessStateEq
  subst witnessStateEq
  have witnessRecord := publicRecord_of_forced who witnessTrace witnessControl rfl witnessForced
  have sameView : control.execution.observe (application setup leaks) who =
      witnessControl.execution.observe (application setup leaks) who :=
    viewEq.trans witnessViewEq.symm
  have samePublic : control.execution.application.publicView =
      witnessControl.execution.application.publicView :=
    congrArg (fun observed : (application setup leaks).PlayerView =>
      observed.application.publicView) sameView
  have sameAccepted : control.execution.application.accepted =
      witnessControl.execution.application.accepted :=
    congrArg PublicView.accepted samePublic
  have sameOrder : control.execution.application.config.history.map EventGraph.Completion.event =
      witnessControl.execution.application.config.history.map EventGraph.Completion.event :=
    congrArg (fun publicView : PublicView (graph setup) =>
      publicView.observation.completionOrder) samePublic
  have sameSource := (sourceViewOf_eq_decodedPoint who trace).symm.trans
    ((congrArg (sourceViewOf setup leaks who) sameView).trans
      (sourceViewOf_eq_decodedPoint who witnessTrace))
  have record : PublicRecord setup who control := by
    refine ⟨fun event owner payload layout other completed => ?_,
      fun player other point decoded failed => ?_⟩
    · rw [sameAccepted]
      refine witnessRecord.1 event owner payload layout other ?_
      apply (witnessControl.execution.application.config.history_exact event).mp
      rw [← sameOrder]
      exact (control.execution.application.config.history_exact event).mpr completed
    · obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
        (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler witnessTrace
        witnessControl rfl
      have witnessDecoded := decodedPoint_eq residual
      rw [decoded, witnessDecoded] at sameSource
      have observed := Option.some.inj sameSource
      exact witnessRecord.2 player other _ witnessDecoded
        ((ProtocolState.revealFailed_iff_of_observe_eq player who setup.program _ _
          observed).mp failed)
  obtain ⟨point, decoded, intended⟩ := intended_of_regular wellFormed assessment who trace
    control rfl record regular ownIntended
  exact (forcedState_iff_decodedPoint control).mpr
    ⟨point, decoded, forcedPoint_of_intended who intended⟩

end Vegas
