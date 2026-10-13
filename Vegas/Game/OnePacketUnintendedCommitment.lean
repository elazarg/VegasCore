/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketProjectedDecision
import Vegas.Game.OnePacketSureFailure
import Vegas.Game.OnePacketDisclosureResolves
import Vegas.Source.IntendedForPlayer

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
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (state : ProtocolState program) (bound : count < eventCount program) (actor : Player)
      (action : EventGraph.EventField.Action (outputLayout program ⟨count, bound⟩))
      (target : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history =
          some state →
      IntendedFor actor program state →
      eventOwner? program ⟨count, bound⟩ = some actor →
      target ∈ (step program state
        (fun _ => decodeEventAction program ⟨count, bound⟩ action)).support →
      (∀ act, decodeEventAction program ⟨count, bound⟩ action = some act →
        act ∉ ProtocolView.intendedAvailable actor program (observe actor program state)) →
      OwesFailure actor program target := by
  induction program with
  | ret _ =>
      intro count _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached unintended
      cases count with
      | zero => cases owned
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended owned supported unintended
  | @commit commitCtx commitNames name owner payload fresh guard next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached unintended
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          change PublicationResult (L.Val payload) at action
          change ∀ act, some (OwnAction.commit owner name payload action) = some act → _
            at unintended
          change OwesFailure owner (.commit name owner fresh guard next) (Sum.inr (entry next
            (commitSuccessor name guard ⟨cells, registry, revelations, history⟩
              (OwnAction.binding owner name payload
                (some (OwnAction.commit owner name payload action))))))
          rw [OwnAction.binding_commit]
          cases action with
          | failure =>
              exact Or.inr (failedBinding_entry next _ (intended.failedBinding_commit fresh guard))
          | success value =>
              have outside := unintended _ rfl
              have rejected : guard.predicts (sourceObserve owner cells) value = false := by
                cases predicted : guard.predicts (sourceObserve owner cells) value with
                | false => rfl
                | true =>
                    exact (outside ⟨value, Or.inl
                      ((mem_predictedValues_self guard _ value).mpr predicted), rfl⟩).elim
              exact Or.inl (indebted_entry next _ (intended.indebted_commit fresh guard value
                rejected))
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended owned supported unintended
  | reveal published owner name fresh source unresolved next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached unintended
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          change Bool at action
          change ∀ act, some (OwnAction.reveal owner name action) = some act → _ at unintended
          cases action with
          | true => exact (unintended _ rfl rfl).elim
          | false =>
              refine Or.inl (Or.inl ⟨rfl, ?_⟩)
              rw [base_entry]
              exact disclosureResult_false published source _
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended owned supported unintended with indebted | failed
          · exact Or.inl (Or.inr indebted)
          · exact Or.inr (Or.inr failed)

end Vegas.SourceProgram.ProtocolState

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

variable (setup leaks) in
/-- **The unintended-commitment invariant** after `who` emits, from a recorded
entry, the commitment of its binding event `event` to `candidate`, at a
configuration `start` decoding to `point`: the history is legal, the entry is
recorded, the candidate's meaning is fixed and opens no value whose decoded
action is intended at `who`'s view of `point`; until the event completes the
configuration is `start`, and once it has completed `who` owes a failure at the
decoded point. -/
def UnintendedCommitmentInvariant (profile : BehavioralProfile setup.program) (who : Player)
    (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (candidate : Handle (graph setup)) {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (start : (graph setup).Config) (point : ProtocolState setup.program) :
    (application setup leaks).ProtocolState → Prop
  | none => False
  | some control =>
      Nonempty (((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
        horizon scheduler).Trace (some control)) ∧
      RecordsEntry setup leaks who entry (some control) ∧ entry.emitted = some message ∧
      message.sender = who ∧ message.payload.call = .commitment event candidate ∧
      control.execution.application.candidates.lookup candidate ≠ .fresh ∧
      (∀ value act, control.execution.application.candidates.lookup candidate =
          .openable ⟨payload, value⟩ →
        decodeEventAction setup.program event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm)
            (PublicationResult.success value)) = some act →
        act ∉ ProtocolView.intendedAvailable who setup.program
          (ProtocolState.observe who setup.program point)) ∧
      (event ∉ control.execution.application.config.cut.completed →
        control.execution.application.config = start) ∧
      (event ∈ control.execution.application.config.cut.completed →
        DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program)
          (some control))

private theorem cast_some' {A B : Type} (same : A = B) (value : A) :
    cast (congrArg Option same) (some value) = some (cast same value) := by
  subst same
  rfl

private theorem cast_cast_symm' {A B : Type} (same : A = B) (value : B) :
    cast same (cast same.symm value) = value := by
  subst same
  rfl

/-- **The unintended-commitment invariant persists** under every transition of
the one-packet game, from a configuration decoding to a point intended for
`who` at which `event` is ready. -/
theorem unintendedCommitmentInvariant_transition (profile : BehavioralProfile setup.program)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {candidate : Handle (graph setup)} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding who payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {start : (graph setup).Config} {point : ProtocolState setup.program}
    (decoded : decodedPoint setup start = some point)
    (intendedFor : ProtocolState.IntendedFor who setup.program point)
    (startReady : start.cut.Ready event)
    (before after : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (legal : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Legal before joint)
    (holds : UnintendedCommitmentInvariant setup leaks bounds horizon scheduler profile who entry
      message event candidate outputEq start point before)
    (reached : after ∈ (((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).step before ⟨joint, legal⟩).support) :
    UnintendedCommitmentInvariant setup leaks bounds horizon scheduler profile who entry message
      event candidate outputEq start point after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨⟨trace⟩, records, emitted, sender, call, fixed, unintended, pending, settled⟩ :=
        holds
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
          have owned : (graph setup).actor? event = some who := nodeView_bind_actor outputEq codeEq
          by_cases old : event ∈ control.execution.application.config.cut.completed
          · have stillDone : event ∈ next.execution.application.config.cut.completed := by
              rcases transition_configStep (initialLaw setup) horizon scheduler control next joint
                  reached with same | ⟨completed, ready, action, member⟩
              · rw [same]
                exact old
              · rw [control.execution.application.config.step_cut completed ready action _ member,
                  EventOrder.Cut.mem_complete]
                exact Or.inr old
            refine ⟨⟨nextTrace⟩, afterRecords, emitted, sender, call, by rw [lookupEq]; exact fixed,
              fun value act opened => unintended value act (by rw [← lookupEq]; exact opened),
              fun notDone => (notDone stillDone).elim, fun _ => ?_⟩
            exact decodedHolds_transition (owesFailure_stepClosed who) (initialLaw setup)
              horizon scheduler (some control) (some next) joint (settled old) reached
          · have atStart := pending old
            rcases transition_configStep (initialLaw setup) horizon scheduler control next joint
                reached with same | ⟨completed, ready, action, member⟩
            · refine ⟨⟨nextTrace⟩, afterRecords, emitted, sender, call,
                by rw [lookupEq]; exact fixed,
                fun value act opened => unintended value act (by rw [← lookupEq]; exact opened),
                fun _ => same.trans atStart, fun done => ?_⟩
              rw [same] at done
              exact (old done).elim
            · have readyStart : start.cut.Ready completed := atStart ▸ ready
              obtain ⟨rank, ordered, _⟩ := decodedPoint_isPrefix decoded
              have eventEq : completed = event := Fin.ext
                (((ready_iff_rank setup start rank ordered completed).mp readyStart).trans
                  ((ready_iff_rank setup start rank ordered event).mp startReady).symm)
              subst eventEq
              have done : completed ∈ next.execution.application.config.cut.completed := by
                rw [control.execution.application.config.step_cut completed ready action _ member,
                  EventOrder.Cut.mem_complete]
                exact Or.inl rfl
              refine ⟨⟨nextTrace⟩, afterRecords, emitted, sender, call,
                by rw [lookupEq]; exact fixed,
                fun value act opened => unintended value act (by rw [← lookupEq]; exact opened),
                fun notDone => (notDone done).elim, fun _ => ?_⟩
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
                rw [output, cast_some' (congrArg EventGraph.EventField.Value outputEq),
                  cast_cast_symm']
              obtain ⟨residualRank, ⟨residual⟩⟩ := protocol_sourceResidual profile
                (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler trace control rfl
              obtain ⟨successor, reachedPoint⟩ := residual.step completed ready action _ member
              have decodedBefore : decodedPoint setup control.execution.application.config =
                  some point := atStart ▸ decoded
              have samePoint : residual.lift (ProtocolState.entry residual.program
                  residual.source) = point :=
                Option.some.inj ((decodedPoint_eq residual).symm.trans decodedBefore)
              rw [samePoint] at reachedPoint
              have ownedSource : eventOwner? setup.program ⟨completed.val, completed.isLt⟩ =
                  some who := by
                rw [eventOwner?_eq_actor]
                exact owned
              have owes : ProtocolState.OwesFailure who setup.program
                  (successor.lift (ProtocolState.entry successor.program successor.source)) := by
                cases result : (cast (congrArg EventGraph.EventField.Action outputEq) action :
                    PublicationResult (L.Val payload)) with
                | failure =>
                    have actionEq : action = cast (congrArg EventGraph.EventField.Action
                        outputEq.symm) (PublicationResult.failure :
                          PublicationResult (L.Val payload)) := by
                      rw [← result, cast_cast, cast_eq]
                    have failing := decodeEventAction_failing_binding setup.program completed.val
                      completed.isLt outputEq
                    rw [← actionEq] at failing
                    exact ProtocolState.owesFailure_of_decode_failing setup.program
                      setup.namesNodup completed.val _ _ _ _ _ _ point completed.isLt who _ _
                      (decodedPoint_decode ready decodedBefore) ownedSource failing reachedPoint
                | success value =>
                    rw [result] at read
                    obtain ⟨installed, acceptedAt, _, meaning⟩ :=
                      nextFacts.binding.success_provenance _ value read
                    have vacant : control.execution.application.accepted (.inr completed) =
                        none := by
                      cases present : control.execution.application.accepted (.inr completed) with
                      | none => rfl
                      | some found =>
                          exact (old (facts.binding.toAssociationInvariant.accepted_complete
                            completed found present)).elim
                    have sameCandidate := onePacket_accepted_new bounds horizon scheduler trace
                      records emitted sender call owned vacant joint reached installed acceptedAt
                    subst sameCandidate
                    rw [lookupEq] at meaning
                    have actionEq : action = cast (congrArg EventGraph.EventField.Action
                        outputEq.symm) (PublicationResult.success value) := by
                      rw [← result, cast_cast, cast_eq]
                    exact ProtocolState.owesFailure_of_decode_not_intendedAvailable setup.program
                      completed.val _ _ _ _ _ _ point completed.isLt who action _
                      (decodedPoint_decode ready decodedBefore) intendedFor ownedSource
                      reachedPoint fun act decodedAct => by
                        rw [actionEq] at decodedAct
                        exact unintended value act meaning decodedAct
              refine ⟨residualRank + 1, ⟨successor⟩, fun state decodedState => ?_⟩
              rw [successor.decode] at decodedState
              obtain rfl := Option.some.inj decodedState
              exact owes

/-- **An unintended commitment pays the exclusion payoff on every
continuation.** Under a scheduler that completes play, let `who`, at its turn
at a binding event, at a configuration decoding to a point intended for it,
respond with a commitment of that event to a candidate whose meaning after the
response is fixed and opens no value whose decoded action is intended at
`who`'s view of the point. Every terminal history of terminal play from the
state that response reaches, under any players, pays `who` its exclusion
payoff. -/
theorem unintendedCommitment_exclusionBase (profile : BehavioralProfile setup.program)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    {event : (graph setup).EventId}
    (turn : execution.application.publicView.ownTurn? who = some event) {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {point : ProtocolState setup.program}
    (decoded : decodedPoint setup execution.application.config = some point)
    (intendedFor : ProtocolState.IntendedFor who setup.program point)
    (response : (application setup leaks).Action) (material : (application setup leaks).Submission)
    (submits : response.transmission = some material) {candidate : Handle (graph setup)}
    (call : (sentEnvelope setup leaks execution who material).payload.call =
      .commitment event candidate)
    (fixed : (execution.respond (application setup leaks) who
      response).application.candidates.lookup candidate ≠ .fresh)
    (unintended : ∀ value act, (execution.respond (application setup leaks) who
        response).application.candidates.lookup candidate = .openable ⟨payload, value⟩ →
      decodeEventAction setup.program event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (PublicationResult.success value)) = some act →
      act ∉ ProtocolView.intendedAvailable who setup.program
        (ProtocolState.observe who setup.program point))
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
      exclusionBase setup parameter utility excludedPayoff leaks final.state who =
        excludedPayoff who := by
  intro final supported
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  have afterTrace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩) :=
    current ▸ history.trace
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  have sameConfig := ((runtime setup).reactive_respond_application leaks execution who
    response).1
  have start : UnintendedCommitmentInvariant setup leaks bounds horizon scheduler profile who
      (respondEntry setup leaks execution who response)
      (sentEnvelope setup leaks execution who material) event candidate outputEq
      execution.application.config point history.state := by
    rw [current]
    refine ⟨⟨afterTrace⟩, recordsEntry_respond execution who response remaining none,
      by rw [respondEntry_of_transmission execution who response material submits], rfl, call,
      fixed, unintended, fun _ => sameConfig, fun done => ?_⟩
    rw [sameConfig] at done
    exact (ready.1 done).elim
  have reachedInvariant := model.runBehavioralTerminalFrom_support_closed certificate players _
    (fun state joint legal target holds reached =>
      unintendedCommitmentInvariant_transition bounds horizon scheduler profile codeEq decoded
        intendedFor ready state target joint legal holds reached)
    history start final supported
  have stopped := model.runBehavioralTerminalFrom_support_terminal certificate players history
    final supported
  cases state : final.state with
  | none =>
      rw [state] at reachedInvariant
      exact reachedInvariant.elim
  | some control =>
      have invariantAt := reachedInvariant
      rw [state] at reachedInvariant stopped
      obtain ⟨⟨finalTrace⟩, _, _, _, _, _, _, _, settled⟩ := reachedInvariant
      have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
          scheduler).Trace (some control) :=
        menu.toRawTrace (initialLaw setup) horizon scheduler finalTrace
      have terminal := completes control rawTrace stopped
      have done : event ∈ control.execution.application.config.cut.completed := by
        rw [terminal]
        exact Finset.mem_univ _
      have owed := settled done
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
      have paid := decoded_owesFailure_exclusionBase parameter utility excludedPayoff menu
        horizon scheduler completes certificate players who final owed final self
      rw [state] at paid
      exact paid

open Classical in
/-- **Committing to an unintended commitment pays the exclusion payoff.** Under
the hypotheses of `Vegas.unintendedCommitment_exclusionBase`, at a decision
history of `who`, committing to that response, play for the horizon from the
history, under any other policies, reaches only histories paying `who` its
exclusion payoff. -/
theorem unintendedCommitment_commit_exclusionBase (profile : BehavioralProfile setup.program)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
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
    {point : ProtocolState setup.program}
    (decoded : decodedPoint setup execution.application.config = some point)
    (intendedFor : ProtocolState.IntendedFor who setup.program point)
    (response : (application setup leaks).Action) (material : (application setup leaks).Submission)
    (submits : response.transmission = some material) {candidate : Handle (graph setup)}
    (call : (sentEnvelope setup leaks execution who material).payload.call =
      .commitment event candidate)
    (fixed : (execution.respond (application setup leaks) who
      response).application.candidates.lookup candidate ≠ .fresh)
    (unintended : ∀ value act, (execution.respond (application setup leaks) who
        response).application.candidates.lookup candidate = .openable ⟨payload, value⟩ →
      decodeEventAction setup.program event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          (PublicationResult.success value)) = some act →
      act ∉ ProtocolView.intendedAvailable who setup.program
        (ProtocolState.observe who setup.program point))
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
      exclusionBase setup parameter utility excludedPayoff leaks final.state who =
        excludedPayoff who := by
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
  exact unintendedCommitment_exclusionBase bounds horizon scheduler profile completes parameter
    utility excludedPayoff turn outputEq codeEq decoded intendedFor response material submits call
    fixed unintended certificate committed middle middleState final rest

/-- **One-packet commitments are well formed.** A transmitting response of the
one-packet menu that commits an event commits a binding event of the
responder to one of its own prepared slots: the count verdict checks the
call. -/
theorem onePacket_commitment_facts {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {response : (application setup leaks).Action}
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who past view)
    {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) {event : (graph setup).EventId}
    {candidate : Handle (graph setup)}
    (packet : material.call.packet = .commitment event candidate) :
    candidate.1 = who ∧ (∃ serial, candidate.2 = .prepared serial) ∧
      ∃ (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .binding who payload)
        (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes event) = .bind who payload),
        nodeView (graph setup) event = .bind who payload outputEq codeEq := by
  obtain ⟨_, either⟩ := (bounds.mem_onePacketActions (runtime setup) leaks who past view
    response).mp member
  rcases either with silent | ⟨material', transmits, permitted⟩
  · rw [silent] at sends
    cases sends
  have same : material' = material := Option.some.inj (transmits.symm.trans sends)
  subst same
  obtain ⟨_, correct, _⟩ := (countPermits_eq_true_iff _ _).mp permitted
  unfold CountCallCorrect at correct
  have callEq : ((runtime setup).localEnvelope leaks who past view material').payload.call =
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

variable (setup leaks) in
/-- **A commitment of an intended value.** A choice at a decision input whose
response commits an event to a prepared slot of the player, whose meaning after
the submission opens a value whose decoded source action is in the intended
menu at the projected view. -/
def IntendedCommitment {who : Player}
    (site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    (choice : (onePacketInformation setup leaks bounds horizon scheduler).Choice who site.1) :
    Prop :=
  ∃ (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (material : (application setup leaks).Submission) (event : (graph setup).EventId)
    (serial : Nat) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding who payload) (value : L.Val payload),
    site.1 = some (past, view) ∧ choice.1 = some response ∧
      response.transmission = some material ∧
      material.call.packet = .commitment event (who, .prepared serial) ∧
      material.call.candidateAfter who view.application.candidates (.prepared serial) =
        .openable ⟨payload, value⟩ ∧
      sourceOfValue setup event outputEq value ∈
        setup.intendedMenu who (projectView setup leaks who site.1)

open Classical in
/-- **An unintended commitment at a debt-free site pays the exclusion
payoff.** For a well-formed setup, under a scheduler completing play, at a
decision input of `who` showing its turn at `event`, where `who` owes no
failure at the decoded point of any history, a choice committing `event`
without committing an intended value reaches, from every history of the site's
belief, only histories paying `who` its exclusion payoff. -/
theorem unintendedCommitment_localRun_support (wellFormed : setup.WellFormed)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (assessment : (onePacketInformation setup leaks bounds horizon
      scheduler).BehavioralAssessment)
    {who : Player}
    (site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (atSite : site.1 = some (past, view))
    {event : (graph setup).EventId} (turn : view.application.publicView.ownTurn? who = some event)
    (choice : (onePacketInformation setup leaks bounds horizon scheduler).Choice who site.1)
    {response : (application setup leaks).Action} (selected : choice.1 = some response)
    {material : (application setup leaks).Submission}
    (sends : response.transmission = some material) {candidate : Handle (graph setup)}
    (packet : material.call.packet = .commitment event candidate)
    (debtFree : ∀ history : (onePacketInformation setup leaks bounds horizon
        scheduler).InformationHistory who site.1,
      ∀ point, nativeDecodedState setup leaks history.1.state = some point →
        ¬ ProtocolState.OwesFailure who setup.program point)
    (unintended : ¬ IntendedCommitment setup leaks bounds horizon scheduler site choice) :
    ∀ final ∈ (InformationModel.localRun (2 * horizon + 1) assessment site
        (PMF.pure choice)).support,
      exclusionBase setup parameter utility excludedPayoff leaks final.state who =
        excludedPayoff who := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  have member : response ∈ bounds.onePacketActions (runtime setup) leaks who past view := by
    have legal := choice.2
    obtain ⟨info, decision⟩ := site
    change info = some (past, view) at atSite
    subst atSite
    obtain ⟨action, actionMember, actionEq⟩ := legal
    rw [selected] at actionEq
    cases Option.some.inj actionEq
    exact actionMember
  obtain ⟨candidateOwner, ⟨serial, candidateSlot⟩, payload, outputEq, codeEq, _⟩ :=
    onePacket_commitment_facts bounds member sends packet
  have candidateEq : candidate = (who, .prepared serial) :=
    Prod.ext candidateOwner candidateSlot
  subst candidateEq
  intro final supported
  rw [InformationModel.localRun_eq_bind, PMF.mem_support_bind_iff] at supported
  obtain ⟨⟨history, observed⟩, _, reached⟩ := supported
  have infoEq := observed
  rw [atSite] at infoEq
  change (menu.signals (initialLaw setup) horizon scheduler).infoOf who history.trace = _
    at infoEq
  rw [menu.info] at infoEq
  cases state : history.state with
  | none =>
      rw [state] at infoEq
      cases infoEq
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      rw [state] at infoEq
      by_cases active : actor = some who
      swap
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at infoEq
        cases infoEq
      subst active
      simp only [ReactiveApplication.observe, ↓reduceIte] at infoEq
      obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj infoEq)
      subst pastEq
      subst viewEq
      have localTurn : execution.application.publicView.ownTurn? who = some event := turn
      have ready : execution.application.config.cut.Ready event :=
        (execution.application.publicView_eventReady event).mp
          (PublicView.ownTurn?_spec _ who event localTurn).1
      have historyTrace := history.trace
      rw [state] at historyTrace
      obtain ⟨rank, ⟨residual⟩, holds⟩ := decodedState_intendedFor_or_owes wellFormed who
        (failureProfile setup.program) menu horizon scheduler historyTrace _ rfl
      have decoded := decodedPoint_eq residual
      have intendedFor : ProtocolState.IntendedFor who setup.program
          (residual.lift (ProtocolState.entry residual.program residual.source)) := by
        rcases holds _ residual.decode with intended | owes
        · exact intended
        · exact (debtFree ⟨history, observed⟩ _ (by rw [state]; exact decoded) owes).elim
      have afterLookup : ∀ slot, (execution.respond (application setup leaks) who
          response).application.candidates.lookup (who, slot) =
          material.call.candidateAfter who
            (execution.observe (application setup leaks) who).application.candidates slot := by
        intro slot
        rcases response with ⟨transmission⟩
        change transmission = some material at sends
        subst sends
        exact material.call.candidateAfter_eq who execution.application slot
      have fixed : (execution.respond (application setup leaks) who
          response).application.candidates.lookup (who, .prepared serial) ≠ .fresh := by
        rw [afterLookup]
        unfold Submission.candidateAfter
        rw [packet]
        simp only [and_self, ↓reduceIte]
        split
        · split <;> simp
        · assumption
      have projected : projectView setup leaks who
          (some (execution.recall who, execution.observe (application setup leaks) who)) =
          some (ProtocolState.observe who setup.program
            (residual.lift (ProtocolState.entry residual.program residual.source))) :=
        projectView_observe setup leaks who execution rank residual.checkpoint.ordered _
          residual.decode _
      have acting : ProtocolView.actor who setup.program (ProtocolState.observe who setup.program
          (residual.lift (ProtocolState.entry residual.program residual.source))) = some who :=
        (decodedPoint_actor who ready decoded).trans (PublicView.ownTurn?_spec _ who event
          localTurn).2
      exact unintendedCommitment_commit_exclusionBase bounds horizon scheduler
        (failureProfile setup.program) completes parameter utility excludedPayoff
        assessment.strategy history state localTurn outputEq codeEq decoded intendedFor response
        material sends packet fixed
        (fun value act opened decodedAct actMember => unintended
          ⟨_, _, response, material, event, serial, payload, outputEq, value, atSite, selected,
            sends, packet, (afterLookup _).symm.trans opened, by
              rw [atSite, projected]
              change ProtocolView.intendedMenu who setup.program _ (sourceOfValue setup event
                outputEq value)
              unfold sourceOfValue
              rw [decodedAct]
              exact ⟨acting, actMember⟩⟩)
        site.1 observed choice selected final reached

end Vegas
