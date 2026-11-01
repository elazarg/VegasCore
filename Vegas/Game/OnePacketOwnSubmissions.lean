/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketActorRecord
import Vegas.Game.SourceServiceFacts
import Vegas.Game.SourceServiceCompletion
import Vegas.Pending.ReactiveSignedCommitments
import Vegas.Source.FailedBindingDeviation

/-! # Own submissions on one-packet histories are made at the owner's turns

**Intended points owe nothing.** At a point of the intended game no player owes
a failure (`Vegas.SourceProgram.ProtocolState.Intended.not_owesFailure`): every
written commitment cell holds a value, every obligation's guard accepts its
bound value, and every written reveal cell holds a value.

**The own-turn record.** A one-packet response that transmits carries the
readiness token of its event, which is issued only once all the event's
predecessors have completed, and names an event of its sender. In the
sequential order the predecessors of an event are all earlier events, so the
event is then ready, and it is the sender's own turn, or it has completed. In
the latter case, by the actor record, either the sender's accepted packet for
it is an earlier own packet naming the event, which the count verdict forbids,
or the sender owes a failure. So at every history of the one-packet game, every
own submission was made at the owner's turn at its event, or the owner owes a
failure at the decoded point (`Vegas.ownTurnRecord_history`). At a history
decoding to a point of the intended game, every own submission was therefore
made at the owner's turn (`Vegas.onePacket_ownSubmissionsAtTurn`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup runtime leaks) in
/-- **The own-turn record.** The configuration decodes at a prefix, and every
own submission of a player was made at its turn at its event, or that player
owes a failure at the decoded point. -/
def OwnTurnRecord (profile : BehavioralProfile setup.program)
    (execution : (application setup runtime leaks).Execution) : Prop :=
  ∃ rank, Nonempty (SourceResidual setup profile rank execution.application.config) ∧
    ∀ who, ∀ entry ∈ execution.recall who, ∀ event,
      runtime.submittedEvent? leaks entry.action = some event →
        entry.beforeView.application.publicView.ownTurn? who = some event ∨
        DecodedHolds (ProtocolState.OwesFailure who setup.program) rank
          execution.application.config

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- **A one-packet submission is at its owner's turn, or the owner owes.** At a
history of the one-packet game, every transmitting one-packet response of
`who` names an event at `who`'s turn, or `who` owes a failure at the decoded
point. -/
theorem onePacket_submission_atTurn {horizon : Nat}
    {scheduler : (application setup runtime leaks).Scheduler} (profile : BehavioralProfile
      setup.program)
    {rank remaining : Nat} {who : Player} {execution : (application setup runtime leaks).Execution}
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (residual : SourceResidual setup profile rank execution.application.config)
    (action : (application setup runtime leaks).Action)
    (member : action ∈ bounds.onePacketActions runtime leaks who (execution.recall who)
      (execution.observe (application setup runtime leaks) who))
    (event : (graph setup).EventId)
    (submitted : runtime.submittedEvent? leaks action = some event) :
    execution.application.publicView.ownTurn? who = some event ∨
      DecodedHolds (ProtocolState.OwesFailure who setup.program) rank
        execution.application.config := by
  let app := application setup runtime leaks
  rcases ((bounds.mem_onePacketActions runtime leaks who _ _ action).mp member).2 with
    silent | ⟨material, transmits, permitted⟩
  · unfold EventGraphRuntime.submittedEvent? at submitted
    rw [silent] at submitted
    cases submitted
  have materialNamed : material.call.packet.event? (graph setup) = some event := by
    unfold EventGraphRuntime.submittedEvent? at submitted
    rw [transmits] at submitted
    exact submitted
  obtain ⟨inputRecall, serialRecall, _⟩ := runtime.countRecall_history leaks trace
  have facts := legalFacts setup leaks horizon scheduler ⟨remaining, some who, execution⟩ trace
  set envelope := runtime.localEnvelope leaks who (execution.recall who)
    (execution.observe app who) material with envelopeEq
  obtain ⟨tokenValid, correct, first⟩ := (countPermits_eq_true_iff _ _).mp permitted
  obtain ⟨named, namedEvent, tokenEq⟩ := (WitnessedPacket.tokenValid_iff _).mp tokenValid
  have sameEvent : named = event := by
    have call : envelope.payload.call = material.call.packet := rfl
    rw [call, materialNamed] at namedEvent
    exact (Option.some.inj namedEvent).symm
  subst sameEvent
  have sender : envelope.sender = who := rfl
  have actor := correct.actor namedEvent
  rw [sender] at actor
  have issued : ∀ predecessor ∈ (graph setup).order.predecessors named,
      predecessor ∈ execution.application.config.cut.completed := by
    have token : execution.application.publicView.tokenFor envelope.payload.call =
        some ⟨named⟩ := tokenEq
    unfold PublicView.tokenFor at token
    rw [namedEvent, Option.bind_some] at token
    obtain ⟨_, complete⟩ := (PublicView.readinessToken?_eq_some_iff _ named ⟨named⟩).mp token
    intro predecessor predecessorMember
    exact (execution.application.config.history_exact predecessor).mp
      (complete predecessor predecessorMember)
  by_cases completed : named ∈ execution.application.config.cut.completed
  · obtain ⟨recordRank, ⟨recordResidual⟩, record⟩ :=
      actorRecord_history (runtime := runtime) profile horizon scheduler trace
    have sameRank := recordResidual.checkpoint.ordered.unique residual.checkpoint.ordered
    subst sameRank
    rcases record named completed who actor with
      ⟨message, onLedger, _, messageNamed, messageSender⟩ | owed
    · exfalso
      obtain ⟨entry, recorded, material, _transmission, emitted, _packet⟩ :=
        facts.provenance.ledger message onLedger
      have recalled : message ∈ app.outputs (execution.recall who) := by
        exact List.mem_filterMap.mpr ⟨entry, messageSender ▸ recorded, emitted⟩
      have emitted : message ∈ execution.network.inputs := by
        rw [← inputRecall who] at recalled
        exact (List.mem_filter.mp recalled).1
      have lower : message.id.2 < envelope.id.2 := by
        have bound := facts.serials.inputs message emitted
        change message.id.2 < execution.network.nextSerial message.sender at bound
        rw [messageSender, serialRecall who] at bound
        exact bound
      exact first message ⟨recalled, messageSender.trans sender.symm, lower⟩
        (messageNamed.trans namedEvent.symm)
    · exact Or.inr owed
  · left
    have ready : execution.application.config.cut.Ready named := ⟨completed, issued⟩
    refine PublicView.ownTurn?_of_ownTurn _ who named
      ⟨(execution.application.publicView_eventReady named).mpr ready, actor,
        fun other otherReady _ => ?_⟩
    exact setup.eventGraph.sequentialize_ready_unique _
      ((execution.application.publicView_eventReady other).mp otherReady) ready

/-- **The own-turn record holds along one-packet histories.** At every history
of the one-packet game, under every scheduler, every own submission of a player
was made at its turn at its event, or that player owes a failure at the decoded
point. -/
theorem ownTurnRecord_history (profile : BehavioralProfile setup.program) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler) :
    ∀ {state} (_ : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
        horizon scheduler).Trace state) (control : (application setup runtime leaks).Control),
      state = some control → OwnTurnRecord setup runtime leaks profile control.execution := by
  let app := application setup runtime leaks
  let menu := bounds.onePacketMenu runtime leaks
  intro state trace
  induction trace with
  | start => intro _ initialized; cases initialized
  | @extend before after prior joint legal realized ih =>
      intro control current
      subst current
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state =>
            some ⟨horizon, none, ReactiveApplication.Execution.initial app state⟩).support
            at realized
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨0, ⟨SourceResidual.initial setup profile initial⟩,
            fun _ _ member => (List.not_mem_nil member).elim⟩
      | some previous =>
          obtain ⟨rank, ⟨residual⟩, record⟩ := ih previous rfl
          have rawPrior := menu.toRawTrace (initialLaw setup) horizon scheduler prior
          rcases previous with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              have localLegal := legal.2 who
              cases selected : joint who with
              | none =>
                  simp [selected, ReactiveApplication.ResponseMenu.protocol,
                    ReactiveApplication.actor] at localLegal
              | some action =>
                  rw [selected] at localLegal
                  have chosen : action ∈ bounds.onePacketActions runtime leaks who
                      (execution.recall who) (execution.observe app who) := localLegal.2
                  have responded : some control = some (⟨remaining, none,
                      execution.respond app who action⟩ : app.Control) := by
                    change some control ∈ (PMF.pure (some (⟨remaining, none,
                      execution.respond app who ((joint who).getD ⟨none⟩)⟩ : app.Control))).support
                      at realized
                    rw [selected, Option.getD_some, PMF.mem_support_pure_iff] at realized
                    exact realized
                  cases Option.some.inj responded
                  have configEq :=
                    (runtime.reactive_respond_application leaks execution who action).1
                  refine ⟨rank, ⟨configEq ▸ residual⟩, fun observer entry entryMember event
                    submitted => ?_⟩
                  change entry ∈ (execution.respond app who action).recall observer at entryMember
                  change _ ∨ DecodedHolds _ rank
                    (execution.respond app who action).application.config
                  rw [configEq]
                  rw [runtime.respond_recall leaks execution who observer action]
                    at entryMember
                  split at entryMember
                  · rename_i same
                    subst same
                    rcases List.mem_append.mp entryMember with old | new
                    · exact record observer entry old event submitted
                    · cases List.mem_singleton.mp new
                      exact onePacket_submission_atTurn (runtime := runtime) bounds profile
                        rawPrior residual action
                        chosen event submitted
                  · exact record observer entry entryMember event submitted
          | none =>
              cases remaining with
              | zero =>
                  cases (PMF.mem_support_pure_iff _ _).mp realized
                  exact ⟨rank, ⟨residual⟩, record⟩
              | succ remaining =>
                  obtain ⟨command, _, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
                  obtain ⟨next, reached, nextEq⟩ := PMF.support_map .. ▸ moved
                  cases nextEq
                  have recallEq := app.environmentStep_recall execution next command reached
                  have path := (runtime.reactiveApplication_graphSteps leaks).environmentStep
                    execution next command reached
                  obtain ⟨nextRank, ⟨nextResidual⟩⟩ := residual.path path
                  refine ⟨nextRank, ⟨nextResidual⟩, fun who entry entryMember event submitted =>
                    ?_⟩
                  change entry ∈ next.recall who at entryMember
                  rw [recallEq] at entryMember
                  rcases record who entry entryMember event submitted with turn | owed
                  · exact Or.inl turn
                  · obtain ⟨owedRank, ⟨owedResidual⟩, holds⟩ :=
                      residual.decodedHolds_path (owesFailure_stepClosed who) owed path
                    have same := owedResidual.checkpoint.ordered.unique
                      nextResidual.checkpoint.ordered
                    exact Or.inr (by simpa only [same] using holds)

/-- **Own submissions at intended points are at the owner's turns.** At a
history of the one-packet game whose configuration decodes at its completed
prefix to a point of the intended game, every own submission of every player
was made at its turn at its event. -/
theorem onePacket_ownSubmissionsAtTurn {horizon : Nat}
    {scheduler : (application setup runtime leaks).Scheduler}
    {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    {rank : Nat} (ordered : control.execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank control.execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point) (who : Player) :
    OwnSubmissionsAtTurn setup leaks control.execution who := by
  obtain ⟨recordRank, ⟨residual⟩, record⟩ := ownTurnRecord_history (runtime := runtime) bounds
    (failureProfile setup.program) horizon scheduler trace control rfl
  have sameRank := EventOrder.Cut.IsPrefix.unique residual.checkpoint.ordered ordered
  subst sameRank
  intro entry member event submitted
  rcases record who entry member event submitted with turn | owed
  · exact turn
  · exact (ProtocolState.Intended.not_owesFailure who setup.program point intendedPoint
      (owed point decoded)).elim


/-- **One-packet boundaries are reached boundaries.** A history of the
one-packet game ending between rounds at an execution whose configuration is a
prefix of `rank`, with every event from `rank` on untouched and a decoding to a
point of the intended game, ends at a reached boundary: its own submissions
were made at the owners' turns (`Vegas.onePacket_ownSubmissionsAtTurn`). -/
theorem reachedBoundary_of_onePacket (bounds : MessageBounds (graph setup))
    {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler} {rank : Nat}
    {anchor : (application setup runtime leaks).Execution}
    (start : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (bounded : anchor.environmentRecall.length ≤ horizon)
    (ordered : anchor.application.config.cut.IsPrefix rank)
    (untouched : ∀ event : (graph setup).EventId, rank ≤ event.val →
      Untouched setup leaks event anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point) :
    ReachedBoundary setup runtime leaks horizon scheduler rank anchor := by
  have trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩) :=
    state ▸ start.trace
  exact ⟨⟨(bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon
      scheduler trace⟩, bounded, ordered, untouched,
    onePacket_ownSubmissionsAtTurn (runtime := runtime) bounds trace ordered point decoded
      intendedPoint⟩


end Vegas
