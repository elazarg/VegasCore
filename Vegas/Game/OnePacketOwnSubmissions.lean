/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketActorRecord
import Vegas.Game.SourceServiceTurnSubmissions
import Vegas.Pending.ReactiveSignedCommitments

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

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

variable {Γ : SourceCtx Player L} {unresolved : Finset VarId} {config : Config Player L Γ}

omit [IExpr.ResultTypes L] in
/-- An intended configuration owes no failed reveal. -/
theorem Intended.not_indebted (intended : config.Intended unresolved) (who : Player) :
    ¬ config.Indebted who unresolved := by
  intro indebted
  obtain ⟨obligation, member, _, _, value, bound, rejects⟩ := indebted.pending
  rw [intended.predicted obligation member value bound] at rejects
  cases rejects

omit [IExpr.ResultTypes L] in
/-- An intended configuration has no failed binding. -/
theorem Intended.not_failedBinding (intended : config.Intended unresolved) (who : Player) :
    ¬ config.FailedBinding who unresolved := by
  intro failed
  obtain ⟨_, _, source, _, failure⟩ := failed.pending
  obtain ⟨value, success⟩ := intended.bound source
  rw [success] at failure
  cases failure

end Config

namespace ProtocolState

/-- A point of the intended game has no failed reveal or debt. -/
theorem Intended.not_indebted (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    Intended program state → ¬ Indebted who program state
  | _, _, .ret _, _, intended =>
      Config.Intended.not_indebted (unresolved := ∅) intended who
  | _, _, .sample _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact Config.Intended.not_indebted intended.1 who
      | inr rest => exact Intended.not_indebted who next rest intended
  | _, _, .commit _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact Config.Intended.not_indebted intended.1 who
      | inr rest => exact Intended.not_indebted who next rest intended
  | _, _, .reveal _ _ _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact Config.Intended.not_indebted intended.1 who
      | inr rest =>
          rintro (⟨_, failure⟩ | indebted)
          · obtain ⟨value, success⟩ := intended.1
            rw [success] at failure
            cases failure
          · exact Intended.not_indebted who next rest intended.2 indebted

/-- A point of the intended game has no failed binding. -/
theorem Intended.not_failedBinding (who : Player) : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (state : ProtocolState program) → Intended program state → ¬ FailedBinding who program state
  | _, _, .ret _, _, intended =>
      Config.Intended.not_failedBinding (unresolved := ∅) intended who
  | _, _, .sample _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact Config.Intended.not_failedBinding intended.1 who
      | inr rest => exact Intended.not_failedBinding who next rest intended
  | _, _, .commit _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact Config.Intended.not_failedBinding intended.1 who
      | inr rest => exact Intended.not_failedBinding who next rest intended
  | _, _, .reveal _ _ _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact Config.Intended.not_failedBinding intended.1 who
      | inr rest =>
          rintro (⟨_, failure⟩ | failed)
          · obtain ⟨value, success⟩ := intended.1
            rw [success] at failure
            cases failure
          · exact Intended.not_failedBinding who next rest intended.2 failed

/-- **Intended points owe nothing.** No player owes a failure at a point of the
intended game. -/
theorem Intended.not_owesFailure (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program)
    (intended : Intended program state) : ¬ OwesFailure who program state := by
  rintro (indebted | failed)
  · exact Intended.not_indebted who program state intended indebted
  · exact Intended.not_failedBinding who program state intended failed

end ProtocolState

end Vegas.SourceProgram

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup leaks) in
/-- **The own-turn record.** The configuration decodes at a prefix, and every
own submission of a player was made at its turn at its event, or that player
owes a failure at the decoded point. -/
def OwnTurnRecord (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution) : Prop :=
  ∃ rank, Nonempty (SourceResidual setup profile rank execution.application.config) ∧
    ∀ who, ∀ entry ∈ execution.recall who, ∀ event,
      (runtime setup).submittedEvent? leaks entry.action = some event →
        entry.beforeView.application.publicView.ownTurn? who = some event ∨
        DecodedHolds (ProtocolState.OwesFailure who setup.program) rank
          execution.application.config

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- **A one-packet submission is at its owner's turn, or the owner owes.** At a
history of the one-packet game, every transmitting one-packet response of
`who` names an event at `who`'s turn, or `who` owes a failure at the decoded
point. -/
theorem onePacket_submission_atTurn {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} (profile : BehavioralProfile setup.program)
    {rank remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (residual : SourceResidual setup profile rank execution.application.config)
    (action : (application setup leaks).Action)
    (member : action ∈ bounds.onePacketActions (runtime setup) leaks who (execution.recall who)
      (execution.observe (application setup leaks) who))
    (event : (graph setup).EventId)
    (submitted : (runtime setup).submittedEvent? leaks action = some event) :
    execution.application.publicView.ownTurn? who = some event ∨
      DecodedHolds (ProtocolState.OwesFailure who setup.program) rank
        execution.application.config := by
  let app := application setup leaks
  rcases ((bounds.mem_onePacketActions (runtime setup) leaks who _ _ action).mp member).2 with
    silent | ⟨material, transmits, permitted⟩
  · unfold EventGraphRuntime.submittedEvent? at submitted
    rw [silent] at submitted
    cases submitted
  have materialNamed : material.call.packet.event? (graph setup) = some event := by
    unfold EventGraphRuntime.submittedEvent? at submitted
    rw [transmits] at submitted
    exact submitted
  obtain ⟨inputRecall, serialRecall, _⟩ := (runtime setup).countRecall_history leaks trace
  have facts := settledFacts_history (initialLaw setup) horizon scheduler trace
  set envelope := (runtime setup).localEnvelope leaks who (execution.recall who)
    (execution.observe app who) material with envelopeEq
  obtain ⟨tokenValid, correct, first⟩ := (countPermits_eq_true_iff _ _).mp permitted
  obtain ⟨named, namedEvent, tokenEq⟩ := (WitnessedPacket.tokenValid_iff _).mp tokenValid
  have sameEvent : named = event := by
    have call : envelope.payload.call = material.call.packet := rfl
    rw [call, materialNamed] at namedEvent
    exact (Option.some.inj namedEvent).symm
  subst sameEvent
  have sender : envelope.sender = who := rfl
  have actor := countCallCorrect_actor _ envelope correct namedEvent
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
      actorRecord_history profile horizon scheduler trace
    have sameRank := isPrefix_unique recordResidual.checkpoint.ordered residual.checkpoint.ordered
    subst sameRank
    rcases record named completed who actor with
      ⟨message, onLedger, _, messageNamed, messageSender⟩ | owed
    · exfalso
      have emitted : message ∈ execution.network.inputs := facts.carried.ledger message onLedger
      have recalled : message ∈ app.outputs (execution.recall who) := by
        rw [← inputRecall who]
        exact List.mem_filter.mpr ⟨emitted, by simp [messageSender]⟩
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
    exact ready_unique (setup := setup) _
      ((execution.application.publicView_eventReady other).mp otherReady) ready

/-- **The own-turn record holds along one-packet histories.** At every history
of the one-packet game, under every scheduler, every own submission of a player
was made at its turn at its event, or that player owes a failure at the decoded
point. -/
theorem ownTurnRecord_history (profile : BehavioralProfile setup.program) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) :
    ∀ {state} (_ : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
        horizon scheduler).Trace state) (control : (application setup leaks).Control),
      state = some control → OwnTurnRecord setup leaks profile control.execution := by
  let app := application setup leaks
  let menu := bounds.onePacketMenu (runtime setup) leaks
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
                  have chosen : action ∈ bounds.onePacketActions (runtime setup) leaks who
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
                    ((runtime setup).reactive_respond_application leaks execution who action).1
                  refine ⟨rank, ⟨configEq ▸ residual⟩, fun observer entry entryMember event
                    submitted => ?_⟩
                  change entry ∈ (execution.respond app who action).recall observer at entryMember
                  change _ ∨ DecodedHolds _ rank
                    (execution.respond app who action).application.config
                  rw [configEq]
                  rw [(runtime setup).respond_recall leaks execution who observer action]
                    at entryMember
                  split at entryMember
                  · rename_i same
                    subst same
                    rcases List.mem_append.mp entryMember with old | new
                    · exact record observer entry old event submitted
                    · cases List.mem_singleton.mp new
                      exact onePacket_submission_atTurn bounds profile rawPrior residual action
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
                  have configStep := environmentStep_configStep setup leaks execution next
                    command reached
                  obtain ⟨nextRank, ⟨nextResidual⟩⟩ : ∃ nextRank, Nonempty
                      (SourceResidual setup profile nextRank next.application.config) := by
                    rcases configStep with same | ⟨event, ready, action, member⟩
                    · exact ⟨rank, ⟨same ▸ residual⟩⟩
                    · obtain ⟨successor, _⟩ := residual.step event ready action _ member
                      exact ⟨rank + 1, ⟨successor⟩⟩
                  refine ⟨nextRank, ⟨nextResidual⟩, fun who entry entryMember event submitted =>
                    ?_⟩
                  change entry ∈ next.recall who at entryMember
                  rw [recallEq] at entryMember
                  rcases record who entry entryMember event submitted with turn | owed
                  · exact Or.inl turn
                  · exact Or.inr (residual.decodedHolds_configStep
                      (fun state joint target owing reached =>
                        ProtocolState.owesFailure_step who setup.program state joint target owing
                          reached)
                      owed configStep nextResidual.checkpoint.ordered)

/-- **Own submissions at intended points are at the owner's turns.** At a
history of the one-packet game whose configuration decodes at its completed
prefix to a point of the intended game, every own submission of every player
was made at its turn at its event. -/
theorem onePacket_ownSubmissionsAtTurn {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    {rank : Nat} (ordered : control.execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank control.execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point) (who : Player) :
    OwnSubmissionsAtTurn setup leaks control.execution who := by
  obtain ⟨recordRank, ⟨residual⟩, record⟩ := ownTurnRecord_history bounds
    (failureProfile setup.program) horizon scheduler trace control rfl
  have sameRank := isPrefix_unique residual.checkpoint.ordered ordered
  subst sameRank
  intro entry member event submitted
  rcases record who entry member event submitted with turn | owed
  · exact turn
  · exact (ProtocolState.Intended.not_owesFailure who setup.program point intendedPoint
      (owed point decoded)).elim

end Vegas
