/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefixResponse
import Vegas.Game.RevealServicePayoffs
import Vegas.Game.RevealServiceOwnerSupport
import Vegas.Game.RevealServicePrefixLaw
import Vegas.Game.RevealServiceCollection

/-! # Terminal typed laws after an actual owner response

The native finish evaluator follows the unchanged source continuation after
one arbitrary ordinary response. This conditional equation is the input to
the local incentive comparison; it does not identify different alias histories.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
/-- The service's actual terminal cut check succeeds at every legal terminal
history, including histories reached only after a deviation. -/
theorem terminal_history_readout
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (responses : (application setup leaks).ResponseMenu) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (history : (responses.protocol (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).History)
    (terminal : (responses.protocol (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).terminal history.state) :
    sourceReadout setup leaks history.state =
      history.state.bind fun control => decodeState? (terminalRefs setup.program)
        control.execution.application.config.store := by
  obtain ⟨execution, state, settled⟩ :=
    terminal_history_settled setup leaks responses watcher reveals history terminal
  rw [state]
  exact ite_eq_left settled

/-- At the actual remaining evaluation horizon the source readout equals
the typed terminal-store decoder for every native behavioral profile. -/
theorem remaining_readout_eq_decode
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (responses : (application setup leaks).ResponseMenu) (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (profile : ∀ who, (responses.information (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).BehavioralPolicy who)
    (history : (responses.protocol (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).History) :
    ((responses.information (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).runBehavioralFrom profile
        (2 * horizon setup watcher + 1 - history.trace.length) history).map
          (fun final => sourceReadout setup leaks final.state) =
      ((responses.information (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher)).runBehavioralFrom profile
          (2 * horizon setup watcher + 1 - history.trace.length) history).map
            (fun final => final.state.bind fun control =>
              decodeState? (terminalRefs setup.program)
                control.execution.application.config.store) := by
  apply FinDist.map_congr_of_eq_on_support
  intro final supported
  have terminal : (responses.protocol (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).terminal final.state := by
    rcases (responses.protocol (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).runRandomizedFor_terminal_or_length
        ((responses.information (initialLaw setup) (horizon setup watcher)
          (scheduler setup leaks watcher)).randomizedChooser profile)
        (2 * horizon setup watcher + 1 - history.trace.length) history final supported with
      stopped | length
    · exact stopped
    · exact responses.bounded (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher) final.state final.trace (by omega)
  exact terminal_history_readout setup leaks responses watcher reveals final terminal

theorem owner_response_finish_decode_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher who : Player)
    (reveals : setup.program.RevealOnly)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (profile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy)
    (watcherPolicy : players watcher = (application setup leaks).reportFirstUnpublished)
    (ordinary : ∀ player, player ≠ watcher → ∀ past view response,
      response ∈ (players player past view).support → response ∈
        ordinaryActions setup leaks (bounds.withInitialValues (initialLaw setup)) player past view)
    (projects : ∀ player, player ≠ watcher → ∀ past view opening,
      opening? setup leaks player past view = some opening →
      opening ∈ ((bounds.withInitialValues (initialLaw setup)).menu (runtime setup) leaks).actions
        player past view →
      (players player past view).map (sourceChoice setup leaks) =
        sourceChoiceLaw setup leaks profile player view)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (source : ProtocolState setup.program) (execution : (application setup leaks).Execution)
    (related : PrefixCheckpoint setup leaks initial setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) (outputRef setup.program) 0 event.val source execution)
    (granted : execution.application.serviceGrant = some event)
    (position : execution.environmentRecall.length = blockOffset event.val + 2)
    (response : (application setup leaks).Action)
    (member : response ∈ ordinaryActions setup leaks (bounds.withInitialValues (initialLaw setup))
      who (execution.recall who) (execution.observe (application setup leaks) who))
    (joint : Player → Option (OwnAction Player L))
    (chosen : OwnAction.disclosure (joint who) = sourceChoice setup leaks response) :
    ((application setup leaks).finish (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) players
      (some ⟨horizon setup watcher - blockOffset event.val - 2, none,
        execution.respond (application setup leaks) who response⟩)).map
      (fun state => state.bind fun control => decodeState? (terminalRefs setup.program)
        control.execution.application.config.store) =
      ((ProtocolState.step setup.program source joint).bind
        (ProtocolState.continuationLaw setup.program profile)).map some := by
  obtain ⟨rest, split⟩ := plan_split_at setup watcher event
  let after := [.includeLatest event who, .player watcher, .wire] ++
    List.replicate (event.val + 1) .tick ++ [.expire event] ++ rest
  have split' : plan setup watcher =
      planPrefix setup watcher event.val ++ .grant event :: .player who :: after := by
    rw [split, block_of_owner setup watcher who event owned]
    simp only [after, List.append_assoc, List.cons_append, List.nil_append]
  have sourceSplit : plan setup watcher = planPrefix setup watcher event.val ++
      (((List.finRange (eventCount setup.program)).drop event.val).flatMap
        (block setup watcher)) := by
    change (List.finRange (eventCount setup.program)).flatMap (block setup watcher) =
      ((List.finRange (eventCount setup.program)).take event.val).flatMap
          (block setup watcher) ++ _
    rw [← List.flatMap_append, List.take_append_drop]
  have suffixEq := List.append_cancel_left (sourceSplit.symm.trans split')
  have afterEq : ((((List.finRange (eventCount setup.program)).drop event.val).flatMap
      (block setup watcher)).drop 2) = after := by
    rw [suffixEq]
    rfl
  have lengthPrefix := planPrefix_length setup watcher reveals event.val event.isLt.le
  have remaining : horizon setup watcher - blockOffset event.val - 2 = after.length := by
    have lengths := congrArg List.length split'
    simp only [List.length_append, List.length_cons, lengthPrefix] at lengths
    change (plan setup watcher).length - blockOffset event.val - 2 = _
    omega
  have rounds := suffix_rounds setup leaks watcher players
    (planPrefix setup watcher event.val ++ [.grant event, .player who]) after
    (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using split')
    (execution.respond (application setup leaks) who response) (by
      simp only [ReactiveApplication.respond_environmentRecall, List.length_append,
        List.length_cons, List.length_nil, lengthPrefix, position])
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, FinDist.pure_bind,
    remaining, rounds, FinDist.map_comp, Function.comp_def, ReactiveApplication.finished,
    Option.bind_some]
  have law := prefix_response_option_law setup leaks bounds watcher observer profile players
    watcherPolicy ordinary projects initial initialSupport setup.program reveals profile
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputEmbedding setup.program)
    (initialRefsBefore setup.program) 0 (CompiledPolicySuffix.whole setup.program profile)
    event.val event.isLt source execution related who owned granted response member joint chosen
  change ((runtime setup).runInteractionPlan leaks players
    ((runtime setup).reportNetwork leaks watcher)
    ((((List.finRange (eventCount setup.program)).drop event.val).flatMap
      (block setup watcher)).drop 2)
    (execution.respond (application setup leaks) who response)).map
      (fun final => decodeState? (terminalRefs setup.program) final.application.config.store) = _
    at law
  rw [afterEq] at law
  exact law

end Vegas.SourceProgram.RevealService
