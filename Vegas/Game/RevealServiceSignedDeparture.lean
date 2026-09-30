/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceReplayTraffic
import Vegas.Game.RevealServiceTrafficDeparture
import Interaction.ReactiveAllocation

/-! # Every additional response produces attributable signed-envelope evidence

All public-ID replays remain admitted. At a retained checkpoint any further
effective response is therefore a fresh authored submission. Its signer,
transmission phase and prior ledger suffice to certify the departure.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)
  (reveals : setup.program.RevealOnly)
  (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)

omit [Fintype Player] in
private theorem openingTraffic_actor (record : (application setup leaks).TrafficRecord)
    (allowed : openingTraffic setup leaks record) :
    ∃ event, (graph setup).actor? event = some record.input.envelope.sender := by
  unfold openingTraffic at allowed
  cases call : record.input.envelope.payload.call with
  | commitment | withhold | malformed => simp only [call] at allowed
  | opening event candidate raw =>
    rw [call] at allowed
    obtain ⟨_, _, _, linked⟩ := allowed
    cases node : nodeView (graph setup) event with
    | bind | sample => simp only [node] at linked
    | resolve owner payload binding checks outputEq codeEq =>
      simp only [node] at linked
      have actors := congrArg EventCode.actor codeEq
      rw [EventCode.actor_cast outputEq ((graph setup).nodes event)] at actors
      refine ⟨event, ?_⟩
      exact actors.trans (congrArg some linked.2.1.symm)

omit [Fintype Player] in
include observer in
private theorem observer_opening_none
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    opening? setup leaks watcher past view = none := by
  unfold opening?
  rw [PublicView.ownTurn?_eq_none _ watcher (fun event _ => observer event)]
  rfl

include reveals observer openable in
theorem replay_extra_submission
    (history : ((replayMenu setup leaks bounds watcher).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).History)
    (remaining : Nat) (who : Player) (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (excluded : response ∉ (replayMenu setup leaks bounds watcher).actions who
      (execution.recall who) (execution.observe (application setup leaks) who)) :
    ∃ submission, response = ⟨some (.submit submission)⟩ := by
  classical
  have clean := replay_active_clean setup leaks bounds watcher reveals observer openable
    history ⟨remaining, some who, execution⟩ current who rfl
  have recalled := (application setup leaks).history_inputRecall (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher)
    ((replayMenu setup leaks bounds watcher).toRawTrace (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher) history.trace)
  rw [current] at recalled
  apply extra_response_submission setup leaks bounds execution who recalled
  · apply execution.network.known_published who clean.2.2
    intro message member
    change message ∈ execution.network.leaked who at member
    rw [clean.1] at member
    exact (List.not_mem_nil member).elim
  · exact effective
  · intro allowed
    apply excluded
    by_cases watches : who = watcher
    · subst who
      rw [replay_menu_watcher]
      have quiet : (application setup leaks).reportFirstUnpublished (execution.recall watcher)
          (execution.observe (application setup leaks) watcher) = PMF.pure ⟨none⟩ := by
        apply ReactiveApplication.reportFirstUnpublished_silent
        intro message observed
        change message ∈ execution.network.leaked watcher at observed
        rw [clean.1] at observed
        exact (List.not_mem_nil observed).elim
      rcases ordinary_response_cases setup leaks bounds watcher _ _ response allowed with
        silence | opening | replayed
      · subst response
        apply Finset.mem_union_left
        rw [Set.Finite.mem_toFinset, quiet, PMF.mem_support_pure_iff _ _]
      · rw [observer_opening_none setup leaks watcher observer] at opening
        cases opening
      · exact Finset.mem_union_right _ ((mem_publishedReplays setup leaks _ response).mpr replayed)
    · rw [replay_menu_ordinary setup leaks bounds watcher who watches]
      exact allowed

include reveals observer openable in
/-- An additional effective response yields a forbidden fresh envelope whose
signed author is the deviator. No rebroadcaster authentication is used. -/
theorem replay_extra_traffic
    (history : ((replayMenu setup leaks bounds watcher).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).History)
    (remaining : Nat) (who : Player) (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (excluded : response ∉ (replayMenu setup leaks bounds watcher).actions who
      (execution.recall who) (execution.observe (application setup leaks) who)) :
    ∃ record, (application setup leaks).trafficStep
      (some ⟨remaining, some who, execution⟩)
      (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩) =
        [record] ∧ record.input.envelope.sender = who ∧
        permittedEnvelope setup leaks (envelopeEvidence setup leaks record) = false := by
  obtain ⟨submission, rfl⟩ := replay_extra_submission setup leaks bounds watcher reveals observer
    openable history remaining who execution current response effective excluded
  let record : (application setup leaks).TrafficRecord :=
    ⟨execution.application.publicView, execution.network.ledger,
      ⟨who, ⟨(who, execution.network.nextSerial who), submission.emit
        ((application setup leaks).submit execution.application who submission) who
          (execution.network.known who)⟩⟩⟩
  have actual : (application setup leaks).trafficStep
      (some ⟨remaining, some who, execution⟩)
      (some ⟨remaining, none, execution.respond (application setup leaks) who
        ⟨some (.submit submission)⟩⟩) = [record] :=
    (application setup leaks).trafficStep_submit execution remaining who submission
  refine ⟨record, actual, rfl, ?_⟩
  by_cases watches : who = watcher
  · subst who
    have serials := (application setup leaks).serialsBeforeNext_history
      (scheduler setup leaks watcher) (initialLaw setup) (horizon setup watcher)
      ((replayMenu setup leaks bounds watcher).toRawTrace (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher) history.trace)
    rw [current] at serials
    cases verdict : permittedEnvelope setup leaks (envelopeEvidence setup leaks record) with
    | false => rfl
    | true =>
      obtain published | opening := (permittedEnvelope_iff setup leaks record rfl).mp verdict
      · exact (serials.next_unpublished watcher published).elim
      · obtain ⟨event, owner⟩ := openingTraffic_actor setup leaks record opening
        exact (observer event owner).elim
  · obtain ⟨original, first, state, same⟩ := replay_history_counterpart setup leaks bounds watcher
      reveals observer openable history ⟨remaining, some who, execution⟩ current
    have sourceEffective := effective
    rw [← same.recall who watches, ← same.observe who] at sourceEffective
    have sourceExtra : (⟨some (.submit submission)⟩ : (application setup leaks).Action) ∉
        ordinaryActions setup leaks bounds who (first.recall who)
          (first.observe (application setup leaks) who) := by
      rw [replay_menu_ordinary setup leaks bounds watcher who watches,
        ← same.recall who watches, ← same.observe who] at excluded
      exact excluded
    obtain ⟨sourceRecord, sourceTraffic, authored, forbidden⟩ := owner_extra_traffic setup leaks
      bounds watcher reveals observer openable who watches original remaining first state
        ⟨some (.submit submission)⟩ sourceEffective sourceExtra
    have sameTraffic := ReplayAgreement.ordinary_traffic setup leaks watcher same who watches
      remaining ⟨some (.submit submission)⟩
    have equalRecord : sourceRecord = record :=
      (List.cons.inj (sourceTraffic.symm.trans (sameTraffic.trans actual))).1
    subst sourceRecord
    exact permittedEnvelope_forbidden setup leaks watcher record
      (by simpa only [record] using watches) rfl forbidden


include reveals observer openable in
open Classical in
/-- Committing any additional effective response at a retained site records an
attributable violation after the actual first behavioral step. Later profile
choices play no role in the certificate. -/
theorem replay_extra_choice_traffic
    (profile : Profile (effectiveInformation setup leaks bounds watcher).behavioralSignature)
    (who : Player) (site : ((replayMenu setup leaks bounds watcher).information (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).InformationSite who)
    (action : (effectiveInformation setup leaks bounds watcher).Choice who
      (((replay_in_effective setup leaks bounds watcher).actionRestriction (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)).site who site).1)
    (extra : action ∉ Set.range
      (((replay_in_effective setup leaks bounds watcher).actionRestriction (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)).choice who site.1))
    (history : ((replayMenu setup leaks bounds watcher).information (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).InformationHistory who site.1)
    (next : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).History)
    (supported : next ∈ ((effectiveInformation setup leaks bounds watcher).runBehavioralFrom
      (Profile.update (sig := (effectiveInformation setup leaks bounds watcher).behavioralSignature)
        profile who ((profile who).commit
          (((replay_in_effective setup leaks bounds watcher).actionRestriction (initialLaw setup)
            (horizon setup watcher) (scheduler setup leaks watcher)).site who site).1 action))
      1 (((replay_in_effective setup leaks bounds watcher).actionRestriction (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)).history history.1)).support) :
    ∃ record ∈ (application setup leaks).stateTraffic next.state,
      record.input.envelope.sender = who ∧
      permittedEnvelope setup leaks (envelopeEvidence setup leaks record) = false := by
  classical
  let sourceMenu := replayMenu setup leaks bounds watcher
  let targetMenu := bounds.menu (runtime setup) leaks
  let included := replay_in_effective setup leaks bounds watcher
  let initial := initialLaw setup
  let horizon := horizon setup watcher
  let scheduler := scheduler setup leaks watcher
  let restriction := included.actionRestriction initial horizon scheduler
  rcases site with ⟨info, occurs⟩
  have active := InformationModel.InformationSite.active
    (sourceMenu.information initial horizon scheduler) ⟨info, occurs⟩ history
  cases current : history.1.state with
  | none => simp only [current, ReactiveApplication.ResponseMenu.protocol,
      ReactiveApplication.actor, Option.bind_none, reduceCtorEq] at active
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      have actorEq : actor = some who := by
        simpa only [current, ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor,
          Option.bind_some] using active
      subst actor
      have observed : info = some (execution.recall who,
          execution.observe (application setup leaks) who) := by
        have seen := history.2
        change (sourceMenu.signals initial horizon scheduler).infoOf who history.1.trace = info
          at seen
        rw [sourceMenu.info, current] at seen
        simpa only [ReactiveApplication.observe, ↓reduceIte] using seen.symm
      subst info
      change (effectiveInformation setup leaks bounds watcher).Choice who
        (some (execution.recall who, execution.observe (application setup leaks) who)) at action
      obtain ⟨response, selected, effective, excluded⟩ :=
        included.extra_choice_response initial horizon scheduler who _ _ action extra
      obtain ⟨record, recorded, attributed, forbidden⟩ :
          ∃ record, (application setup leaks).trafficStep
              (some ⟨remaining, some who, execution⟩)
              (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩) =
                [record] ∧ record.input.envelope.sender = who ∧
            permittedEnvelope setup leaks (envelopeEvidence setup leaks record) = false := by
        exact replay_extra_traffic setup leaks bounds watcher reveals observer openable
          history.1 remaining who execution current response effective excluded
      let native := restriction.history history.1
      have nativeState : native.state = some ⟨remaining, some who, execution⟩ := current
      have nativeInfo : (effectiveInformation setup leaks bounds watcher).infoOf who native.trace =
          some (execution.recall who, execution.observe (application setup leaks) who) :=
        (included.observed initial horizon scheduler who history.1).trans history.2
      let chosen : (effectiveInformation setup leaks bounds watcher).Choice who
          ((effectiveInformation setup leaks bounds watcher).infoOf who native.trace) :=
        ⟨action.1, by simpa only [nativeInfo] using action.2⟩
      have one := targetMenu.run_commit_response initial horizon scheduler profile native who
        remaining execution nativeState chosen response selected
      change (targetMenu.information initial horizon scheduler).infoOf who native.trace = _
        at nativeInfo
      have stateLaw : ((effectiveInformation setup leaks bounds watcher).runBehavioralFrom
          (Profile.update (sig :=
            (effectiveInformation setup leaks bounds watcher).behavioralSignature)
            profile who ((profile who).commit
              (some (execution.recall who,
                execution.observe (application setup leaks) who)) action))
          1 native).map History.state =
            PMF.pure (some ⟨remaining, none,
              execution.respond (application setup leaks) who response⟩) := by
        have transport
            (first last : (effectiveInformation setup leaks bounds watcher).InfoState who)
            (same : first = last)
            (left : (effectiveInformation setup leaks bounds watcher).Choice who first)
            (right : (effectiveInformation setup leaks bounds watcher).Choice who last)
            (value : left.1 = right.1) :
            (profile who).commit first left = (profile who).commit last right := by
          subst last
          have equal : left = right := Subtype.ext value
          subst right
          rfl
        have installed := transport _ _ nativeInfo chosen action rfl
        rw [installed] at one
        exact one
      have nextState : next.state = some ⟨remaining, none,
          execution.respond (application setup leaks) who response⟩ := by
        have inMap : next.state ∈ (PMF.pure (some ⟨remaining, none,
            execution.respond (application setup leaks) who response⟩)).support := by
          rw [← stateLaw, PMF.support_map]
          exact ⟨next, supported, rfl⟩
        exact (PMF.mem_support_pure_iff _ _).mp inMap
      let original := sourceMenu.toRawHistory initial horizon scheduler history.1
      have transition : some ⟨remaining, none,
          execution.respond (application setup leaks) who response⟩ ∈
            ((application setup leaks).transition initial horizon scheduler original.state
              (fun _ => some response)).support := by
        change _ ∈ ((application setup leaks).transition initial horizon scheduler history.1.state
          (fun _ => some response)).support
        simp only [current, ReactiveApplication.transition, Option.getD_some,
          PMF.mem_support_pure_iff _ _]
      have audit := (application setup leaks).stateTraffic_transition initial horizon scheduler
        original (fun _ => some response) _ transition
      refine ⟨record, ?_, attributed, forbidden⟩
      rw [nextState, audit]
      change record ∈ _ ++ (application setup leaks).trafficStep history.1.state _
      rw [current, recorded]
      exact List.mem_append_right _ (List.mem_singleton_self _)

end Vegas
