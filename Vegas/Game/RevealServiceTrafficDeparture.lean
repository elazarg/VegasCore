/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceTraffic
import Vegas.Game.RevealServicePrefixEnforcement
import Vegas.Game.RevealServiceOwnerSupport
import Vegas.Game.RevealServiceWatcherSupport
import Interaction.ReactiveLocalContinuation
import Interaction.ReactiveTrafficState

/-! # Attributable audit evidence for every extra retained response

Every added effective response at a retained information history emits an
actual forbidden traffic record. Ordinary owners use the checked source-prefix
packet classifier. The reporting player is silent at every compliant history;
its extra transmissions are attributed to that broadcaster, including replays.
Later players and schedulers cannot remove these authenticated records.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)
  (reveals : setup.program.RevealOnly)
  (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)

include reveals observer openable in
theorem owner_extra_traffic (who : Player) (ordinary : who ≠ watcher)
    (history : (protocol setup leaks bounds watcher).History)
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (excluded : response ∉ ordinaryActions setup leaks bounds who (execution.recall who)
      (execution.observe (application setup leaks) who)) :
    ∃ record, (application setup leaks).trafficStep
        (some ⟨remaining, some who, execution⟩)
        (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩) =
          [record] ∧ record.input.broadcaster = who ∧
      permittedTraffic setup leaks watcher record = false := by
  let responses := menu setup leaks bounds watcher
  let reference := responses.uniformPolicy (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)
  have active : (protocol setup leaks bounds watcher).active history.state who := by
    change (application setup leaks).actor history.state = some who
    rw [current]
    rfl
  obtain ⟨event, owned, _length, supported⟩ := owner_history_supported setup leaks bounds
    watcher who reveals ordinary history active
  obtain ⟨boundary, _supported, nativeState, initial, _initialSupport, source,
      _boundaryCheckpoint, related, _decoded⟩ :=
    owner_supported setup leaks bounds watcher who reveals observer openable reference
      event owned history supported
  have sameExecution : execution = ownerOpportunity setup leaks event who boundary :=
    congrArg ReactiveApplication.Control.execution
      (Option.some.inj (current.symm.trans nativeState))
  have checkpoint : PrefixCheckpoint setup leaks initial setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) (outputRef setup.program) 0 event.val source execution :=
    sameExecution.symm ▸ related
  have grant : execution.application.serviceGrant = some event := by rw [sameExecution]; rfl
  obtain ⟨submission, same, departure⟩ := prefix_extra_submission setup leaks bounds who reveals
    initial event owned source execution checkpoint grant response effective excluded
  subst response
  have serials : execution.network.SerialsBeforeNext :=
    PrefixCheckpoint.runtime_fact (fun next => next.network.SerialsBeforeNext)
      (fun _ _ _ _ checkpoint => checkpoint.serials) _ _ _ _ _ _ _ _ checkpoint
  have binding : execution.application.BindingInvariant :=
    PrefixCheckpoint.runtime_fact (fun next => next.application.BindingInvariant)
      (fun _ _ _ _ checkpoint => checkpoint.binding) _ _ _ _ _ _ _ _ checkpoint
  have sound := ((runtime setup).packetEvidence leaks).history_sound (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher)
    (responses.toRawTrace (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) history.trace)
  rw [current] at sound
  refine ⟨_, (application setup leaks).trafficStep_submit execution remaining who submission,
    rfl, ?_⟩
  exact departureTraffic_forbidden setup leaks execution watcher who sound binding serials
    submission departure

include reveals observer openable in
theorem watcher_extra_traffic
    (history : (protocol setup leaks bounds watcher).History)
    (remaining : Nat) (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some watcher, execution⟩)
    (response : (application setup leaks).Action)
    (effective : response ∈ (bounds.menu (runtime setup) leaks).actions watcher
      (execution.recall watcher) (execution.observe (application setup leaks) watcher))
    (excluded : response ∉ (menu setup leaks bounds watcher).actions watcher
      (execution.recall watcher) (execution.observe (application setup leaks) watcher)) :
    ∃ record, (application setup leaks).trafficStep
        (some ⟨remaining, some watcher, execution⟩)
        (some ⟨remaining, none, execution.respond (application setup leaks) watcher response⟩) =
          [record] ∧ record.input.broadcaster = watcher ∧
      permittedTraffic setup leaks watcher record = false := by
  have silent := watcher_history_silent setup leaks bounds watcher reveals observer openable
    history ⟨remaining, some watcher, execution⟩ current rfl
  have nonempty : response ≠ ⟨none⟩ := by
    intro same
    apply excluded
    simp only [menu, ↓reduceIte, silent, FinDist.mem_supportFinset,
      FinDist.mem_support_pure, same]
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact (nonempty rfl).elim
  | some transmission =>
      cases transmission with
      | submit submission =>
          exact ⟨_, (application setup leaks).trafficStep_submit execution remaining watcher
            submission, rfl, permittedTraffic_reporter setup leaks watcher _ rfl⟩
      | replay id =>
          have recalled := (application setup leaks).history_inputRecall (initialLaw setup)
            (horizon setup watcher) (scheduler setup leaks watcher)
            ((menu setup leaks bounds watcher).toRawTrace (initialLaw setup) (horizon setup watcher)
              (scheduler setup leaks watcher) history.trace)
          rw [current] at recalled
          have known := ((bounds.menu_mem (runtime setup) leaks watcher _ _ _).mp effective).1
          have actual := (ReactiveApplication.SubmissionNormalization.replayKnown_iff
            (app := application setup leaks) execution watcher recalled id).mp known
          obtain ⟨message, member, identified⟩ := actual
          have found : ∃ message, (execution.network.known watcher).find?
              (fun packet => packet.id = id) = some message := by
            apply Option.isSome_iff_exists.mp
            exact List.find?_isSome.mpr ⟨message, member, by simp only [identified, decide_true]⟩
          obtain ⟨message, found⟩ := found
          exact ⟨_, (application setup leaks).trafficStep_replay execution remaining watcher id
            message found, rfl, permittedTraffic_reporter setup leaks watcher _ rfl⟩

include reveals observer openable in
open Classical in
/-- Committing any additional effective response at a retained site records an
attributable violation after the actual first behavioral step. Later profile
choices play no role in the certificate. -/
theorem extra_choice_traffic
    (profile : Profile (effectiveInformation setup leaks bounds watcher).behavioralSignature)
    (who : Player) (site : (information setup leaks bounds watcher).InformationSite who)
    (action : (effectiveInformation setup leaks bounds watcher).Choice who
      (((menu_in_effective setup leaks bounds watcher).actionRestriction (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)).site who site).1)
    (extra : action ∉ Set.range
      (((menu_in_effective setup leaks bounds watcher).actionRestriction (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)).choice who site.1))
    (history : (information setup leaks bounds watcher).InformationHistory who site.1)
    (next : ((bounds.menu (runtime setup) leaks).protocol (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher)).History)
    (supported : next ∈ ((effectiveInformation setup leaks bounds watcher).runBehavioralFrom
      (Profile.update (sig := (effectiveInformation setup leaks bounds watcher).behavioralSignature)
        profile who ((profile who).commit
          (((menu_in_effective setup leaks bounds watcher).actionRestriction (initialLaw setup)
            (horizon setup watcher) (scheduler setup leaks watcher)).site who site).1 action))
      1 (((menu_in_effective setup leaks bounds watcher).actionRestriction (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher)).history history.1)).support) :
    ∃ record ∈ (application setup leaks).stateTraffic next.state,
      record.input.broadcaster = who ∧ permittedTraffic setup leaks watcher record = false := by
  classical
  let sourceMenu := menu setup leaks bounds watcher
  let targetMenu := bounds.menu (runtime setup) leaks
  let included := menu_in_effective setup leaks bounds watcher
  let initial := initialLaw setup
  let horizon := horizon setup watcher
  let scheduler := scheduler setup leaks watcher
  let restriction := included.actionRestriction initial horizon scheduler
  rcases site with ⟨info, occurs⟩
  have active := InformationModel.InformationSite.active
    (information setup leaks bounds watcher) ⟨info, occurs⟩ history
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
                [record] ∧ record.input.broadcaster = who ∧
            permittedTraffic setup leaks watcher record = false := by
        by_cases same : who = watcher
        · subst who
          exact watcher_extra_traffic setup leaks bounds watcher reveals observer openable
            history.1 remaining execution current response effective excluded
        · apply owner_extra_traffic setup leaks bounds watcher reveals observer openable who same
            history.1 remaining execution current response effective
          simpa only [menu, same, ↓reduceIte] using excluded
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
            FinDist.pure (some ⟨remaining, none,
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
        have inMap : next.state ∈ (FinDist.pure (some ⟨remaining, none,
            execution.respond (application setup leaks) who response⟩)).support := by
          rw [← stateLaw, FinDist.support_map]
          exact ⟨next, supported, rfl⟩
        exact FinDist.mem_support_pure.mp inMap
      let original := sourceMenu.toRawHistory initial horizon scheduler history.1
      have transition : some ⟨remaining, none,
          execution.respond (application setup leaks) who response⟩ ∈
            ((application setup leaks).transition initial horizon scheduler original.state
              (fun _ => some response)).support := by
        change _ ∈ ((application setup leaks).transition initial horizon scheduler history.1.state
          (fun _ => some response)).support
        simp only [current, ReactiveApplication.transition, Option.getD_some,
          FinDist.mem_support_pure]
      have audit := (application setup leaks).stateTraffic_transition initial horizon scheduler
        original (fun _ => some response) _ transition
      refine ⟨record, ?_, attributed, forbidden⟩
      rw [nextState, audit]
      change record ∈ _ ++ (application setup leaks).trafficStep history.1.state _
      rw [current, recorded]
      exact List.mem_append_right _ (List.mem_singleton_self _)

end Vegas
