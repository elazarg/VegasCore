/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceReplayContinuation
import Vegas.Game.RevealServiceClock

/-! # Harmless published-replay deviations at retained information sites

The comparator is a lawful response at the original site, selected independently
of the hidden history. Every extra choice is a watcher replay of a public ID.
Its entire continuation has the same application-state law as silence.
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

open Classical in
private theorem local_law_at {app : ReactiveApplication Player}
    (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler)
    (profile : Profile (menu.information initial horizon scheduler).behavioralSignature)
    (history : (menu.protocol initial horizon scheduler).History)
    (who : Player) (remaining : Nat) (execution : app.Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (info : app.Info)
    (observed : (menu.information initial horizon scheduler).infoOf who history.trace = info)
    (law : PMF ((menu.information initial horizon scheduler).Choice who info)) :
    ((menu.information initial horizon scheduler).runBehavioralFrom
      (Profile.update profile who ((profile who).withLaw info law))
      (2 * horizon + 1 - history.trace.length) history).map History.state =
      (law.map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
        app.finish initial horizon scheduler (menu.decodeProfile initial horizon scheduler profile)
          (some ⟨remaining, none, execution.respond app who response⟩) := by
  subst info
  exact menu.run_local_law_remaining initial horizon scheduler profile history who
    remaining execution current law

open Classical in
include reveals observer openable in
/-- The complete application-state law is independent of the extra public replay.
The source comparator may be any local law: the retained watcher menu is forced
silence at every history in this information site. -/
theorem replay_extra_continuation_law
    (source : Profile (information setup leaks bounds watcher).behavioralSignature)
    (target : Profile ((replayMenu setup leaks bounds watcher).information
      (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).behavioralSignature)
    (agrees : ((menu_in_replay setup leaks bounds watcher).actionRestriction
      (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).ExtendsProfile
        source target)
    (who : Player) (site : (information setup leaks bounds watcher).InformationSite who)
    (action : ((replayMenu setup leaks bounds watcher).information
      (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).Choice who
      (((menu_in_replay setup leaks bounds watcher).actionRestriction
        (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).site
          who site).1)
    (extra : action ∉ Set.range
      (((menu_in_replay setup leaks bounds watcher).actionRestriction
        (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).choice who
        site.1))
    (law : PMF ((information setup leaks bounds watcher).Choice who site.1))
    (history : (information setup leaks bounds watcher).InformationHistory who site.1) :
    (((replayMenu setup leaks bounds watcher).information
      (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).runBehavioralFrom
      (Profile.update target who ((target who).commit
        (((menu_in_replay setup leaks bounds watcher).actionRestriction
          (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).site
            who site).1 action))
      (2 * horizon setup watcher + 1 - history.1.trace.length)
      (((menu_in_replay setup leaks bounds watcher).actionRestriction
        (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).history
          history.1)).map (fun final =>
        final.state.map (fun control => control.execution.application)) =
    ((information setup leaks bounds watcher).runBehavioralFrom
      (Profile.update source who ((source who).withLaw site.1 law))
      (2 * horizon setup watcher + 1 - history.1.trace.length) history.1).map
        (fun final => final.state.map (fun control => control.execution.application)) := by
  classical
  let app := application setup leaks
  let sourceMenu := menu setup leaks bounds watcher
  let targetMenu := replayMenu setup leaks bounds watcher
  let included := menu_in_replay setup leaks bounds watcher
  let initial := initialLaw setup
  let count := horizon setup watcher
  let service := scheduler setup leaks watcher
  let restriction := included.actionRestriction initial count service
  rcases site with ⟨info, occurs⟩
  have active := InformationModel.InformationSite.active
    (information setup leaks bounds watcher) ⟨info, occurs⟩ history
  have present : ∃ remaining execution,
      history.1.state = some ⟨remaining, some who, execution⟩ := by
    cases current : history.1.state with
    | none => simp only [current, ReactiveApplication.ResponseMenu.protocol,
        ReactiveApplication.actor, Option.bind_none, reduceCtorEq] at active
    | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      have actorEq : actor = some who := by
        simpa only [current, ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor,
          Option.bind_some] using active
      exact ⟨remaining, execution, by rw [actorEq]⟩
  obtain ⟨remaining, execution, current⟩ := present
  have observed : info = some (execution.recall who, execution.observe app who) := by
    have seen := history.2
    change (sourceMenu.signals initial count service).infoOf who history.1.trace = info at seen
    rw [sourceMenu.info, current] at seen
    simpa only [ReactiveApplication.observe, reduceIte] using seen.symm
  subst info
  change (targetMenu.information initial count service).Choice who
    (some (execution.recall who, execution.observe app who)) at action
  obtain ⟨response, selected, allowed, excluded⟩ :=
    included.extra_choice_response initial count service who _ _ action extra
  obtain ⟨isWatcher, packet, published, replayed⟩ :=
    replay_extra_response setup leaks bounds watcher who _ _ response allowed excluded
  subst who
  have quiet := watcher_history_silent setup leaks bounds watcher reveals observer openable
    history.1 ⟨remaining, some watcher, execution⟩ current rfl
  change app.reportFirstUnpublished (execution.recall watcher)
    (execution.observe app watcher) = PMF.pure ⟨none⟩ at quiet
  have lawSilent : law.map (fun choice => choice.1.getD ⟨none⟩) = PMF.pure ⟨none⟩ := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro physical member
    obtain ⟨choice, _supported, equal⟩ := PMF.support_map .. ▸ member
    obtain ⟨chosen, legal, selectedChoice⟩ := choice.2
    have silence : chosen = ⟨none⟩ := by
      simp only [menu, reduceIte] at legal
      change chosen ∈ (app.reportFirstUnpublished (execution.recall watcher)
        (execution.observe app watcher)).supportFinset at legal
      simpa only [quiet, FinDist.mem_supportFinset, PMF.mem_support_pure_iff _ _] using legal
    simpa only [selectedChoice, silence, Option.getD_some, Set.mem_singleton_iff]
      using equal.symm
  let native := restriction.history history.1
  have nativeState : native.state = some ⟨remaining, some watcher, execution⟩ := current
  have nativeInfo : (targetMenu.information initial count service).infoOf watcher native.trace =
      some (execution.recall watcher, execution.observe app watcher) :=
    (included.observed initial count service watcher history.1).trans history.2
  have targetLaw := local_law_at targetMenu initial count service target native watcher
    remaining execution nativeState _ nativeInfo (PMF.pure action)
  have sourceLaw := local_law_at sourceMenu initial count service source history.1 watcher
    remaining execution current _ history.2 law
  rw [PMF.pure_map, PMF.pure_bind, selected, Option.getD_some] at targetLaw
  rw [lawSilent, PMF.pure_bind] at sourceLaw
  have lengthEq : native.trace.length = history.1.trace.length := restriction.length history.1
  rw [lengthEq] at targetLaw
  have supportSilent : (⟨none⟩ : app.Action) ∈
      (sourceMenu.decodeProfile initial count service source watcher
        (execution.recall watcher) (execution.observe app watcher)).support := by
    rw [show sourceMenu.decodeProfile initial count service source watcher =
        app.reportFirstUnpublished from menu_decode_reports setup leaks bounds watcher source,
      quiet]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  obtain ⟨next, _supported, nextState⟩ := sourceMenu.response_history_exists initial count service
    source history.1 watcher remaining execution current ⟨none⟩ supportSilent
  have clean := watcher_history_clean setup leaks bounds watcher reveals observer openable
    history.1 ⟨remaining, some watcher, execution⟩ current rfl
  have selfRelated : ReplayAgreement setup leaks watcher execution execution :=
    ReplayAgreement.refl execution (fun input member _ => clean.2.2 input member)
  have related := selfRelated.respond_watcher_replay packet.id
    (List.mem_map.mpr ⟨packet, published, rfl⟩)
  rw [← replayed] at related
  have finished := replay_finish_application_law setup leaks bounds watcher reveals observer
    openable source target agrees next remaining none _ _ nextState related
  have targetMapped := congrArg (fun distribution => distribution.map
    (fun state : app.ProtocolState => state.map (fun control => control.execution.application)))
    targetLaw
  have sourceMapped := congrArg (fun distribution => distribution.map
    (fun state : app.ProtocolState => state.map (fun control => control.execution.application)))
    sourceLaw
  rw [PMF.map_comp] at targetMapped sourceMapped
  exact targetMapped.trans (finished.symm.trans sourceMapped.symm)

end Vegas
