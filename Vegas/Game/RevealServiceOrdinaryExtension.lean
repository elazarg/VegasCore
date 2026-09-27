/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceClean
import Vegas.Game.RevealServiceOwnerCollection

/-! # Restoring every ordinary response in the monitored reveal service

The actual passive observation rule supplies a per-packet sampling bound.
The service's checkpoint classification and reporting block turn that bound
into persistent departure evidence, uniformly over all continuation policies.
A fixed whole-payoff-range deposit therefore extends every retained sequential
equilibrium. Source withholding and spent public replays remain legal.

The subsequent watcher and private-alias extensions recover every bounded raw
response at the existing service opportunities. The reporting player must have
zero utility for that final composition. Collection is the explicit net-utility
interpretation; these theorems do not implement an escrow contract.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)

/-- C and W prescribe the same reporter menu, including at off-path inputs. -/
theorem watcher_choice_surjective (info : (application setup leaks).Info) :
    Function.Surjective ((ordinaryRestriction setup leaks bounds watcher).choice watcher info) :=
    by
  intro action
  have member := action.2
  refine ⟨⟨action.1, ?_⟩, Subtype.ext rfl⟩
  cases info with
  | none => exact member
  | some data =>
      obtain ⟨response, allowed, same⟩ := member
      exact ⟨response, by simpa only [watchedMenu, menu, ↓reduceIte] using allowed, same⟩

variable (reveals : setup.program.RevealOnly)
  (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
  (base : (application setup leaks).ProtocolState → Player → ℝ)
  (deposit lower upper probability : Player → ℝ)
  (nonnegative : ∀ who, 0 ≤ deposit who)
  (below : ∀ (history : (protocol setup leaks bounds watcher).History) who,
    lower who ≤ base history.state who)
  (above : ∀ (history : ((watchedMenu setup leaks bounds watcher).protocol
    (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)).History) who,
      base history.state who ≤ upper who)
  (sufficient : ∀ who, who ≠ watcher → upper who - lower who ≤ probability who * deposit who)
  (sampling : ∀ owner, owner ≠ watcher →
    ∀ pending (message : Message Player (WitnessedPacket (graph setup))), message ∈ pending →
      message.id.1 = owner → probability owner ≤ (leaks watcher pending).probOf
        {selected | message.id ∈ selected})

include reveals observer openable nonnegative below above sufficient sampling in
/-- Fixed utility bounds, deposits and observation coverage suffice for every
retained SE. The conclusion includes its policies and beliefs at retained
information sets and its full initialized history/net-payoff law. -/
theorem ordinary_equilibrium_extends
    (source : (information setup leaks bounds watcher).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((menu setup leaks bounds watcher).decisionInformationAntichain (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher))
      (fun who site => source.continuationContext site
        (fun history => netUtility setup leaks watcher base deposit history.state who)
        (2 * horizon setup watcher + 1))) :
    ∃ target : (watchedInformation setup leaks bounds watcher).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((watchedMenu setup leaks bounds watcher).decisionInformationAntichain (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher))
        (fun who site => target.continuationContext site
          (fun history => netUtility setup leaks watcher base deposit history.state who)
          (2 * horizon setup watcher + 1)) ∧
      (ordinaryRestriction setup leaks bounds watcher).ExtendsProfile
        source.strategy target.strategy ∧
      (∀ who site, target.belief who ((ordinaryRestriction setup leaks bounds watcher).site
        who site) = (source.belief who site).map
          ((ordinaryRestriction setup leaks bounds watcher).informationHistory who site)) ∧
      ((information setup leaks bounds watcher).runBehavioral source.strategy
        (2 * horizon setup watcher + 1)).map
          (ordinaryRestriction setup leaks bounds watcher).history =
        (watchedInformation setup leaks bounds watcher).runBehavioral target.strategy
          (2 * horizon setup watcher + 1) ∧
      ((information setup leaks bounds watcher).runBehavioral source.strategy
        (2 * horizon setup watcher + 1)).map (fun history =>
          ((ordinaryRestriction setup leaks bounds watcher).history history,
            netUtility setup leaks watcher base deposit history.state)) =
        ((watchedInformation setup leaks bounds watcher).runBehavioral target.strategy
          (2 * horizon setup watcher + 1)).map (fun history =>
            (history, netUtility setup leaks watcher base deposit history.state)) := by
  classical
  let initial := initialLaw setup
  let count := horizon setup watcher
  let service := scheduler setup leaks watcher
  let retained := menu setup leaks bounds watcher
  let watched := watchedMenu setup leaks bounds watcher
  let restriction := ordinaryRestriction setup leaks bounds watcher
  let depth (who : Player)
      (site : (watchedInformation setup leaks bounds watcher).InformationSite who) :=
    decisionDepth setup leaks watcher who site.1
  let utility := netUtility setup leaks watcher base deposit
  have clock := menu_common_decision_depth setup leaks watched watcher reveals observer
  have sourceClock := menu_common_decision_depth setup leaks retained watcher reveals observer
  have sourceRemaining := (source.sequentialEquilibrium_remaining_iff
    (information setup leaks bounds watcher)
    (retained.decisionInformationAntichain initial count service) (2 * count + 1)
    (retained.bounded initial count service)
    (fun who site => decisionDepth setup leaks watcher who site.1) sourceClock
    (fun who history => utility history.state who)).mpr equilibrium
  let comparator (who : Player)
      (site : (information setup leaks bounds watcher).InformationSite who)
      (_ : (watchedInformation setup leaks bounds watcher).Choice who
        (restriction.site who site).1) :
      FinDist ((information setup leaks bounds watcher).Choice who site.1) :=
    FinDist.pure ⟨some site.2.choose_spec.2.choose, site.2.choose_spec.2.choose_spec⟩
  have comparison : ∀
      (sourceProfile : Profile (information setup leaks bounds watcher).behavioralSignature)
      (targetProfile : Profile (watchedInformation setup leaks bounds watcher).behavioralSignature),
      restriction.ExtendsProfile sourceProfile targetProfile →
      ∀ who (site : (information setup leaks bounds watcher).InformationSite who)
        (action : (watchedInformation setup leaks bounds watcher).Choice who
          (restriction.site who site).1),
        action ∉ Set.range (restriction.choice who site.1) →
        ∀ history : (information setup leaks bounds watcher).InformationHistory who site.1,
          ((watchedInformation setup leaks bounds watcher).runBehavioralFrom
            (Profile.update targetProfile who
              ((targetProfile who).commit (restriction.site who site).1 action))
            (2 * count + 1 - depth who (restriction.site who site))
            (restriction.history history.1)).expect (fun final => utility final.state who) ≤
          ((information setup leaks bounds watcher).runBehavioralFrom
            (Profile.update sourceProfile who
              ((sourceProfile who).withLaw site.1 (comparator who site action)))
            (2 * count + 1 - depth who (restriction.site who site)) history.1).expect
              (fun final => utility final.state who) := by
    intro sourceProfile targetProfile _paired who site action extra history
    by_cases isWatcher : who = watcher
    · subst who
      exact (extra (watcher_choice_surjective setup leaks bounds watcher site.1 action)).elim
    let fuel := 2 * count + 1 - depth who (restriction.site who site)
    let legalProfile := Profile.update sourceProfile who
      ((sourceProfile who).withLaw site.1 (comparator who site action))
    let targetProfile' := Profile.update targetProfile who
      ((targetProfile who).commit (restriction.site who site).1 action)
    let legalLaw := (information setup leaks bounds watcher).runBehavioralFrom legalProfile
      fuel history.1
    let targetLaw := (watchedInformation setup leaks bounds watcher).runBehavioralFrom
      targetProfile' fuel (restriction.history history.1)
    have enough : 2 * horizon setup watcher + 1 - history.1.trace.length ≤ fuel := by
      rw [sourceClock who site history]
      exact Nat.le_refl _
    have collected := owner_extra_collection setup leaks bounds watcher reveals observer openable
      targetProfile who isWatcher site action extra history probability sampling fuel enough
    have clean : ∀ final ∈ legalLaw.support, ¬ departureAtState setup leaks who final.state := by
      intro final supported
      exact continuation_clean setup leaks bounds watcher reveals observer openable
        legalProfile history.1 final fuel enough supported who
    have compared := netUtility_comparison setup leaks watcher who isWatcher base deposit
      (nonnegative who) (targetLaw.map History.state) (legalLaw.map History.state)
      (lower who) (upper who) (probability who)
      (by
        intro final supported
        obtain ⟨reached, _, rfl⟩ := FinDist.support_map .. ▸ supported
        exact above reached who)
      (by
        intro final supported
        obtain ⟨reached, _, rfl⟩ := FinDist.support_map .. ▸ supported
        exact below reached who)
      (by
        intro final supported
        obtain ⟨reached, member, rfl⟩ := FinDist.support_map .. ▸ supported
        exact clean reached member)
      (by rw [FinDist.probOf_map]; exact collected) (sufficient who isWatcher)
    simpa only [FinDist.expect_map] using compared
  obtain ⟨target, targetRemaining, agrees, beliefs, historyLaw, joint, _terminal⟩ :=
    restriction.sequential_equilibrium_extends_of_comparator
      (retained.decisionInformationAntichain initial count service)
      (watched.uniformAssessment initial count service)
      (watched.uniform_fullyMixed initial count service)
      (watched.decisionRecall initial count service) (2 * count + 1)
      (watched.bounded initial count service) depth clock
      (fun history who => utility history.state who)
      (fun history who => utility history.state who) (fun _ _ => rfl)
      comparator comparison source sourceRemaining
  have targetFull := (target.sequentialEquilibrium_remaining_iff
    (watchedInformation setup leaks bounds watcher)
    (watched.decisionRecall initial count service).antichain (2 * count + 1)
    (watched.bounded initial count service) depth clock
    (fun who history => utility history.state who)).mp targetRemaining
  exact ⟨target, targetFull, agrees, beliefs, historyLaw, joint⟩

include reveals observer openable nonnegative below above sufficient sampling in
/-- The composed extension restores every bounded raw response of the same
service. Source policies may randomize, withhold, or replay public envelopes;
the target construction supplies consistent rational off-path play. -/
theorem ordinary_raw_equilibrium_extends
    {Observation : Type} (observe : (application setup leaks).ProtocolState → Observation)
    (observationInvariant : ∀ state,
      observe (((runtime setup).reactiveNormalization leaks).state state) = observe state)
    (baseInvariant : ∀ state,
      base (((runtime setup).reactiveNormalization leaks).state state) = base state)
    (indifferent : ∀ state, base state watcher = 0)
    (source : (information setup leaks bounds watcher).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((menu setup leaks bounds watcher).decisionInformationAntichain (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher))
      (fun who site => source.continuationContext site
        (fun history => netUtility setup leaks watcher base deposit history.state who)
        (2 * horizon setup watcher + 1))) :
    ∃ target : (rawInformation setup leaks bounds watcher).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((bounds.rawMenu (runtime setup) leaks).decisionInformationAntichain (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher))
        (fun who site => target.continuationContext site
          (fun history => netUtility setup leaks watcher base deposit history.state who)
          (2 * horizon setup watcher + 1)) ∧
      ((rawInformation setup leaks bounds watcher).runBehavioral target.strategy
        (2 * horizon setup watcher + 1)).map (fun history =>
          (observe history.state, netUtility setup leaks watcher base deposit history.state)) =
        ((information setup leaks bounds watcher).runBehavioral source.strategy
          (2 * horizon setup watcher + 1)).map (fun history =>
            (observe history.state, netUtility setup leaks watcher base deposit history.state)) :=
    by
  classical
  obtain ⟨watched, watchedSE, _agrees, _beliefs, historyLaw, _joint⟩ :=
    ordinary_equilibrium_extends setup leaks bounds watcher reveals observer openable base
      deposit lower upper probability nonnegative below above sufficient sampling source equilibrium
  obtain ⟨target, targetSE, joint⟩ := watched_raw_equilibrium_extends setup leaks bounds watcher
    reveals observer observe observationInvariant (netUtility setup leaks watcher base deposit)
    (netUtility_normalization setup leaks watcher base deposit baseInvariant)
    (fun state => (netUtility_watcher setup leaks watcher base deposit state).trans
      (indifferent state)) watched watchedSE
  refine ⟨target, targetSE, ?_⟩
  rw [joint, ← historyLaw, FinDist.map_comp]
  rfl

end Vegas.SourceProgram.RevealService
