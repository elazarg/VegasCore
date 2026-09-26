/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceClock
import Interaction.ReactiveFiniteAssessment
import Interaction.ReactiveMenuPolicy
import GameTheoryExtensions.Analysis.Protocol.RestrictionExtension
import GameTheoryExtensions.Protocol.ContinuationHorizon
import Vegas.Pending.ReactiveAliasEquilibrium

/-! # Restoring watcher choices and raw responses in the reveal service

The watched game admits every effective ordinary response and prescribes the
existing reporting policy. If the watcher's actual utility is constant zero,
every watched SE extends to the full bounded raw native game with identical
joint observation/net-payoff law. All games and utilities are fixed before
choosing the assessment. Reporting is an equilibrium choice, not a strict
incentive or a coalition-resistance guarantee.

Source-to-watched correspondence and enforcement of ordinary deviations remain
separate obligations. This theorem supplies the last two strategic edges for
the constructed service, rather than another execution semantics.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open Interaction EventGraphRuntime GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))

open Classical in
def watchedMenu (watcher : Player) : (application setup leaks).ResponseMenu where
  actions who past view := if who = watcher then
      ((application setup leaks).reportFirstUnpublished past view).supportFinset
    else (bounds.menu (runtime setup) leaks).actions who past view
  nonempty who past view := by
    split
    · obtain ⟨response, supported⟩ :=
        ((application setup leaks).reportFirstUnpublished past view).support_nonempty
      exact ⟨response, FinDist.mem_supportFinset.mpr supported⟩
    · exact (bounds.menu (runtime setup) leaks).nonempty who past view

theorem menu_in_watched (watcher : Player) :
    (menu setup leaks bounds watcher).IncludedIn (watchedMenu setup leaks bounds watcher) := by
  intro who past view
  simp only [menu, watchedMenu]
  split
  · exact fun _ member => member
  · exact ordinary_effective setup leaks bounds who past view

theorem watched_in_effective (watcher : Player) :
    (watchedMenu setup leaks bounds watcher).IncludedIn (bounds.menu (runtime setup) leaks) := by
  intro who past view response member
  change response ∈ (if who = watcher then _ else _) at member
  split at member
  · exact report_effective setup leaks bounds who past view response
      (FinDist.mem_supportFinset.mp member)
  · exact member

abbrev watchedInformation (watcher : Player) :=
  (watchedMenu setup leaks bounds watcher).information (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)

abbrev effectiveInformation (watcher : Player) :=
  (bounds.menu (runtime setup) leaks).information (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)

abbrev rawInformation (watcher : Player) :=
  (bounds.rawMenu (runtime setup) leaks).information (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)

def ordinaryRestriction (watcher : Player) :
    (information setup leaks bounds watcher).ActionRestriction
      (watchedInformation setup leaks bounds watcher) :=
  (menu_in_watched setup leaks bounds watcher).actionRestriction (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher)

def watcherRestriction (watcher : Player) :
    (watchedInformation setup leaks bounds watcher).ActionRestriction
      (effectiveInformation setup leaks bounds watcher) :=
  (watched_in_effective setup leaks bounds watcher).actionRestriction (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher)

theorem ordinary_choice_surjective (watcher who : Player) (ordinary : who ≠ watcher)
    (info : (application setup leaks).Info) :
    Function.Surjective ((watcherRestriction setup leaks bounds watcher).choice who info) := by
  intro action
  have member := action.2
  refine ⟨⟨action.1, ?_⟩, ?_⟩
  · cases info with
    | none => exact member
    | some data =>
        obtain ⟨response, allowed, same⟩ := member
        exact ⟨response, by simpa only [watchedMenu, ordinary, ↓reduceIte] using allowed, same⟩
  · exact Subtype.ext rfl

/-- Every watched behavioral profile executes the specified report response,
including at off-path local inputs. This is imposed by the actual response
menu and does not assume that players choose a particular continuation. -/
theorem watched_decode_reports (watcher : Player)
    (profile : Profile (watchedInformation setup leaks bounds watcher).behavioralSignature) :
    (watchedMenu setup leaks bounds watcher).decodeProfile (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher) profile watcher =
        (application setup leaks).reportFirstUnpublished := by
  funext past view
  have deterministic : ∃ response,
      (application setup leaks).reportFirstUnpublished past view = FinDist.pure response := by
    unfold ReactiveApplication.reportFirstUnpublished
    split <;> exact ⟨_, rfl⟩
  obtain ⟨reported, law⟩ := deterministic
  rw [law]
  apply FinDist.eq_pure_of_support_subset_singleton
  intro response supported
  have allowed := (watchedMenu setup leaks bounds watcher).decode_embedPolicy_covered
    (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)
    watcher (profile watcher) past view response supported
  simpa only [watchedMenu, ↓reduceIte, law, FinDist.mem_supportFinset,
    FinDist.mem_support_pure, Set.mem_singleton_iff] using allowed

/-- Every equilibrium with prescribed reporting extends to the full bounded
raw game of this service. Observations and net utilities ignore only the proved
private submission normalization; public traffic and replay effects are kept.
The construction supplies consistent off-path play rather than assuming it. -/
theorem watched_raw_equilibrium_extends (watcher : Player)
    (reveals : setup.program.RevealOnly)
    (separate : ∀ event, (graph setup).actor? event ≠ some watcher)
    {Observation : Type} (observe : (application setup leaks).ProtocolState → Observation)
    (observationInvariant : ∀ state,
      observe (((runtime setup).reactiveNormalization leaks).state state) = observe state)
    (utility : (application setup leaks).ProtocolState → Player → ℝ)
    (utilityInvariant : ∀ state,
      utility (((runtime setup).reactiveNormalization leaks).state state) = utility state)
    (indifferent : ∀ state, utility state watcher = 0)
    (source : (watchedInformation setup leaks bounds watcher).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor
      ((watchedMenu setup leaks bounds watcher).decisionInformationAntichain (initialLaw setup)
        (horizon setup watcher) (scheduler setup leaks watcher))
      (fun who site => source.continuationContext site
        (fun history => utility history.state who) (2 * horizon setup watcher + 1))) :
    ∃ target : (rawInformation setup leaks bounds watcher).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        ((bounds.rawMenu (runtime setup) leaks).decisionInformationAntichain (initialLaw setup)
          (horizon setup watcher) (scheduler setup leaks watcher))
        (fun who site => target.continuationContext site
          (fun history => utility history.state who) (2 * horizon setup watcher + 1)) ∧
      ((rawInformation setup leaks bounds watcher).runBehavioral target.strategy
        (2 * horizon setup watcher + 1)).map
          (fun history => (observe history.state, utility history.state)) =
        ((watchedInformation setup leaks bounds watcher).runBehavioral source.strategy
          (2 * horizon setup watcher + 1)).map
            (fun history => (observe history.state, utility history.state)) := by
  classical
  let initial := initialLaw setup
  let count := horizon setup watcher
  let service := scheduler setup leaks watcher
  let watched := watchedMenu setup leaks bounds watcher
  let effective := bounds.menu (runtime setup) leaks
  let restriction := watcherRestriction setup leaks bounds watcher
  let depth (who : Player)
      (site : (effectiveInformation setup leaks bounds watcher).InformationSite who) :=
    decisionDepth setup leaks watcher who site.1
  have clock := menu_common_decision_depth setup leaks effective watcher reveals separate
  have sourceClock := menu_common_decision_depth setup leaks watched watcher reveals separate
  have remaining := (source.sequentialEquilibrium_remaining_iff
    (watchedInformation setup leaks bounds watcher)
    (watched.decisionInformationAntichain initial count service) (2 * count + 1)
    (watched.bounded initial count service)
    (fun who site => decisionDepth setup leaks watcher who site.1) sourceClock
    (fun who history => utility history.state who)).mpr equilibrium
  have unchangedOrIndifferent (who : Player) :
      (∀ info, Function.Surjective (restriction.choice who info)) ∨
        ∃ constant, ∀ history : (effective.protocol initial count service).History,
          utility history.state who = constant := by
    by_cases same : who = watcher
    · subst who
      exact Or.inr ⟨0, fun history => indifferent history.state⟩
    · exact Or.inl (ordinary_choice_surjective setup leaks bounds watcher who same)
  obtain ⟨normalized, normalizedSE, _agrees, _beliefs, historyLaw, _joint, _terminal⟩ :=
    restriction.sequential_equilibrium_extends_of_indifference
      (watched.decisionInformationAntichain initial count service)
      (effective.uniformAssessment initial count service)
      (effective.uniform_fullyMixed initial count service)
      (effective.decisionRecall initial count service) (2 * count + 1)
      (effective.bounded initial count service) depth clock
      (fun history who => utility history.state who)
      (fun history who => utility history.state who) (fun _ _ => rfl)
      unchangedOrIndifferent source remaining
  have full := (normalized.sequentialEquilibrium_remaining_iff
    (effectiveInformation setup leaks bounds watcher)
    (effective.decisionRecall initial count service).antichain (2 * count + 1)
    (effective.bounded initial count service) depth clock
    (fun who history => utility history.state who)).mp normalizedSE
  obtain ⟨raw, _strategy, rawSE, _beliefs, projected⟩ :=
    bounds.exists_canonicalRaw_sequentialEquilibrium (runtime setup) leaks initial count service
      normalized (fun who state => utility state who) full
  refine ⟨raw, ?_, ?_⟩
  · simpa only [utilityInvariant] using rawSE
  · have law := congrArg (FinDist.map (fun state => (observe state, utility state))) projected
    simp only [FinDist.map_comp, Function.comp_def, observationInvariant, utilityInvariant] at law
    rw [law, ← historyLaw, FinDist.map_comp]
    rfl

end Vegas.SourceProgram.RevealService
