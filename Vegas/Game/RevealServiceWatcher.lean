/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealService
import Interaction.ReactiveFiniteAssessment
import Interaction.ReactiveMenuPolicy
import GameTheoryExtensions.Analysis.Protocol.RestrictionExtension
import GameTheoryExtensions.Protocol.ContinuationHorizon
import Vegas.Pending.ReactiveAliasEquilibrium

/-! # Restoring watcher choices and raw responses in the reveal service

The watched game admits every effective ordinary response and prescribes the
watcher's silence: it only observes. If the watcher's actual utility is constant
zero,
every watched SE extends to the full bounded raw native game with identical
joint observation/net-payoff law. All games and utilities are fixed before
choosing the assessment. Silence is an equilibrium choice, not a strict
incentive or a coalition-resistance guarantee.

Source-to-watched correspondence and enforcement of ordinary deviations remain
separate obligations. This theorem supplies the last two strategic edges for
the constructed service, rather than another execution semantics.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))

open Classical in
def watchedMenu (watcher : Player) : (application setup leaks).ResponseMenu where
  actions who past view := if who = watcher then {⟨none⟩}
    else (bounds.menu (runtime setup) leaks).actions who past view
  nonempty who past view := by
    split
    · exact ⟨⟨none⟩, Finset.mem_singleton_self _⟩
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
  · cases Finset.mem_singleton.mp member
    exact silence_effective setup leaks bounds who past view
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

/-- Every watched behavioral profile keeps the watcher silent, including at
off-path local inputs. This is imposed by the actual response menu and does
not assume that players choose a particular continuation. -/
theorem watched_decode_silent (watcher : Player)
    (profile : Profile (watchedInformation setup leaks bounds watcher).behavioralSignature) :
    (watchedMenu setup leaks bounds watcher).decodeProfile (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher) profile watcher =
        (application setup leaks).silentPolicy := by
  funext past view
  apply pmf_eq_pure_of_support_subset_singleton
  intro response supported
  have allowed := (watchedMenu setup leaks bounds watcher).decode_embedPolicy_covered
    (initialLaw setup) (horizon setup watcher) (scheduler setup leaks watcher)
    watcher (profile watcher) past view response supported
  simpa only [watchedMenu, ↓reduceIte, Finset.mem_singleton, Set.mem_singleton_iff] using allowed

end Vegas
