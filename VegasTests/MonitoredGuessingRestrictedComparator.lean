/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.MonitoredGuessingRestrictedAliceSupport
import VegasTests.MonitoredGuessingRestrictedFinalComparison
import Interaction.ReactiveMenuPolicy

/-! # Legal local comparators for the ordinary-player extension

The comparator is fixed by the player's information and proposed response.
Bob and early Alice are compared with silence. Final Alice uses the checked
result-preserving comparator. Watcher has no added response on this edge.
The inequalities for these choices are separate operational obligations.
-/

noncomputable section

namespace VegasTests.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

def comparatorResponse (who : Player) (information : nativeApp.Info)
    (response : nativeApp.Action) : nativeApp.Action :=
  if who = watcher then
    information.elim nativeSilent (fun pair => nativeWatcherResponse pair.2)
  else if who = alice ∧
      information.bind (fun pair => pair.2.application.publicView.serviceGrant) =
        some alicePublication then finalComparator information response
  else nativeSilent

theorem comparatorResponse_legal (who : Player)
    (site : restrictedModel.InformationSite who) (response : nativeApp.Action) :
    some (comparatorResponse who site.1 response) ∈ restrictedModel.menu who site.1 := by
  classical
  by_cases watching : who = watcher
  · subst who
    obtain ⟨_, _, chosen, allowed⟩ := site.2
    cases observed : site.1 with
    | none => rw [observed] at allowed; cases allowed
    | some data =>
        change ∃ action ∈ restrictedMenu.actions watcher data.1 data.2,
          some (comparatorResponse watcher (some data) response) = some action
        refine ⟨nativeWatcherResponse data.2, ?_, rfl⟩
        simp [restrictedMenu]
  · by_cases sender : who = alice
    · subst who
      rcases alice_site_cases site with ⟨bit, observed⟩ | ⟨bit, guess, observed⟩
      · rw [observed]
        change ∃ action ∈ restrictedMenu.actions alice []
            ((aliceActivated bit).observe nativeApp alice),
          some (comparatorResponse alice _ response) = some action
        refine ⟨nativeSilent, ?_, ?_⟩
        · simp only [restrictedMenu, watching, ↓reduceIte]
          exact silent_ordinary alice _ _
        · simp only [comparatorResponse, watching, ↓reduceIte, Option.bind_some]
          rfl
      · rw [observed]
        change ∃ action ∈ restrictedMenu.actions alice ((beforeAlice bit guess).recall alice)
            ((beforeAlice bit guess).observe nativeApp alice),
          some (comparatorResponse alice (aliceInput bit guess) response) = some action
        exact ⟨finalComparator (aliceInput bit guess) response,
          final_comparator_available bit guess response, rfl⟩
    · obtain ⟨_, _, chosen, allowed⟩ := site.2
      cases observed : site.1 with
      | none => rw [observed] at allowed; cases allowed
      | some data =>
          change ∃ action ∈ restrictedMenu.actions who data.1 data.2,
            some (comparatorResponse who (some data) response) = some action
          refine ⟨nativeSilent, ?_, ?_⟩
          · simp only [restrictedMenu, watching, ↓reduceIte]
            exact silent_ordinary who _ _
          · simp only [comparatorResponse, watching, sender, false_and, ↓reduceIte]

def ordinaryComparator (who : Player) (site : restrictedModel.InformationSite who)
    (action : watchedModel.Choice who (ordinaryRestriction.site who site).1) :
    FinDist (restrictedModel.Choice who site.1) :=
  FinDist.pure ⟨some (comparatorResponse who site.1 (action.1.getD nativeSilent)),
    comparatorResponse_legal who site _⟩

theorem watcher_choice_surjective (info : nativeApp.Info) :
    Function.Surjective (ordinaryRestriction.choice watcher info) := by
  intro action
  have member := action.2
  refine ⟨⟨action.1, ?_⟩, Subtype.ext rfl⟩
  cases info with
  | none => exact member
  | some data =>
      obtain ⟨response, allowed, same⟩ := member
      exact ⟨response, by simpa only [watchedMenu, restrictedMenu, ↓reduceIte] using allowed,
        same⟩

theorem watched_watcher_policy (profile : Profile watchedModel.behavioralSignature) :
    watchedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler profile watcher =
      nativeWatcherPolicy := by
  funext past view
  change _ = FinDist.pure (nativeWatcherResponse view)
  apply FinDist.eq_pure_of_support_subset_singleton
  intro response supported
  have member := watchedMenu.decode_embedPolicy_covered nativeInitialLaw nativeHorizon
    nativeScheduler watcher (profile watcher) past view response supported
  simpa only [watchedMenu, ↓reduceIte, Finset.mem_singleton, Set.mem_singleton_iff] using member

end VegasTests.MonitoredGuessing.Restricted
