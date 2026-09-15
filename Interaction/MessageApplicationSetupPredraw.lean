/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPredraw
import GameTheoryExtensions.Protocol.FiniteSupportPredraw

/-! # Predrawing across a finite initial execution law -/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]

/-- Total deterministic fallback used by the setup-wide predraw. -/
def focalWaitPolicy (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) :
    (app.focalInformation players environment who schedule initial).Policy () :=
  fun info => match info with
    | none => ⟨none, by simp⟩
    | some _ => ⟨some (app.invocationWait who), by simp⟩


/-- The union of the selected policy's bounded reachable information sites
over every execution in a finite initial law. -/
def setupFocalSites (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who)) :
    Finset (Option (app.InvocationSite who)) := by
  classical
  exact initials.supportFinset.biUnion fun initial =>
    InformationModel.behavioralSupportSitesFrom
      (M := app.focalInformation players environment who schedule initial)
      (fun _ => app.focalBehavioral players environment who schedule initial replacement)
      schedule.length
      (app.focalProtocol players environment who schedule initial).initHistory ()

/-- The model-independent common response draw.  It samples each site in the
setup-wide union once and uses `wait` away from that finite union. -/
def setupResponseMixture (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who)) :
    FinDist (app.InvocationSite who → app.InvocationCommand who) := by
  classical
  exact FinDist.runDependent replacement
    (List.filterMap id
      (app.setupFocalSites players environment who schedule initials replacement).toList)
    (fun _ => app.invocationWait who)

theorem focalSupportSites_subset_setupFocalSites
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who))
    (initial : app.PolicyExecution) (hinitial : initial ∈ initials.support) :
    InformationModel.behavioralSupportSitesFrom
        (M := app.focalInformation players environment who schedule initial)
        (fun _ => app.focalBehavioral players environment who schedule initial replacement)
        schedule.length
        (app.focalProtocol players environment who schedule initial).initHistory () ⊆
      app.setupFocalSites players environment who schedule initials replacement := by
  classical
  intro info hinfo
  rw [setupFocalSites]
  exact Finset.mem_biUnion.mpr
    ⟨initial, FinDist.mem_supportFinset.mpr hinitial, hinfo⟩

/-- On every history in the bounded behavioral support, restricting to the
setup-wide union of sites leaves the selected behavioral kernel unchanged. -/
theorem focal_restrictProfile_agrees_on_support
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who))
    (initial : app.PolicyExecution) (hinitial : initial ∈ initials.support) :
    let M := app.focalInformation players environment who schedule initial
    let start := (app.focalProtocol players environment who schedule initial).initHistory
    let policy : (i : Unit) → M.BehavioralPolicy i := fun _ =>
      app.focalBehavioral players environment who schedule initial replacement
    let sites : (i : Unit) → Finset (M.InfoState i) := fun _ =>
      app.setupFocalSites players environment who schedule initials replacement
    let fallback : (i : Unit) → M.Policy i := fun _ =>
      app.focalWaitPolicy players environment who schedule initial
    ∀ elapsed, elapsed ≤ schedule.length → ∀ later,
      later ∈ (M.runBehavioralFrom policy elapsed start).support →
      ¬ (app.focalProtocol players environment who schedule initial).terminal later.state →
      ∀ i, policy i (M.infoOf i later.trace) =
        InformationModel.restrictProfile M policy sites fallback i (M.infoOf i later.trace) := by
  classical
  dsimp only
  intro elapsed helapsed later hlater _ i
  cases i
  apply Eq.symm
  apply InformationModel.restrictProfile_apply_of_mem
  apply app.focalSupportSites_subset_setupFocalSites players environment who schedule initials
    replacement initial hinitial
  exact InformationModel.mem_behavioralSupportSitesFrom
    (M := app.focalInformation players environment who schedule initial)
    (fun _ => app.focalBehavioral players environment who schedule initial replacement)
    schedule.length elapsed helapsed
    (app.focalProtocol players environment who schedule initial).initHistory later hlater ()

theorem focal_runMixedWithin_setup_eq_runBehavioral
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who))
    (initial : app.PolicyExecution) (hinitial : initial ∈ initials.support) :
    let M := app.focalInformation players environment who schedule initial
    let start := (app.focalProtocol players environment who schedule initial).initHistory
    let policy : (i : Unit) → M.BehavioralPolicy i := fun _ =>
      app.focalBehavioral players environment who schedule initial replacement
    let sites : (i : Unit) → Finset (M.InfoState i) := fun _ =>
      app.setupFocalSites players environment who schedule initials replacement
    let fallback : (i : Unit) → M.Policy i := fun _ =>
      app.focalWaitPolicy players environment who schedule initial
    M.runMixedFrom (fun i => (policy i).toMixedWithin (sites i) (fallback i))
        schedule.length start = M.runBehavioralFrom policy schedule.length start := by
  classical
  dsimp only
  let M := app.focalInformation players environment who schedule initial
  let start := (app.focalProtocol players environment who schedule initial).initHistory
  let policy : (i : Unit) → M.BehavioralPolicy i := fun _ =>
    app.focalBehavioral players environment who schedule initial replacement
  let sites : (i : Unit) → Finset (M.InfoState i) := fun _ =>
    app.setupFocalSites players environment who schedule initials replacement
  let fallback : (i : Unit) → M.Policy i := fun _ =>
    app.focalWaitPolicy players environment who schedule initial
  calc
    _ = M.runBehavioralFrom (InformationModel.restrictProfile M policy sites fallback)
          schedule.length start :=
      M.runMixedFrom_restrictRandomization
        (app.focal_actsOnceWhereItMatters players environment who schedule initial)
        policy sites fallback schedule.length start
    _ = _ := (M.runBehavioralFrom_congr_on_support schedule.length start
      (app.focal_restrictProfile_agrees_on_support players environment who schedule initials
        replacement initial hinitial)).symm

end Interaction.MessageApplication
