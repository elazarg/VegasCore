/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageApplicationPredrawTransport

/-! # Support guarantees for setup-wide response predraws -/

noncomputable section
namespace Interaction.MessageApplication

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]

/-- Every coordinate selected by the setup-wide site union is drawn from its
original behavioral command law. This is the support fact needed to retain
mandatory commands when a response function is later used as a pure policy. -/
theorem setupResponseMixture_apply_mem_support
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who))
    (response : app.InvocationSite who → app.InvocationCommand who)
    (supported : response ∈
      (app.setupResponseMixture players environment who schedule initials replacement).support)
    (site : app.InvocationSite who)
    (selected : some site ∈
      app.setupFocalSites players environment who schedule initials replacement) :
    response site ∈ (replacement site).support := by
  classical
  let sites := app.setupFocalSites players environment who schedule initials replacement
  have siteMem : site ∈ List.filterMap id sites.toList := by
    simp only [List.mem_filterMap]
    exact ⟨some site, Finset.mem_toList.mpr selected, rfl⟩
  unfold setupResponseMixture at supported
  have indicesNodup : (List.filterMap id sites.toList).Nodup := by
    apply List.Nodup.filterMap _ sites.nodup_toList
    intro first second value hfirst hsecond
    simpa using hfirst.trans hsecond.symm
  have orderEq : FinDist.runDependent replacement (List.filterMap id sites.toList)
        (fun _ => app.invocationWait who) =
      FinDist.runDependent replacement
        (List.filterMap id sites.toList).toFinset.toList
        (fun _ => app.invocationWait who) := by
    apply FinDist.runDependent_eq_of_toFinset_eq replacement
    · exact indicesNodup
    · exact (List.filterMap id sites.toList).toFinset.nodup_toList
    · simp
  have factored := FinDist.runDependent_factor_of_mem replacement
    (List.filterMap id sites.toList).toFinset (fun _ => app.invocationWait who) site
    (List.mem_toFinset.mpr siteMem)
  rw [orderEq, factored, FinDist.support_map] at supported
  obtain ⟨pair, pairSupported, responseEq⟩ := supported
  simp only [FinDist.product, FinDist.support_bind, Set.mem_iUnion,
    FinDist.support_map] at pairSupported
  obtain ⟨value, valueSupported, assignment, _, pairEq⟩ := pairSupported
  rw [← pairEq] at responseEq
  have atSite := congrFun responseEq site
  simp only [FinDist.DependentAssignment.setOne_apply_self] at atSite
  simpa [atSite] using valueSupported

/-- Every history reached by a supported pure setup response is also reached
by the original behavioral focal policy. The mixed-profile equality supplies
this support inclusion without reconstructing native policy traces. -/
theorem focal_pureResponse_support_subset
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who))
    (response : app.InvocationSite who → app.InvocationCommand who)
    (supported : response ∈
      (app.setupResponseMixture players environment who schedule initials replacement).support)
    (initial : app.PolicyExecution) (hinitial : initial ∈ initials.support)
    (fuel : Nat) (hfuel : fuel ≤ schedule.length) :
    let M := app.focalInformation players environment who schedule initial
    let start := (app.focalProtocol players environment who schedule initial).initHistory
    let purePolicy : (i : Unit) → M.BehavioralPolicy i := fun _ =>
      app.focalBehavioral players environment who schedule initial
        (fun site => FinDist.pure (response site))
    let original : (i : Unit) → M.BehavioralPolicy i := fun _ =>
      app.focalBehavioral players environment who schedule initial replacement
    ∀ later, later ∈ (M.runBehavioralFrom purePolicy fuel start).support →
      later ∈ (M.runBehavioralFrom original fuel start).support := by
  classical
  dsimp only
  let M := app.focalInformation players environment who schedule initial
  let original : (i : Unit) → M.BehavioralPolicy i := fun _ =>
    app.focalBehavioral players environment who schedule initial replacement
  let sites : (i : Unit) → Finset (M.InfoState i) := fun _ =>
    app.setupFocalSites players environment who schedule initials replacement
  let fallback : (i : Unit) → M.Policy i := fun _ =>
    app.focalWaitPolicy players environment who schedule initial
  rw [app.setupResponseMixture_eq_focalMixed players environment who schedule initials
    replacement initial, FinDist.support_map] at supported
  obtain ⟨pureProfile, pureProfileSupported, responseEq⟩ := supported
  let readResponse (site : app.InvocationSite who) : app.InvocationCommand who :=
    ((pureProfile () (some site)).1).getD (app.invocationWait who)
  have responseRead : response = readResponse := responseEq.symm
  have hresponse : (fun site => FinDist.pure (response site)) =
      app.focalPolicyOfPure players environment who schedule initial (pureProfile ()) := by
    rw [responseRead]
    rfl
  have policyEq : (fun _ : Unit => app.focalBehavioral players environment who schedule initial
        (fun site => FinDist.pure (response site))) =
      fun i => (pureProfile i).toBehavioral := by
    funext i
    cases i
    rw [hresponse]
    exact app.focalBehavioral_focalPolicyOfPure players environment who schedule initial
      (pureProfile ())
  intro later laterSupported
  rw [policyEq, M.runBehavioralFrom_toBehavioral] at laterSupported
  have mixedSupported : later ∈
      (M.runMixedFrom (fun i => (original i).toMixedWithin (sites i) (fallback i))
        fuel (app.focalProtocol players environment who schedule initial).initHistory).support := by
    rw [InformationModel.runMixedFrom, FinDist.support_bind]
    exact Set.mem_iUnion₂.mpr ⟨pureProfile, pureProfileSupported, laterSupported⟩
  rw [app.focal_runMixedWithin_setup_eq_runBehavioral players environment who schedule initials
    replacement initial hinitial fuel hfuel] at mixedSupported
  exact mixedSupported

/-- Every nonterminal information state reached by a supported pure response
belongs to the common setup-wide site union. -/
theorem focal_pureResponse_info_mem_setupFocalSites
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who))
    (response : app.InvocationSite who → app.InvocationCommand who)
    (supported : response ∈
      (app.setupResponseMixture players environment who schedule initials replacement).support)
    (initial : app.PolicyExecution) (hinitial : initial ∈ initials.support)
    (elapsed : Nat) (helapsed : elapsed ≤ schedule.length)
    (later : (app.focalProtocol players environment who schedule initial).History)
    (laterSupported : later ∈
      ((app.focalInformation players environment who schedule initial).runBehavioralFrom
        (fun _ => app.focalBehavioral players environment who schedule initial
          (fun site => FinDist.pure (response site))) elapsed
        (app.focalProtocol players environment who schedule initial).initHistory).support) :
    (app.focalInformation players environment who schedule initial).infoOf () later.trace ∈
      app.setupFocalSites players environment who schedule initials replacement := by
  apply app.focalSupportSites_subset_setupFocalSites players environment who schedule initials
    replacement initial hinitial
  apply InformationModel.mem_behavioralSupportSitesFrom
    (M := app.focalInformation players environment who schedule initial)
    (fun _ => app.focalBehavioral players environment who schedule initial replacement)
    schedule.length elapsed helapsed
    (app.focalProtocol players environment who schedule initial).initHistory later
  exact app.focal_pureResponse_support_subset players environment who schedule initials
    replacement response supported initial hinitial elapsed helapsed later laterSupported

end Interaction.MessageApplication
