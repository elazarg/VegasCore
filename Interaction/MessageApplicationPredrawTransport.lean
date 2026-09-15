/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationSetupPredraw

/-! # Transporting setup-wide predraws to focal models -/

noncomputable section
namespace Interaction.MessageApplication

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]

/-- The setup-wide command draw is exactly the finite focal-model predraw when
the latter uses the canonical wait policy outside the setup-wide sites. -/
theorem setupResponseMixture_eq_focalMixed
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who))
    (initial : app.PolicyExecution) :
    let M := app.focalInformation players environment who schedule initial
    let policy : (i : Unit) → M.BehavioralPolicy i := fun _ =>
      app.focalBehavioral players environment who schedule initial replacement
    let sites : (i : Unit) → Finset (M.InfoState i) := fun _ =>
      app.setupFocalSites players environment who schedule initials replacement
    app.setupResponseMixture players environment who schedule initials replacement =
      (FinDist.pi fun i => (policy i).toMixedWithin
        (sites i) (app.focalWaitPolicy players environment who schedule initial)).map
          fun pureProfile site =>
            ((pureProfile () (some site)).1).getD (app.invocationWait who) := by
  classical
  dsimp only
  let _ : DecidableEq (Option (app.InvocationSite who)) := Classical.decEq _
  let M := app.focalInformation players environment who schedule initial
  let policy := app.focalBehavioral players environment who schedule initial replacement
  let sites := app.setupFocalSites players environment who schedule initials replacement
  let fallback := app.focalWaitPolicy players environment who schedule initial
  let mixed : Unit → FinDist (M.Policy ()) := fun _ => policy.toMixedWithin sites fallback
  let readPolicy : M.Policy () → app.InvocationSite who → app.InvocationCommand who :=
    fun purePolicy site => (purePolicy (some site)).1.getD (app.invocationWait who)
  have projectDraw : ∀ (infos : List (Option (app.InvocationSite who)))
      (assignment : M.Policy ()),
      (FinDist.runDependent policy infos assignment).map readPolicy =
        FinDist.runDependent replacement (infos.filterMap fun x => x) (readPolicy assignment) := by
    intro infos
    induction infos with
    | nil => intro assignment; simp [FinDist.runDependent]
    | cons info rest ih =>
        intro assignment
        cases info with
        | none =>
            simp only [FinDist.runDependent, policy, focalBehavioral, FinDist.pure_bind,
              List.filterMap]
            let updated := FinDist.DependentAssignment.setOne assignment
              ⟨none, ⟨none, by simp [M]⟩⟩
            have hread : readPolicy updated = readPolicy assignment := by
              funext site
              unfold readPolicy updated
              rw [FinDist.DependentAssignment.setOne_apply_of_ne]
              simp
            rw [ih updated, hread]
        | some site =>
            simp only [FinDist.runDependent, policy, focalBehavioral, FinDist.bind_map,
              FinDist.map_bind, List.filterMap]
            apply FinDist.bind_congr
            intro command _
            have step := ih
              (FinDist.DependentAssignment.setOne assignment
                ⟨some site, ⟨some command, by simp [M]⟩⟩)
            let updated := FinDist.DependentAssignment.setOne assignment
              ⟨some site, ⟨some command, by simp [M]⟩⟩
            have hread : readPolicy updated =
                FinDist.DependentAssignment.setOne (readPolicy assignment) ⟨site, command⟩ := by
              funext other
              by_cases h : other = site
              · subst other
                simp [updated, readPolicy, FinDist.DependentAssignment.setOne_apply_self]
              · unfold updated readPolicy
                rw [FinDist.DependentAssignment.setOne_apply_of_ne]
                · rw [FinDist.DependentAssignment.setOne_apply_of_ne]
                  exact h
                · exact fun eq => h (Option.some.inj eq)
            simpa [updated, hread] using step
  change app.setupResponseMixture players environment who schedule initials replacement =
    (FinDist.pi mixed).map _
  calc
    _ = (mixed ()).map readPolicy := by
      unfold mixed InformationModel.BehavioralPolicy.toMixedWithin
        InformationModel.BehavioralPolicy.toMixedOn
      have restrictEq :
          FinDist.runDependent
              (InformationModel.BehavioralPolicy.restrictRandomization
                M policy sites fallback) sites.toList fallback =
            FinDist.runDependent policy sites.toList fallback := by
        apply FinDist.runDependent_congr_laws
        intro info hinfo
        simp [InformationModel.BehavioralPolicy.restrictRandomization,
          Finset.mem_toList.mp hinfo]
      unfold setupResponseMixture
      have restrictEq' := restrictEq
      simp only [M] at restrictEq'
      calc
        _ = (FinDist.runDependent policy sites.toList fallback).map readPolicy := by
          rw [projectDraw]
          rfl
        _ = _ := by exact congrArg (FinDist.map readPolicy) restrictEq'.symm
    _ = _ := by
      rw [← FinDist.map_apply_pi () mixed, FinDist.map_comp]
      rfl

/-- A single finite response mixture, chosen before the initial execution is
sampled, preserves the complete setup-wide native trace law. -/
theorem setupResponseMixture_tracePolicies_setup
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who)) :
    (app.setupResponseMixture players environment who schedule initials replacement).bind
      (fun response => initials.bind fun initial => app.tracePolicies
        (app.playersReplacing players who (fun site => FinDist.pure (response site)))
        (app.environmentReplacing environment who (fun site => FinDist.pure (response site)))
        schedule initial) =
      initials.bind fun initial => app.tracePolicies
        (app.playersReplacing players who replacement)
        (app.environmentReplacing environment who replacement) schedule initial := by
  classical
  rw [FinDist.bind_comm
    (app.setupResponseMixture players environment who schedule initials replacement) initials]
  apply FinDist.bind_congr
  intro initial hinitial
  let M := app.focalInformation players environment who schedule initial
  let start := (app.focalProtocol players environment who schedule initial).initHistory
  let policy : (i : Unit) → M.BehavioralPolicy i := fun _ =>
    app.focalBehavioral players environment who schedule initial replacement
  let sites : (i : Unit) → Finset (M.InfoState i) := fun _ =>
    app.setupFocalSites players environment who schedule initials replacement
  let fallback : (i : Unit) → M.Policy i := fun _ =>
    app.focalWaitPolicy players environment who schedule initial
  let readResponse (pureProfile : (i : Unit) → M.Policy i)
      (site : app.InvocationSite who) : app.InvocationCommand who :=
    ((pureProfile () (some site)).1).getD (app.invocationWait who)
  rw [app.setupResponseMixture_eq_focalMixed players environment who schedule initials
    replacement initial, FinDist.bind_map]
  have hprefix : app.focalRecordedTrace players environment who schedule initial start = id := rfl
  calc
    _ = (M.runMixedFrom (fun i => (policy i).toMixedWithin (sites i) (fallback i))
          schedule.length start).map
          (fun result => app.focalRecordedTrace players environment who schedule initial result
            (.finish result.state.execution)) := by
      rw [InformationModel.runMixedFrom, FinDist.map_bind]
      apply FinDist.bind_congr
      intro pureProfile _
      have hresponse : (fun site => FinDist.pure (readResponse pureProfile site)) =
          app.focalPolicyOfPure players environment who schedule initial (pureProfile ()) := rfl
      rw [hresponse]
      simpa only [hprefix, FinDist.map_id, start, ExecutionProtocol.initHistory_state] using
        (app.focal_runPureFrom players environment who schedule initial pureProfile start).symm
    _ = (M.runBehavioralFrom policy schedule.length start).map
          (fun result => app.focalRecordedTrace players environment who schedule initial result
            (.finish result.state.execution)) := by
      rw [app.focal_runMixedWithin_setup_eq_runBehavioral players environment who schedule
        initials replacement initial hinitial schedule.length (by rfl)]
    _ = _ := by
      simpa only [hprefix, FinDist.map_id, start, ExecutionProtocol.initHistory_state] using
        app.focal_runBehavioralFrom players environment who schedule initial replacement start

theorem exists_invocation_response_mixture_tracePolicies_setup
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who)) :
    ∃ mixture : FinDist (app.InvocationSite who → app.InvocationCommand who),
      mixture.bind (fun response => initials.bind fun initial => app.tracePolicies
        (app.playersReplacing players who (fun site => FinDist.pure (response site)))
        (app.environmentReplacing environment who (fun site => FinDist.pure (response site)))
        schedule initial) =
      initials.bind fun initial => app.tracePolicies
        (app.playersReplacing players who replacement)
        (app.environmentReplacing environment who replacement) schedule initial := by
  exact ⟨app.setupResponseMixture players environment who schedule initials replacement,
    app.setupResponseMixture_tracePolicies_setup players environment who schedule initials
      replacement⟩

/-- Execution projection of the explicit canonical setup-response mixture. -/
theorem setupResponseMixture_runPolicies_setup
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who)) :
    (app.setupResponseMixture players environment who schedule initials replacement).bind
      (fun response => initials.bind fun initial => app.runPolicies
        (app.playersReplacing players who (fun site => FinDist.pure (response site)))
        (app.environmentReplacing environment who (fun site => FinDist.pure (response site)))
        schedule initial) =
      initials.bind fun initial => app.runPolicies
        (app.playersReplacing players who replacement)
        (app.environmentReplacing environment who replacement) schedule initial := by
  have traced := app.setupResponseMixture_tracePolicies_setup players environment who schedule
    initials replacement
  have mapped := congrArg (FinDist.map PolicyTrace.last) traced
  simpa only [FinDist.map_bind, app.tracePolicies_last] using mapped

theorem exists_native_response_mixture_tracePolicies_setup
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution) (replacement : app.PlayerPolicy) :
    ∃ mixture : FinDist (List app.PlayerEntry → app.View → app.PlayerCommand),
      mixture.bind (fun response => initials.bind fun initial => app.tracePolicies
        (Profile.update (sig := policySignature Principal app) players who
          (fun history view => FinDist.pure (response history view)))
        environment schedule initial) =
      initials.bind fun initial => app.tracePolicies
        (Profile.update (sig := policySignature Principal app) players who replacement)
        environment schedule initial := by
  obtain ⟨mixture, hlaw⟩ := app.exists_invocation_response_mixture_tracePolicies_setup
    players environment (.player who) schedule initials (fun site => replacement site.1 site.2)
  refine ⟨mixture.map (fun response history view => response (history, view)), ?_⟩
  rw [FinDist.bind_map]
  exact hlaw

theorem exists_environment_response_mixture_tracePolicies_setup
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (initials : FinDist app.PolicyExecution) :
    ∃ mixture : FinDist
        (List app.EnvironmentEntry → app.EnvironmentObservation → app.EnvironmentPolicyCommand),
      mixture.bind (fun response => initials.bind fun initial => app.tracePolicies players
        (fun history view => FinDist.pure (response history view)) schedule initial) =
      initials.bind fun initial => app.tracePolicies players environment schedule initial := by
  obtain ⟨mixture, hlaw⟩ := app.exists_invocation_response_mixture_tracePolicies_setup
    players environment .environment schedule initials (fun site => environment site.1 site.2)
  refine ⟨mixture.map (fun response history view => response (history, view)), ?_⟩
  rw [FinDist.bind_map]
  exact hlaw

theorem exists_joint_response_mixture_tracePolicies_setup
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution) (replacement : app.PlayerPolicy) :
    ∃ mixture : FinDist
        ((List app.PlayerEntry → app.View → app.PlayerCommand) ×
          (List app.EnvironmentEntry → app.EnvironmentObservation →
            app.EnvironmentPolicyCommand)),
      mixture.bind (fun responses => initials.bind fun initial => app.tracePolicies
        (Profile.update (sig := policySignature Principal app) players who
          (fun history view => FinDist.pure (responses.1 history view)))
        (fun history view => FinDist.pure (responses.2 history view)) schedule initial) =
      initials.bind fun initial => app.tracePolicies
        (Profile.update (sig := policySignature Principal app) players who replacement)
        environment schedule initial := by
  obtain ⟨playerResponses, hplayers⟩ := app.exists_native_response_mixture_tracePolicies_setup
    players environment who schedule initials replacement
  let PlayerResponse := List app.PlayerEntry → app.View → app.PlayerCommand
  let EnvironmentResponse :=
    List app.EnvironmentEntry → app.EnvironmentObservation → app.EnvironmentPolicyCommand
  have environmentExists (response : PlayerResponse) : ∃ mixture : FinDist EnvironmentResponse,
      mixture.bind (fun environmentResponse => initials.bind fun initial => app.tracePolicies
        (Profile.update (sig := policySignature Principal app) players who
          (fun history view => FinDist.pure (response history view)))
        (fun history view => FinDist.pure (environmentResponse history view)) schedule initial) =
      initials.bind fun initial => app.tracePolicies
        (Profile.update (sig := policySignature Principal app) players who
          (fun history view => FinDist.pure (response history view)))
        environment schedule initial :=
    app.exists_environment_response_mixture_tracePolicies_setup
      (Profile.update (sig := policySignature Principal app) players who
        (fun history view => FinDist.pure (response history view)))
      environment schedule initials
  let environmentResponses (response : PlayerResponse) :=
    Classical.choose (environmentExists response)
  refine ⟨playerResponses.bind (fun response =>
    (environmentResponses response).map fun environmentResponse =>
      (response, environmentResponse)), ?_⟩
  rw [FinDist.bind_bind]
  calc
    _ = playerResponses.bind (fun response => initials.bind fun initial => app.tracePolicies
        (Profile.update (sig := policySignature Principal app) players who
          (fun history view => FinDist.pure (response history view)))
        environment schedule initial) := by
      apply FinDist.bind_congr
      intro response _
      rw [FinDist.bind_map]
      exact Classical.choose_spec (environmentExists response)
    _ = _ := hplayers

/-- Execution-only projection of the setup-wide joint response theorem. -/
theorem exists_joint_response_mixture_runPolicies_setup
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initials : FinDist app.PolicyExecution) (replacement : app.PlayerPolicy) :
    ∃ mixture : FinDist
        ((List app.PlayerEntry → app.View → app.PlayerCommand) ×
          (List app.EnvironmentEntry → app.EnvironmentObservation →
            app.EnvironmentPolicyCommand)),
      mixture.bind (fun responses => initials.bind fun initial => app.runPolicies
        (Profile.update (sig := policySignature Principal app) players who
          (fun history view => FinDist.pure (responses.1 history view)))
        (fun history view => FinDist.pure (responses.2 history view)) schedule initial) =
      initials.bind fun initial => app.runPolicies
        (Profile.update (sig := policySignature Principal app) players who replacement)
        environment schedule initial := by
  obtain ⟨mixture, hlaw⟩ := app.exists_joint_response_mixture_tracePolicies_setup
    players environment who schedule initials replacement
  refine ⟨mixture, ?_⟩
  have hmapped := congrArg (FinDist.map PolicyTrace.last) hlaw
  simpa only [FinDist.map_bind, app.tracePolicies_last] using hmapped

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.exists_joint_response_mixture_runPolicies_setup'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.exists_joint_response_mixture_runPolicies_setup
