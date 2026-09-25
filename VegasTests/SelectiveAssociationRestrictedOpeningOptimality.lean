/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedOpening

/-! # Whole-policy optimality of prescribed native opening

At each legal opening history all bindings are frozen. The prescribed other
players publish those values, regardless of the current player's complete
deviation. Its successful publication therefore keeps the same payoff, while
failure is strictly worse whenever successful publication remains possible.
A failed binding forces the same failed publication under every continuation.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

def resultFor (result : Results) (who : Player) : PublicationResult Bool :=
  if who = alice then result.alice else if who = bob then result.bob else result.carol

theorem nativeResults_for (config : nativeGraph.Config) (who : Player) :
    resultFor (nativeResults config) who =
      ((nativePublicationRef who).get? config.store).getD .failure := by fin_cases who <;> rfl

def publication (who : Player) (state : app.ProtocolState) : PublicationResult Bool :=
  state.elim .failure (fun control =>
    ((nativePublicationRef who).get? control.execution.application.config.store).getD .failure)

/-- An arbitrary full policy can discard a frozen result but cannot replace
its value. The statement also covers failed bindings and incomplete runs. -/
theorem publication_or_failure (players : Profile model.behavioralSignature) (who : Player)
    (control : app.Control) (trace : arena.Trace (some control)) (value : PublicationResult Bool)
    (stored : (nativeBindingRef who).get? control.execution.application.config.store = some value)
    (fuel : Nat) (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom players fuel ⟨some control, trace⟩).support) :
    publication who final.state = value ∨ publication who final.state = .failure := by
  obtain ⟨result, stateEq, kept⟩ := (binding_invariant who value).behavioral_continuation menu
    (FinDist.pure nativeInitial) nativeHorizon scheduler players fuel control trace final stored
      supported
  rcases final with ⟨state, finalTrace⟩
  change state = some result at stateEq
  subst state
  change (((nativePublicationRef who).get? result.execution.application.config.store).getD
    .failure) = value ∨ (((nativePublicationRef who).get?
      result.execution.application.config.store).getD .failure) = .failure
  cases published : (nativePublicationRef who).get? result.execution.application.config.store with
  | none => exact Or.inr rfl
  | some output =>
      cases output with
      | failure => exact Or.inr rfl
      | success bit =>
          have original := native_publication_binding result.execution.application.config
            (native_history_reachable (observation := leaks) result finalTrace) who bit published
          rw [kept] at original
          cases Option.some.inj original
          exact Or.inl rfl

theorem prescribed_later_publication (players : Profile model.behavioralSignature)
    (first last : Player)
    (ordered : (nativePublicationEvent first).val ≤ (nativePublicationEvent last).val)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some first)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent first))
    (value : PublicationResult Bool)
    (stored : (nativeBindingRef last).get? control.execution.application.config.store = some value)
    (opens : Opens players last) (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom players (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support) : publication last final.state = value := by
  cases value with
  | failure =>
      exact (publication_or_failure players last control trace .failure stored _ final
        supported).elim id id
  | success bit =>
      obtain ⟨result, stateEq, published⟩ := future_opening_success players first last ordered
        control trace active granted bit stored opens final supported
      simp only [publication, stateEq, Option.elim_some, published, Option.getD_some]

theorem earlier_publication_fixed (players : Profile model.behavioralSignature)
    (first last : Player)
    (ordered : (nativePublicationEvent last).val < (nativePublicationEvent first).val)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some first)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent first))
    (fuel : Nat) (final : arena.History)
    (supported : final ∈ (model.runBehavioralFrom players fuel ⟨some control, trace⟩).support) :
    publication last final.state = publication last (some control) := by
  have complete := earlier_completed (nativePublicationEvent first) (nativePublicationEvent last)
    ordered control trace (by rwa [native_publication_owner]) granted
  have field := (control.execution.application.config.output_available
    (nativePublicationEvent last)).mpr complete
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
    ((nativePublicationRef last).get?_isSome control.execution.application.config.store field)
  obtain ⟨result, stateEq, kept⟩ :=
    (native_publication_invariant (observation := leaks) last value).behavioral_continuation menu
      (FinDist.pure nativeInitial) nativeHorizon scheduler players fuel control trace final stored
        supported
  simp only [publication, stateEq, Option.elim_some, kept, stored]

theorem update_opens_other (who other : Player) (different : other ≠ who)
    (alternative : model.BehavioralPolicy who) :
    Opens (Profile.update (sig := model.behavioralSignature) profile who alternative) other := by
  intro past view granted
  change app.decodePolicy (menu.embedPolicy (FinDist.pure nativeInitial) nativeHorizon scheduler
    other ((Profile.update (sig := model.behavioralSignature) profile who alternative) other))
      past view = _
  rw [Profile.update_of_ne _ _ different]
  exact profile_opens other past view granted

/-- Every other public result is fixed across the prescribed continuation and
an arbitrary complete policy deviation from the current opening. -/
theorem other_publication_same (who other : Player) (different : other ≠ who)
    (alternative : model.BehavioralPolicy who) (control : app.Control)
    (trace : arena.Trace (some control)) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (prescribed deviated : arena.History)
    (prescribedMem : prescribed ∈ (model.runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support)
    (deviatedMem : deviated ∈ (model.runBehavioralFrom
      (Profile.update (sig := model.behavioralSignature) profile who alternative)
        (2 * nativeHorizon + 1) ⟨some control, trace⟩).support) :
    publication other deviated.state = publication other prescribed.state := by
  by_cases ordered : (nativePublicationEvent who).val ≤ (nativePublicationEvent other).val
  · obtain ⟨value, stored⟩ := binding_present_at_opening other who control trace active granted
    rw [prescribed_later_publication _ who other ordered control trace active granted value stored
      (update_opens_other who other different alternative) deviated deviatedMem,
      prescribed_later_publication profile who other ordered control trace active granted value
        stored (profile_Opens other) prescribed prescribedMem]
  · have earlier := Nat.lt_of_not_ge ordered
    rw [earlier_publication_fixed _ who other earlier control trace active granted _ deviated
      deviatedMem, earlier_publication_fixed profile who other earlier control trace active granted
        _ prescribed prescribedMem]

theorem payoff_le_of_same_or_failure (first second : Results) (who : Player)
    (own : resultFor first who = resultFor second who ∨ resultFor first who = .failure)
    (others : ∀ other, other ≠ who → resultFor first other = resultFor second other) :
    utility first who ≤ utility second who := by
  rcases own with same | failed
  · have all : ∀ other, resultFor first other = resultFor second other := by
      intro other
      by_cases identical : other = who
      · simpa only [identical] using same
      · exact others other identical
    have results : first = second := by
      have a : first.alice = second.alice := all alice
      have b : first.bob = second.bob := all bob
      have c : first.carol = second.carol := all carol
      cases first
      cases second
      cases a
      cases b
      cases c
      rfl
    rw [results]
  · have penalty : utility first who = -4 := by
      fin_cases who
      · change first.alice = .failure at failed
        change utility first alice = -4
        simp [utility_alice, failed]
      · change first.bob = .failure at failed
        change utility first bob = -4
        simp [utility_bob, failed]
      · change first.carol = .failure at failed
        change utility first carol = -4
        simp [utility_carol, failed]
    rw [penalty]
    fin_cases who
    · exact (utility_alice_bounds second).1
    · exact (utility_bob_bounds second).1
    · exact (utility_carol_bounds second).1

/-- Pointwise comparison of complete supported continuations. There is no
posterior premise and no restriction on the deviator's raw response policy. -/
theorem opening_payoff_optimal (who : Player) (alternative : model.BehavioralPolicy who)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (prescribed deviated : arena.History)
    (prescribedMem : prescribed ∈ (model.runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support)
    (deviatedMem : deviated ∈ (model.runBehavioralFrom
      (Profile.update (sig := model.behavioralSignature) profile who alternative)
        (2 * nativeHorizon + 1) ⟨some control, trace⟩).support) :
    nativeUtility who deviated.state ≤ nativeUtility who prescribed.state := by
  obtain ⟨value, stored⟩ := binding_present_at_opening who who control trace active granted
  obtain ⟨prescribedControl, prescribedEq, _⟩ :=
    (binding_invariant who value).behavioral_continuation menu (FinDist.pure nativeInitial)
      nativeHorizon scheduler profile _ control trace prescribed stored prescribedMem
  obtain ⟨deviatedControl, deviatedEq, _⟩ :=
    (binding_invariant who value).behavioral_continuation menu (FinDist.pure nativeInitial)
      nativeHorizon scheduler (Profile.update (sig := model.behavioralSignature) profile who
        alternative) _ control trace deviated stored deviatedMem
  have prescribedOwn := prescribed_later_publication profile who who le_rfl control trace active
    granted value stored (profile_Opens who) prescribed prescribedMem
  have deviatedOwn := publication_or_failure _ who control trace value stored _ deviated deviatedMem
  rw [← prescribedOwn] at deviatedOwn
  rw [prescribedEq, deviatedEq]
  apply payoff_le_of_same_or_failure
  · simpa only [nativeResults_for, publication, prescribedEq, deviatedEq, Option.elim_some] using
      deviatedOwn
  · intro other different
    have same := other_publication_same who other different alternative control trace active granted
      prescribed deviated prescribedMem deviatedMem
    simpa only [nativeResults_for, publication, prescribedEq, deviatedEq, Option.elim_some]
      using same

theorem opening_expectation_optimal (who : Player) (alternative : model.BehavioralPolicy who)
    (control : app.Control) (trace : arena.Trace (some control))
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who)) :
    (model.runBehavioralFrom (Profile.update (sig := model.behavioralSignature) profile who
      alternative) (2 * nativeHorizon + 1) ⟨some control, trace⟩).expect
        (fun history => nativeUtility who history.state) ≤
    (model.runBehavioralFrom profile (2 * nativeHorizon + 1) ⟨some control, trace⟩).expect
      (fun history => nativeUtility who history.state) := by
  let prescribed := model.runBehavioralFrom profile (2 * nativeHorizon + 1) ⟨some control, trace⟩
  let deviated := model.runBehavioralFrom (Profile.update (sig := model.behavioralSignature)
    profile who alternative) (2 * nativeHorizon + 1) ⟨some control, trace⟩
  change deviated.expect _ ≤ prescribed.expect _
  calc
    _ ≤ deviated.expect (fun _ => prescribed.expect (fun history =>
      nativeUtility who history.state)) := FinDist.expect_mono (by
        intro other otherMem
        calc
          _ = prescribed.expect (fun _ => nativeUtility who other.state) :=
            (FinDist.expect_const _ _).symm
          _ ≤ _ := FinDist.expect_mono (by
            intro final finalMem
            exact opening_payoff_optimal who alternative control trace active granted final other
              finalMem otherMem))
    _ = _ := FinDist.expect_const _ _

theorem information_control (who : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
    (history : model.InformationHistory who (some (past, view))) :
    ∃ control, history.1.state = some control ∧ control.actor = some who ∧
      control.execution.recall who = past ∧ control.execution.observe app who = view := by
  rcases history with ⟨⟨state, trace⟩, information⟩
  change (menu.signals (FinDist.pure nativeInitial) nativeHorizon scheduler).infoOf who trace =
    some (past, view) at information
  rw [menu.info] at information
  cases state with
  | none => cases information
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at information
        exact ⟨control, rfl, active, congrArg Prod.fst (Option.some.inj information),
          congrArg Prod.snd (Option.some.inj information)⟩
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at information
        cases information

/-- The complete prescribed policy is sequentially rational at every legal
opening information site, for every belief system over that site's histories.
No assumption of sequential rationality or posterior correctness is used. -/
theorem profile_opening_rational (assessment : model.BehavioralAssessment)
    (strategy : assessment.strategy = profile) (who : Player) (site : model.InformationSite who)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (information : site.1 = some (past, view))
    (granted : view.application.publicView.serviceGrant = some (nativePublicationEvent who)) :
    assessment.IsSequentiallyRationalAt site (assessment.continuationContext site
      (fun history => nativeUtility who history.state) (2 * nativeHorizon + 1)) := by
  intro alternative _
  simp only [InformationModel.BehavioralAssessment.continuationContext_value,
    FinDist.expect_bind, strategy, Profile.update_eq_self]
  apply FinDist.expect_mono
  intro history _
  obtain ⟨control, stateEq, active, _, observed⟩ :=
    information_control who past view ⟨history.1, history.2.trans information⟩
  rcases history with ⟨⟨state, trace⟩, historyInfo⟩
  change state = some control at stateEq
  subst state
  have controlGrant : control.execution.application.serviceGrant =
      some (nativePublicationEvent who) := by
    rw [← observed] at granted
    exact granted
  exact opening_expectation_optimal who alternative control trace active controlGrant

end VegasTests.SelectiveAssociation.Restricted
