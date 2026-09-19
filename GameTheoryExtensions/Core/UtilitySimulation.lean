/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Core.MixtureSimulation
import GameTheoryExtensions.Math.SelectiveStopping

/-! # Strategic transfer by utility bounds

Some target deviations admit a source deviation with at least as much utility,
although their outcome laws differ. The certificate is indexed by the coalitions
whose joint deviations it bounds. Honest utility equality alone reflects
equilibrium at a compiled profile; preservation needs the bound at the same
coalitions, where one source witness has to serve every member of a coalition
at once.

Singleton coalitions give approximate Nash and all nonempty coalitions give
strong Nash. These are genuinely different certificates. A target that adds a
communication channel to the source satisfies the singleton bound and refutes
the coalition bound, because one member can route private information to
another; `GameTheoryExtensionsTests.CoalitionSimulation` is that witness.

The utilities are parameters of a certificate. It transports no guarantee for
other utilities, and none for players outside the deviating coalition.
-/

noncomputable section

namespace GameTheory.GameForm

open GameTheory.Math.Probability

universe uPlayer uSource uTarget uMiddle uSourceOutcome uTargetOutcome uMiddleOutcome

variable {Player : Type uPlayer} [DecidableEq Player]

/-- The one-player coalitions. -/
def singletonGroups (Player : Type uPlayer) [DecidableEq Player] : Set (Finset Player) :=
  {members | ∃ who, members = {who}}

/-- Every coalition that can deviate at all. -/
def nonemptyGroups (Player : Type uPlayer) [DecidableEq Player] : Set (Finset Player) :=
  {members | members.Nonempty}

theorem singletonGroups_subset_nonemptyGroups :
    singletonGroups Player ⊆ nonemptyGroups Player := by
  rintro members ⟨who, rfl⟩
  exact Finset.singleton_nonempty who

/-- No coalition in `groups` has a joint replacement that improves every member
by more than `ε`. -/
def IsεGroupNash (F : GameForm.{uPlayer, uSource, uSourceOutcome} Player)
    (utility : F.sig.Outcome → Player → ℝ)
    (groups : Set (Finset Player)) (ε : ℝ) (profile : Profile F.sig) : Prop :=
  ∀ members ∈ groups, ∀ replacement : Subprofile F.sig members,
    ∃ member ∈ members,
      expectedUtility utility member
          (F.play (Profile.override members replacement profile)) ≤
        expectedUtility utility member (F.play profile) + ε

variable {F : GameForm.{uPlayer, uSource, uSourceOutcome} Player}

/-- At one-player coalitions the predicate is ordinary approximate Nash. -/
theorem isεGroupNash_singletonGroups_iff (utility : F.sig.Outcome → Player → ℝ)
    (ε : ℝ) (profile : Profile F.sig) :
    IsεGroupNash F utility (singletonGroups Player) ε profile ↔
      IsεNash F utility ε profile := by
  rw [isεNash_iff]
  constructor
  · intro h who replacement
    obtain ⟨member, hmember, hbound⟩ := h {who} ⟨who, rfl⟩ (Subprofile.single who replacement)
    obtain rfl := Finset.mem_singleton.mp hmember
    rwa [Profile.override_single] at hbound
  · rintro h members ⟨who, rfl⟩ replacement
    refine ⟨who, Finset.mem_singleton_self who, ?_⟩
    rw [Profile.override_singleton]
    exact h who _

/-- At all nonempty coalitions the predicate is strong Nash for the `ε`-relaxed
expected-utility preference. -/
theorem isεGroupNash_nonemptyGroups_iff (utility : F.sig.Outcome → Player → ℝ)
    (ε : ℝ) (profile : Profile F.sig) :
    IsεGroupNash F utility (nonemptyGroups Player) ε profile ↔
      IsStrongNash F (euPreferenceWithin ε utility) profile := by
  rw [isStrongNash_iff]
  exact ⟨fun h coalition hne replacement => h coalition hne replacement,
    fun h members hmembers replacement => h members hmembers replacement⟩

/-- A strategy translation preserving honest expected utilities and bounding
every joint deviation of an allowed coalition by one legal source deviation.
The witness may depend on the fixed opponents and on the utilities, but a
single witness must serve every member of the coalition. -/
structure UtilitySimulation
    (source : GameForm.{uPlayer, uSource, uSourceOutcome} Player)
    (target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player)
    (sourceUtility : source.sig.Outcome → Player → ℝ)
    (targetUtility : target.sig.Outcome → Player → ℝ)
    (groups : Set (Finset Player)) where
  compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who
  honest_utility : ∀ profile who,
    (target.play (fun player => compileStrategy player (profile player))).expect
        (fun outcome => targetUtility outcome who) =
      (source.play profile).expect (fun outcome => sourceUtility outcome who)
  deviation_bound : ∀ members ∈ groups, ∀ (profile : Profile source.sig)
      (replacement : Subprofile target.sig members),
    ∃ alternative : Subprofile source.sig members, ∀ member ∈ members,
      (target.play (Profile.override members replacement
          (fun player => compileStrategy player (profile player)))).expect
          (fun outcome => targetUtility outcome member) ≤
        (source.play (Profile.override members alternative profile)).expect
          (fun outcome => sourceUtility outcome member)

variable {source : GameForm.{uPlayer, uSource, uSourceOutcome} Player}
variable {target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player}
variable {sourceUtility : source.sig.Outcome → Player → ℝ}
variable {targetUtility : target.sig.Outcome → Player → ℝ}

/-- Compiling a coalition's replacement commutes with overriding it. -/
theorem compileStrategy_override
    (compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (members : Finset Player) (replacement : Subprofile source.sig members)
    (profile : Profile source.sig) :
    Profile.override members (fun i => compileStrategy i.1 (replacement i))
        (fun player => compileStrategy player (profile player)) =
      fun player =>
        compileStrategy player (Profile.override members replacement profile player) := by
  funext player
  by_cases h : player ∈ members <;> simp [Profile.override, h]

/-- Honest expected-utility equality alone reflects the coalition predicate
from a compiled profile. No simulation of target deviations is needed. -/
theorem isεGroupNash_of_compileProfile
    (compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honestUtility : ∀ profile who,
      (target.play (fun player => compileStrategy player (profile player))).expect
          (fun outcome => targetUtility outcome who) =
        (source.play profile).expect (fun outcome => sourceUtility outcome who))
    (groups : Set (Finset Player)) (ε : ℝ) (profile : Profile source.sig)
    (h : IsεGroupNash target targetUtility groups ε
      (fun player => compileStrategy player (profile player))) :
    IsεGroupNash source sourceUtility groups ε profile := by
  intro members hmembers replacement
  obtain ⟨member, hmember, hbound⟩ :=
    h members hmembers (fun i => compileStrategy i.1 (replacement i))
  refine ⟨member, hmember, ?_⟩
  rw [compileStrategy_override] at hbound
  simp only [expectedUtility] at hbound ⊢
  rwa [honestUtility, honestUtility] at hbound

/-- Utility equality at compiled profiles and coalition deviation bounds give
the same additive error on both sides. -/
theorem isεGroupNash_compileProfile_iff_of_utility_bounds
    (compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honestUtility : ∀ profile who,
      (target.play (fun player => compileStrategy player (profile player))).expect
          (fun outcome => targetUtility outcome who) =
        (source.play profile).expect (fun outcome => sourceUtility outcome who))
    (groups : Set (Finset Player)) (profile : Profile source.sig)
    (deviationBound : ∀ members ∈ groups,
      ∀ replacement : Subprofile target.sig members,
      ∃ alternative : Subprofile source.sig members, ∀ member ∈ members,
        (target.play (Profile.override members replacement
            (fun player => compileStrategy player (profile player)))).expect
            (fun outcome => targetUtility outcome member) ≤
          (source.play (Profile.override members alternative profile)).expect
            (fun outcome => sourceUtility outcome member))
    (ε : ℝ) :
    IsεGroupNash target targetUtility groups ε
        (fun player => compileStrategy player (profile player)) ↔
      IsεGroupNash source sourceUtility groups ε profile := by
  constructor
  · exact isεGroupNash_of_compileProfile compileStrategy honestUtility groups ε profile
  · intro h members hmembers replacement
    obtain ⟨alternative, hbound⟩ := deviationBound members hmembers replacement
    obtain ⟨member, hmember, hsource⟩ := h members hmembers alternative
    refine ⟨member, hmember, ?_⟩
    simp only [expectedUtility] at hsource ⊢
    refine (hbound member hmember).trans (hsource.trans ?_)
    rw [honestUtility]

namespace UtilitySimulation

variable {groups : Set (Finset Player)}

def compileProfile
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (profile : Profile source.sig) : Profile target.sig :=
  fun who => simulation.compileStrategy who (profile who)

theorem compileProfile_update
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (profile : Profile source.sig) (who : Player) (alternative : source.sig.Strategy who) :
    Profile.update (simulation.compileProfile profile) who
        (simulation.compileStrategy who alternative) =
      simulation.compileProfile (Profile.update profile who alternative) := by
  funext player
  by_cases h : player = who
  · subst player; simp [compileProfile]
  · simp [compileProfile, Profile.update_of_ne, h]

/-- The same additive error is preserved and reflected at every compiled
profile, for the coalitions the certificate covers. -/
theorem isεGroupNash_compileProfile_iff
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (ε : ℝ) (profile : Profile source.sig) :
    IsεGroupNash target targetUtility groups ε (simulation.compileProfile profile) ↔
      IsεGroupNash source sourceUtility groups ε profile :=
  isεGroupNash_compileProfile_iff_of_utility_bounds simulation.compileStrategy
    simulation.honest_utility groups profile
    (fun members hmembers replacement =>
      simulation.deviation_bound members hmembers profile replacement) ε

/-- A certificate for the one-player coalitions transfers approximate Nash. -/
theorem isεNash_compileProfile_iff
    (simulation : UtilitySimulation source target sourceUtility targetUtility
      (singletonGroups Player))
    (ε : ℝ) (profile : Profile source.sig) :
    IsεNash target targetUtility ε (simulation.compileProfile profile) ↔
      IsεNash source sourceUtility ε profile := by
  rw [← isεGroupNash_singletonGroups_iff, ← isεGroupNash_singletonGroups_iff]
  exact simulation.isεGroupNash_compileProfile_iff ε profile

theorem isNash_compileProfile_iff
    (simulation : UtilitySimulation source target sourceUtility targetUtility
      (singletonGroups Player))
    (profile : Profile source.sig) :
    IsNash target (euPreference targetUtility) (simulation.compileProfile profile) ↔
      IsNash source (euPreference sourceUtility) profile := by
  simpa only [isNash_iff_isεNash_zero] using simulation.isεNash_compileProfile_iff 0 profile

/-- A certificate for every nonempty coalition transfers strong Nash. -/
theorem isStrongNash_compileProfile_iff
    (simulation : UtilitySimulation source target sourceUtility targetUtility
      (nonemptyGroups Player))
    (ε : ℝ) (profile : Profile source.sig) :
    IsStrongNash target (euPreferenceWithin ε targetUtility)
        (simulation.compileProfile profile) ↔
      IsStrongNash source (euPreferenceWithin ε sourceUtility) profile := by
  rw [← isεGroupNash_nonemptyGroups_iff, ← isεGroupNash_nonemptyGroups_iff]
  exact simulation.isεGroupNash_compileProfile_iff ε profile

/-- Strong Nash is reflected from a compiled profile by honest utilities alone,
with no coalition bound. Preservation is the direction that needs one. -/
theorem isStrongNash_of_compileProfile
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (ε : ℝ) (profile : Profile source.sig)
    (h : IsStrongNash target (euPreferenceWithin ε targetUtility)
      (simulation.compileProfile profile)) :
    IsStrongNash source (euPreferenceWithin ε sourceUtility) profile := by
  rw [← isεGroupNash_nonemptyGroups_iff] at h ⊢
  exact isεGroupNash_of_compileProfile simulation.compileStrategy simulation.honest_utility
    (nonemptyGroups Player) ε profile h

/-- The one-player case of the coalition bound, in unilateral form. -/
theorem unilateral_bound
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (hsingle : singletonGroups Player ⊆ groups)
    (profile : Profile source.sig) (who : Player)
    (replacement : target.sig.Strategy who) :
    ∃ alternative : source.sig.Strategy who,
      (target.play (Profile.update (simulation.compileProfile profile) who replacement)).expect
          (fun outcome => targetUtility outcome who) ≤
        (source.play (Profile.update profile who alternative)).expect
          (fun outcome => sourceUtility outcome who) := by
  obtain ⟨alternative, hbound⟩ := simulation.deviation_bound {who} (hsingle ⟨who, rfl⟩)
    profile (Subprofile.single who replacement)
  refine ⟨alternative ⟨who, Finset.mem_singleton_self who⟩, ?_⟩
  have hstep := hbound who (Finset.mem_singleton_self who)
  rwa [Profile.override_single, Profile.override_singleton] at hstep

/-- Compiling opponents ignores the deviator's own coordinate, which the
best-response comparison overwrites on both sides. -/
private theorem update_compileProfile_update
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (profile : Profile source.sig) (who : Player)
    (strategy : source.sig.Strategy who) (replacement : target.sig.Strategy who) :
    Profile.update (simulation.compileProfile (Profile.update profile who strategy))
        who replacement =
      Profile.update (simulation.compileProfile profile) who replacement := by
  funext player
  by_cases h : player = who
  · subst player; simp
  · simp [compileProfile, Profile.update_of_ne, h]

/-- A source best response compiles to a best response against the compiled
opponents, now against arbitrary target deviations. Unlike the Nash transfer
this fixes one player, so the opponents need not be best responding. Target
profiles outside the compiler image are not covered. -/
theorem isBestResponse_compileProfile
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (hsingle : singletonGroups Player ⊆ groups)
    (profile : Profile source.sig) (who : Player)
    (best : IsBestResponse source (euPreference sourceUtility) who profile (profile who)) :
    IsBestResponse target (euPreference targetUtility) who
      (simulation.compileProfile profile)
      (simulation.compileStrategy who (profile who)) := by
  intro replacement
  obtain ⟨alternative, hbound⟩ := simulation.unilateral_bound hsingle profile who replacement
  have hbest := best alternative
  rw [euPreference_apply, Profile.update_eq_self] at hbest
  rw [euPreference_apply, simulation.compileProfile_update profile who (profile who),
    Profile.update_eq_self]
  exact hbound.trans (hbest.trans (simulation.honest_utility profile who).symm.le)

/-- A dominant source strategy compiles to a best response against every
compiled opponent profile. Arbitrary target deviations are admitted, whereas
opponents outside the compiler image are not: this is dominance relative to the
source-expressible environments, not target dominance. -/
theorem isBestResponse_compileStrategy_of_isDominant
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (hsingle : singletonGroups Player ⊆ groups)
    (who : Player) (strategy : source.sig.Strategy who)
    (dominant : IsDominant source (euPreference sourceUtility) who strategy)
    (opponents : Profile source.sig) :
    IsBestResponse target (euPreference targetUtility) who
      (simulation.compileProfile opponents) (simulation.compileStrategy who strategy) := by
  have hown : (Profile.update opponents who strategy) who = strategy :=
    Profile.update_same opponents who strategy
  have best : IsBestResponse source (euPreference sourceUtility) who
      (Profile.update opponents who strategy)
      ((Profile.update opponents who strategy) who) := by
    intro alternative
    rw [hown]
    exact dominant alternative (Profile.update opponents who strategy)
  have transferred := simulation.isBestResponse_compileProfile hsingle
    (Profile.update opponents who strategy) who best
  rw [hown] at transferred
  intro replacement
  have hstep := transferred replacement
  simp only [simulation.update_compileProfile_update] at hstep
  exact hstep

/-- Build the one-player certificate from a bound stated per deviating
player. -/
def ofUnilateral
    (compileStrategy : (who : Player) → source.sig.Strategy who → target.sig.Strategy who)
    (honestUtility : ∀ profile who,
      (target.play (fun player => compileStrategy player (profile player))).expect
          (fun outcome => targetUtility outcome who) =
        (source.play profile).expect (fun outcome => sourceUtility outcome who))
    (deviationBound : ∀ profile who replacement,
      ∃ alternative : source.sig.Strategy who,
        (target.play (Profile.update
          (fun player => compileStrategy player (profile player)) who replacement)).expect
            (fun outcome => targetUtility outcome who) ≤
          (source.play (Profile.update profile who alternative)).expect
            (fun outcome => sourceUtility outcome who)) :
    UtilitySimulation source target sourceUtility targetUtility (singletonGroups Player) where
  compileStrategy := compileStrategy
  honest_utility := honestUtility
  deviation_bound := by
    rintro members ⟨who, rfl⟩ profile replacement
    obtain ⟨alternative, hbound⟩ :=
      deviationBound profile who (replacement ⟨who, Finset.mem_singleton_self who⟩)
    refine ⟨Subprofile.single who alternative, ?_⟩
    intro member hmember
    obtain rfl := Finset.mem_singleton.mp hmember
    rw [Profile.override_single, Profile.override_singleton]
    exact hbound

/-- A simulation is unchanged by utility interpretations with the same
expectation at every game profile. Values at unreachable outcomes can differ;
the strategy translation is retained exactly. -/
def congrUtilities
    (simulation : UtilitySimulation source target sourceUtility targetUtility groups)
    (sourceValue : source.sig.Outcome → Player → ℝ)
    (targetValue : target.sig.Outcome → Player → ℝ)
    (hsource : ∀ profile who,
      (source.play profile).expect (fun outcome => sourceUtility outcome who) =
        (source.play profile).expect (fun outcome => sourceValue outcome who))
    (htarget : ∀ profile who,
      (target.play profile).expect (fun outcome => targetUtility outcome who) =
        (target.play profile).expect (fun outcome => targetValue outcome who)) :
    UtilitySimulation source target sourceValue targetValue groups where
  compileStrategy := simulation.compileStrategy
  honest_utility profile who :=
    (htarget _ who).symm.trans ((simulation.honest_utility profile who).trans (hsource profile who))
  deviation_bound members hmembers profile replacement := by
    obtain ⟨alternative, hbound⟩ := simulation.deviation_bound members hmembers profile replacement
    exact ⟨alternative, fun member hmember =>
      (htarget _ member).symm.le.trans ((hbound member hmember).trans (hsource _ member).le)⟩

/-- Utility comparisons compose through independently verified target layers. -/
def trans {middle : GameForm.{uPlayer, uMiddle, uMiddleOutcome} Player}
    {middleUtility : middle.sig.Outcome → Player → ℝ}
    (left : UtilitySimulation source middle sourceUtility middleUtility groups)
    (right : UtilitySimulation middle target middleUtility targetUtility groups) :
    UtilitySimulation source target sourceUtility targetUtility groups where
  compileStrategy who strategy := right.compileStrategy who (left.compileStrategy who strategy)
  honest_utility profile who :=
    (right.honest_utility (left.compileProfile profile) who).trans
      (left.honest_utility profile who)
  deviation_bound members hmembers profile replacement := by
    obtain ⟨middleAlternative, hright⟩ :=
      right.deviation_bound members hmembers (left.compileProfile profile) replacement
    obtain ⟨sourceAlternative, hleft⟩ :=
      left.deviation_bound members hmembers profile middleAlternative
    exact ⟨sourceAlternative, fun member hmember =>
      (hright member hmember).trans (hleft member hmember)⟩

end UtilitySimulation

/-- Exact finite-mixture simulation supplies a one-player utility certificate
for every chosen utility on the common observation. A finite mixture has a
component whose utility is at least its mean, which is why the mixture
certificate is unilateral: a single component need not serve two members of a
coalition at once. -/
def MixtureSimulationOn.toUtilitySimulation
    {source : GameForm.{uPlayer, uSource, uSourceOutcome} Player}
    {target : GameForm.{uPlayer, uTarget, uTargetOutcome} Player}
    {Observation : Type*} {sourceObserve : source.sig.Outcome → Observation}
    {targetObserve : target.sig.Outcome → Observation}
    {Considered : (who : Player) → target.sig.Strategy who → Prop}
    (simulation : MixtureSimulationOn source target sourceObserve targetObserve Considered)
    (utility : Observation → Player → ℝ) (hall : ∀ who strategy, Considered who strategy) :
    UtilitySimulation source target
      (fun outcome who => utility (sourceObserve outcome) who)
      (fun outcome who => utility (targetObserve outcome) who)
      (singletonGroups Player) :=
  UtilitySimulation.ofUnilateral simulation.compileStrategy
    (fun profile who => simulation.expect_compile profile (fun obs => utility obs who))
    (by
      intro profile who replacement
      obtain ⟨alternatives, hlaw⟩ :=
        simulation.deviation_mixture profile who replacement (hall who replacement)
      have hexpect := congrArg (fun law => law.expect (fun obs => utility obs who)) hlaw
      simp only [FinDist.expect_map, FinDist.expect_bind] at hexpect
      obtain ⟨alternative, _, hbound⟩ := FinDist.exists_expect_le_support alternatives
        (fun alternative => (source.play (Profile.update profile who alternative)).expect
          (fun outcome => utility (sourceObserve outcome) who))
      exact ⟨alternative, hexpect.le.trans hbound⟩)

end GameTheory.GameForm
