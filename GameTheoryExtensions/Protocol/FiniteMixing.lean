/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.PolicyRandomization

/-! # Finitely supported mixed realizations

Kuhn realization draws a behavioral policy independently at finitely many
reachable information sites. When every local law at those sites has finite
support, the resulting mixed policy is a finite mixture of pure policies.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type*} {E : ExecutionProtocol ι} (M : InformationModel E)

variable {M} in
/-- Drawing finitely supported local laws at finitely many sites yields a
finitely supported mixed policy. -/
theorem BehavioralPolicy.toMixedOn_support_finite {i : ι} [DecidableEq (M.InfoState i)]
    (policy : M.BehavioralPolicy i) (sites : Finset (M.InfoState i))
    (fallback : M.Policy i) (finiteLaws : ∀ info, (policy info).support.Finite) :
    (policy.toMixedOn sites fallback).support.Finite := by
  unfold BehavioralPolicy.toMixedOn FiniteAssignment.sampleOn
  rw [PMF.support_map]
  apply Set.Finite.image
  exact (Set.Finite.pi' fun site => finiteLaws site.1).subset fun draws member =>
    (independentProduct_support_iff _ draws).1 member

/-- Finite-support form of bounded Kuhn realization from the initial history:
finitely many reachable sites with finitely supported local laws are realized
by a profile of finitely supported mixed policies. -/
theorem exists_finite_mixed_runMixed_eq_runBehavioral [Fintype ι]
    (hactsOnce : M.ActsOnceWhereItMatters)
    (policy : (i : ι) → M.BehavioralPolicy i) (fuel : ℕ)
    (hfinite : ∀ i,
      (M.behavioralSupportSitesFrom policy fuel E.initHistory i).Finite)
    (hlocal : ∀ i info, (policy i info).support.Finite) :
    ∃ mixed : (i : ι) → M.MixedPolicy i,
      (∀ i, (mixed i).support.Finite) ∧
        M.runMixed mixed fuel = M.runBehavioral policy fuel := by
  classical
  let sites : (i : ι) → Finset (M.InfoState i) :=
    fun i => (hfinite i).toFinset
  let fallback : (i : ι) → M.Policy i :=
    fun i => (policy i).supportFallback M
  let finitePolicy : (i : ι) → M.BehavioralPolicy i :=
    fun i => (policy i).restrictRandomization M (sites i) (fallback i)
  refine ⟨fun i => (finitePolicy i).toMixedOn (sites i) (fallback i), ?_, ?_⟩
  · intro i
    apply BehavioralPolicy.toMixedOn_support_finite
    intro info
    by_cases member : info ∈ sites i
    · simpa [finitePolicy, BehavioralPolicy.restrictRandomization, member] using
        hlocal i info
    · simp [finitePolicy, BehavioralPolicy.restrictRandomization, member]
  have hoff : ∀ i info, info ∉ sites i →
      finitePolicy i info = PMF.pure (fallback i info) := by
    intro i info hinfo
    simp [finitePolicy, BehavioralPolicy.restrictRandomization, hinfo]
  refine (M.runMixedFrom_toMixedOn hactsOnce fuel finitePolicy
    sites fallback E.initHistory hoff).trans ?_
  apply (M.runBehavioralFrom_congr_on_support fuel E.initHistory ?_).symm
  intro elapsed helapsed later hlater hterm i
  have hmem : M.infoOf i later.trace ∈ sites i := by
    exact (Set.Finite.mem_toFinset (hfinite i)).2
      (M.mem_behavioralSupportSitesFrom policy fuel elapsed helapsed
        E.initHistory later hlater hterm i)
  simp [finitePolicy, BehavioralPolicy.restrictRandomization, hmem]

end GameTheory.Protocol.InformationModel
