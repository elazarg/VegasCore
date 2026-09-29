/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.HistoryRebase

/-! # Continuation comparisons across private disclosure aliases

At one normalized information fiber, the original private intentions have one
observation-local distribution. The prescribed normalized continuation and any
whole-policy deviation use that same distribution of source comparisons. Each
deviation is lifted uniformly across the hidden configurations, with admitted
support. These are laws of the existing source evaluator, including all later
samples, bindings, disclosures, and deferred guards.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {who : Player} {Γ : SourceCtx Player L} {O : Finset VarId}

/-- Observation-local posterior realization retains every binding interface. -/
theorem BehavioralPolicy.normalizeDisclosureFrom_admitted {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : BehavioralPolicy who program) → policy.Admitted program admission →
    (registry : Registry Γ) → (revelations : Revelations Γ) →
    (remember : DecisionView who Γ → PMF (List (OwnAction Player L))) →
    (policy.normalizeDisclosureFrom program registry revelations remember).Admitted
      program admission
  | _, _, .ret _, _, _, _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, policy, permitted, registry, revelations, remember =>
      policy.normalizeDisclosureFrom_admitted next admission permitted _ _ _
  | _, _, .commit _ _ _ _ next, admission, policy, permitted, registry, revelations, remember => by
      refine ⟨?_, policy.2.normalizeDisclosureFrom_admitted next
        (fun site => admission (some site)) permitted.2 _ _ _⟩
      intro own view choice supported
      obtain ⟨pair, pairSupported, rfl⟩ := PMF.support_map .. ▸ supported
      obtain ⟨past, _remembered, selected⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ pairSupported)
      obtain ⟨binding, chosen, rfl⟩ := PMF.support_map .. ▸ selected
      exact permitted.1 own (view.1, past) binding chosen
  | _, _, .reveal _ _ _ _ _ _ next, admission, policy, permitted, registry,
      revelations, remember =>
      policy.2.normalizeDisclosureFrom_admitted next admission permitted _ _ _

/-- The prescribed continuation is the mixture of original continuations at
the restored private histories. The mixture is fixed across the belief fiber. -/
theorem disclosure_prescribed_continuation_law
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (policy : BehavioralPolicy who program) (registry : Registry Γ)
    (revelations : Revelations Γ)
    (remember : DecisionView who Γ → PMF (List (OwnAction Player L)))
    (belief : PMF (Config Player L Γ)) (view : DecisionView who Γ)
    (sameView : ∀ config ∈ belief.support, config.view who = view)
    (registryEq : ∀ config ∈ belief.support, config.registry = registry)
    (revelationsEq : ∀ config ∈ belief.support, @config.revelations = @revelations) :
    (belief.bind fun config => runFrom program (Function.update profile who
      (policy.normalizeDisclosureFrom program registry revelations remember)) config) =
      (remember view).bind fun past =>
        (belief.map (fun config => config.withOwnHistory who past)).bind
          (runFrom program (Function.update profile who policy)) := by
  simp only [PMF.bind_map]
  rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro config supported
  have realized := normalizeDisclosureFrom_realize program profile policy config.registry
    config.revelations remember config.state config.history
  change ((remember (config.view who)).bind fun past =>
    runFrom program (Function.update profile who policy) (config.withOwnHistory who past)) =
      runFrom program (Function.update profile who
        (policy.normalizeDisclosureFrom program config.registry config.revelations remember))
          config at realized
  rw [registryEq config supported, revelationsEq config supported,
    sameView config supported] at realized
  exact realized.symm

/-- Every whole normalized deviation has one legal history-rebased lift for
each original private intention. Every lift yields the same deviation law;
the weights can therefore be exactly those of the prescribed continuation. -/
theorem disclosure_alternative_continuation_law
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (alternative : BehavioralPolicy who program)
    (belief : PMF (Config Player L Γ)) (view : DecisionView who Γ)
    (sameView : ∀ config ∈ belief.support, config.view who = view)
    (intentions : PMF (List (OwnAction Player L))) :
    (belief.bind (runFrom program (Function.update profile who alternative))) =
      intentions.bind fun past =>
        (belief.map (fun config => config.withOwnHistory who past)).bind
          (runFrom program (Function.update profile who
            (alternative.rebaseHistory past.length view.2 program))) := by
  trans intentions.bind fun _ =>
    belief.bind (runFrom program (Function.update profile who alternative))
  · exact (PMF.bind_const ..).symm
  · apply bind_congr_on_support _
    intro past _
    rw [PMF.bind_map, Function.comp_def]
    apply bind_congr_on_support _
    intro config supported
    rw [rebaseHistory_runFrom program profile alternative past view.2
      (config.withOwnHistory who past) (by simp only [Config.withOwnHistory, Function.update_self]),
      Config.withOwnHistory_twice]
    have own : config.history who = view.2 := congrArg Prod.snd (sameView config supported)
    rw [← own]
    simp only [Config.withOwnHistory, Function.update_eq_self]

/-- Source continuation bounds average without changing their error. This
uses whole-policy deviations, including future private randomization, rather
than only the next response. Posterior correctness is proved separately from
actual prefix execution in `Vegas.SourceProgram.normalized_disclosure_prefix_posterior`.
The utility must be integrable under both compared laws, which is automatic
when they are finitely supported. -/
theorem disclosure_continuation_gain_le
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (policy alternative : BehavioralPolicy who program)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (remember : DecisionView who Γ → PMF (List (OwnAction Player L)))
    (belief : PMF (Config Player L Γ)) (view : DecisionView who Γ)
    (sameView : ∀ config ∈ belief.support, config.view who = view)
    (registryEq : ∀ config ∈ belief.support, config.registry = registry)
    (revelationsEq : ∀ config ∈ belief.support, @config.revelations = @revelations)
    (utility : State L program.terminalCtx → ℝ) (error : ℝ)
    (sourceBound : ∀ past ∈ (remember view).support,
      expect ((belief.map (fun config => config.withOwnHistory who past)).bind
        (runFrom program (Function.update profile who
          (alternative.rebaseHistory past.length view.2 program)))) utility -
        expect ((belief.map (fun config => config.withOwnHistory who past)).bind
          (runFrom program (Function.update profile who policy))) utility ≤ error)
    (alternativeIntegrable : PayoffIntegrable
      (belief.bind (runFrom program (Function.update profile who alternative))) utility)
    (prescribedIntegrable : PayoffIntegrable (belief.bind (runFrom program
      (Function.update profile who
        (policy.normalizeDisclosureFrom program registry revelations remember)))) utility) :
    expect (belief.bind (runFrom program (Function.update profile who alternative))) utility -
      expect (belief.bind (runFrom program (Function.update profile who
        (policy.normalizeDisclosureFrom program registry revelations remember)))) utility ≤
      error := by
  rw [disclosure_alternative_continuation_law program profile alternative belief view sameView
      (remember view)] at alternativeIntegrable ⊢
  rw [disclosure_prescribed_continuation_law program profile policy registry revelations remember
      belief view sameView registryEq revelationsEq] at prescribedIntegrable ⊢
  have alternativeValues := payoffIntegrable_bind_conditionalExpectation _ _ _ alternativeIntegrable
  have prescribedValues := payoffIntegrable_bind_conditionalExpectation _ _ _ prescribedIntegrable
  rw [expect_bind_tower _ _ _ alternativeIntegrable, expect_bind_tower _ _ _ prescribedIntegrable,
    ← expect_sub alternativeValues prescribedValues]
  exact (expect_mono sourceBound (payoffIntegrable_sub alternativeValues prescribedValues)
    (payoffIntegrable_constant _ _)).trans_eq (expect_constant _ _)

end Vegas.SourceProgram
