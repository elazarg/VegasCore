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
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L))) →
    (policy.normalizeDisclosureFrom program registry revelations remember).Admitted
      program admission
  | _, _, .ret _, _, _, _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, policy, permitted, registry, revelations, remember =>
      policy.normalizeDisclosureFrom_admitted next admission permitted _ _ _
  | _, _, .commit _ _ _ _ next, admission, policy, permitted, registry, revelations, remember => by
      refine ⟨?_, policy.2.normalizeDisclosureFrom_admitted next
        (fun site => admission (some site)) permitted.2 _ _ _⟩
      intro own view choice supported
      obtain ⟨pair, pairSupported, rfl⟩ := FinDist.support_map .. ▸ supported
      obtain ⟨past, _remembered, selected⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ pairSupported)
      obtain ⟨binding, chosen, rfl⟩ := FinDist.support_map .. ▸ selected
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
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (belief : FinDist (Config Player L Γ)) (view : DecisionView who Γ)
    (sameView : ∀ config ∈ belief.support, config.view who = view)
    (registryEq : ∀ config ∈ belief.support, config.registry = registry)
    (revelationsEq : ∀ config ∈ belief.support, @config.revelations = @revelations) :
    (belief.bind fun config => runFrom program (Function.update profile who
      (policy.normalizeDisclosureFrom program registry revelations remember)) config) =
      (remember view).bind fun past =>
        (belief.map (fun config => config.withOwnHistory who past)).bind
          (runFrom program (Function.update profile who policy)) := by
  simp only [FinDist.bind_map]
  rw [FinDist.bind_comm]
  apply FinDist.bind_congr
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
    (belief : FinDist (Config Player L Γ)) (view : DecisionView who Γ)
    (sameView : ∀ config ∈ belief.support, config.view who = view)
    (intentions : FinDist (List (OwnAction Player L))) :
    (belief.bind (runFrom program (Function.update profile who alternative))) =
      intentions.bind fun past =>
        (belief.map (fun config => config.withOwnHistory who past)).bind
          (runFrom program (Function.update profile who
            (alternative.rebaseHistory past.length view.2 program))) := by
  trans intentions.bind fun _ =>
    belief.bind (runFrom program (Function.update profile who alternative))
  · exact (FinDist.bind_const ..).symm
  · apply FinDist.bind_congr
    intro past _
    rw [FinDist.bind_map]
    apply FinDist.bind_congr
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
actual prefix execution in `Vegas.SourceProgram.normalized_disclosure_prefix_posterior`. -/
theorem disclosure_continuation_gain_le
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (policy alternative : BehavioralPolicy who program)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (belief : FinDist (Config Player L Γ)) (view : DecisionView who Γ)
    (sameView : ∀ config ∈ belief.support, config.view who = view)
    (registryEq : ∀ config ∈ belief.support, config.registry = registry)
    (revelationsEq : ∀ config ∈ belief.support, @config.revelations = @revelations)
    (utility : State L program.terminalCtx → ℝ) (error : ℝ)
    (sourceBound : ∀ past ∈ (remember view).support,
      ((belief.map (fun config => config.withOwnHistory who past)).bind
        (runFrom program (Function.update profile who
          (alternative.rebaseHistory past.length view.2 program)))).expect utility -
        ((belief.map (fun config => config.withOwnHistory who past)).bind
          (runFrom program (Function.update profile who policy))).expect utility ≤ error) :
    (belief.bind (runFrom program (Function.update profile who alternative))).expect utility -
      (belief.bind (runFrom program (Function.update profile who
        (policy.normalizeDisclosureFrom program registry revelations remember)))).expect utility ≤
      error := by
  rw [disclosure_alternative_continuation_law program profile alternative belief view sameView
      (remember view),
    disclosure_prescribed_continuation_law program profile policy registry revelations remember
      belief view sameView registryEq revelationsEq,
    FinDist.expect_bind, FinDist.expect_bind, ← FinDist.expect_sub]
  exact (FinDist.expect_mono sourceBound).trans_eq (FinDist.expect_const _ _)

end Vegas.SourceProgram
