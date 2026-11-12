module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.DeviationSimulation
public import Vegas.Game.FactorTransfer

@[expose] public section

/-! # A phase that some executions skip

Some executions may already have taken a phase's step, so that the phase leaves
them unchanged. When the view of the point tells those executions apart from
the others, both before and after the phase, a phase's joint law and averaged
target for the others extend to every execution, provided the built policy
leaves the target of the skipping executions unchanged.
-/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability Interaction

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  {Point Outcome Traffic View Policy : Type}
  (point : app.Execution → Point) (traffic : app.Execution → Traffic)
  (view : Point → View) (target : Policy → Point → PMF Outcome)

/-- The joint law and averaged target a phase supplies from coupled priors of
executions satisfying `good`. -/
def PhaseJoint (good : app.Execution → Prop) (phase : app.Execution → PMF app.Execution) :
    Prop :=
  ∀ {Seed : Type} (prior : PMF Seed) (execution : Seed → app.Execution),
    (∀ seed ∈ prior.support, good (execution seed)) →
    ∀ noise : View → PMF Traffic,
    prior.map (fun seed => (point (execution seed), traffic (execution seed))) =
      (prior.map fun seed => point (execution seed)).bind (fun current =>
        (noise (view current)).map fun extra => (current, extra)) →
    ∃ (build : Policy → Policy) (nextNoise : View → PMF Traffic),
      (prior.bind fun seed => (phase (execution seed)).map fun final =>
        (point final, traffic final)) =
      (prior.bind fun seed => (phase (execution seed)).map point).bind (fun current =>
        (nextNoise (view current)).map fun extra => (current, extra)) ∧
      ∀ policy, (prior.bind fun seed => (phase (execution seed)).bind fun final =>
        target policy (point final)) =
        prior.bind fun seed => target (build policy) (point (execution seed))

variable {point traffic view target}

omit [DecidableEq Principal] in
/-- **A phase some executions skip.** If a phase leaves the skipping
executions unchanged, the view of the point tells them apart before and after
the phase, and the phase supplies its joint law and averaged target for the
other executions with a built policy that keeps the skipping executions'
targets, then it supplies them for all executions. -/
theorem PhaseJoint.of_skipping {good : app.Execution → Prop}
    {phase : app.Execution → PMF app.Execution} (skips : app.Execution → Prop)
    (skipped : View → Prop)
    (before : ∀ execution, good execution →
      (skips execution ↔ skipped (view (point execution))))
    (after : ∀ execution, good execution → ∀ final ∈ (phase execution).support,
      (skips execution ↔ skipped (view (point final))))
    (stays : ∀ execution, good execution → skips execution → phase execution = PMF.pure execution)
    (others : ∀ {Seed : Type} (prior : PMF Seed) (execution : Seed → app.Execution),
      (∀ seed ∈ prior.support, good (execution seed) ∧ ¬ skips (execution seed)) →
      ∀ noise : View → PMF Traffic,
      prior.map (fun seed => (point (execution seed), traffic (execution seed))) =
        (prior.map fun seed => point (execution seed)).bind (fun current =>
          (noise (view current)).map fun extra => (current, extra)) →
      ∃ (build : Policy → Policy) (nextNoise : View → PMF Traffic),
        (prior.bind fun seed => (phase (execution seed)).map fun final =>
          (point final, traffic final)) =
        (prior.bind fun seed => (phase (execution seed)).map point).bind (fun current =>
          (nextNoise (view current)).map fun extra => (current, extra)) ∧
        (∀ policy, (prior.bind fun seed => (phase (execution seed)).bind fun final =>
          target policy (point final)) =
          prior.bind fun seed => target (build policy) (point (execution seed))) ∧
        ∀ policy execution, good execution → skips execution →
          target (build policy) (point execution) = target policy (point execution)) :
    PhaseJoint point traffic view target good phase := by
  classical
  intro Seed prior execution goods noise factor
  let part : Set Seed := {seed | skips (execution seed)}
  -- the factored start law, as an equality of binds
  have factorBind : prior.bind (fun seed => PMF.pure (point (execution seed),
      traffic (execution seed))) = prior.bind fun seed =>
        (noise (view (point (execution seed)))).map fun extra =>
          (point (execution seed), extra) := by
    have := factor
    rw [PMF.bind_map] at this
    exact this
  have restrictFactor (piece : Set Seed) (classify : Point × Traffic → Prop)
      (classified : ∀ seed ∈ prior.support, ∀ pair : Point × Traffic,
        pair.1 = point (execution seed) → (classify pair ↔ seed ∈ piece))
      (some : ∃ seed ∈ piece, seed ∈ prior.support) :
      (prior.filter piece some).bind (fun seed => PMF.pure (point (execution seed),
        traffic (execution seed))) = (prior.filter piece some).bind fun seed =>
          (noise (view (point (execution seed)))).map fun extra =>
            (point (execution seed), extra) := by
    apply bind_filter_eq prior piece _ _ classify _ _ factorBind some
    · intro seed member pair inSupport
      rw [PMF.support_pure, Set.mem_singleton_iff] at inSupport
      exact classified seed member pair (by rw [inSupport])
    · intro seed member pair inSupport
      rw [PMF.support_map] at inSupport
      obtain ⟨extra, _, rfl⟩ := inSupport
      exact classified seed member _ rfl
  have filterSupport (piece : Set Seed) (some : ∃ seed ∈ piece, seed ∈ prior.support)
      (seed : Seed) (member : seed ∈ (prior.filter piece some).support) :
      seed ∈ piece ∧ seed ∈ prior.support := by
    rw [PMF.mem_support_filter_iff] at member
    exact member
  -- the others' joint law, when there are other executions
  have othersOf (some : ∃ seed ∈ partᶜ, seed ∈ prior.support) :=
    others (prior.filter partᶜ some) execution (fun seed member => by
      obtain ⟨outside, supported⟩ := filterSupport partᶜ some seed member
      exact ⟨goods seed supported, outside⟩) noise (by
      rw [PMF.bind_map]
      change (prior.filter partᶜ some).bind (fun seed => PMF.pure (point (execution seed),
        traffic (execution seed))) = _
      exact restrictFactor partᶜ (fun pair => ¬ skipped (view pair.1))
        (fun seed member pair same => by
          rw [same]
          change ¬ skipped (view (point (execution seed))) ↔ ¬ skips (execution seed)
          rw [before _ (goods seed member)]) some)
  by_cases someOthers : ∃ seed ∈ partᶜ, seed ∈ prior.support
  · obtain ⟨build, othersNoise, othersJoint, othersAveraged, keeps⟩ := othersOf someOthers
    refine ⟨build, fun observed => if skipped observed then noise observed
      else othersNoise observed, ?_, fun policy => ?_⟩
    · rw [PMF.bind_bind]
      apply bind_eq_of_split prior part
      · intro some
        have restricted := restrictFactor part (fun pair => skipped (view pair.1))
          (fun seed member pair same => by
            rw [same]
            exact (before _ (goods seed member)).symm) some
        refine Eq.trans ?_ (Eq.trans restricted ?_)
        · apply bind_congr_on_support _
          intro seed member
          obtain ⟨inside, supported⟩ := filterSupport part some seed member
          rw [stays _ (goods seed supported) inside, PMF.pure_map]
        · apply bind_congr_on_support _
          intro seed member
          obtain ⟨inside, supported⟩ := filterSupport part some seed member
          have skippedNow : skipped (view (point (execution seed))) :=
            (before _ (goods seed supported)).mp inside
          rw [stays _ (goods seed supported) inside, PMF.pure_map, PMF.pure_bind]
          simp only [skippedNow, ite_true]
      · intro some
        have joint := othersJoint
        rw [PMF.bind_bind] at joint
        refine joint.trans ?_
        apply bind_congr_on_support _
        intro seed member
        obtain ⟨outside, supported⟩ := filterSupport partᶜ some seed member
        simp only [PMF.bind_map]
        apply bind_congr_on_support _
        intro final reached
        have notSkipped : ¬ skipped (view (point final)) := fun skippedFinal =>
          outside ((after _ (goods seed supported) final reached).mpr skippedFinal)
        simp only [Function.comp_apply, ite_eq_right notSkipped]
    · apply bind_eq_of_split prior part
      · intro some
        apply bind_congr_on_support _
        intro seed member
        obtain ⟨inside, supported⟩ := filterSupport part some seed member
        rw [stays _ (goods seed supported) inside, PMF.pure_bind,
          keeps policy _ (goods seed supported) inside]
      · intro some
        exact othersAveraged policy
  · push Not at someOthers
    have allSkip (seed : Seed) (member : seed ∈ prior.support) : skips (execution seed) := by
      by_contra notSkip
      exact someOthers seed notSkip member
    refine ⟨id, noise, ?_, fun policy => ?_⟩
    · rw [PMF.bind_bind]
      refine Eq.trans ?_ (factorBind.trans ?_)
      · apply bind_congr_on_support _
        intro seed member
        rw [stays _ (goods seed member) (allSkip seed member), PMF.pure_map]
      · apply bind_congr_on_support _
        intro seed member
        rw [stays _ (goods seed member) (allSkip seed member), PMF.pure_map, PMF.pure_bind]
    · apply bind_congr_on_support _
      intro seed member
      rw [stays _ (goods seed member) (allSkip seed member), PMF.pure_bind]
      rfl

end Vegas
