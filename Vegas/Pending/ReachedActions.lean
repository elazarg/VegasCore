/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.DeviationPolicy
import Vegas.Pending.DeviationExtraction

/-! # Graph policies extracted from reached native phase changes

The partial action relation here refers to actual initialized runs of the
message runner. Its observations are typed graph observations, and its actions
are normalized effective state changes, not untrusted private policy records.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- An effective graph action reached at one invocation of a fixed native
schedule, starting from a supported private initial environment. -/
def ReachedOwnAction (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (inputs : FinDist (VEnv L Γ₀))
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) (focal : Player)
    (suffix : Graph Player L Γ Δ) (site : Nat) (observation : Observation L focal Γ)
    (action : OwnAction Player L) : Prop :=
  (match action with
    | .bind owner _ _ _ => owner = focal
    | .resolve owner _ _ => owner = focal) ∧
  ∃ input ∈ inputs.support, ∃ before instruction rest,
    schedule = before ++ instruction :: rest ∧
    ∃ execution next : runtime.application.PolicyExecution,
      execution ∈ (runtime.application.runPolicies players environment before
        (MessageApplication.PolicyExecution.initial runtime.application
          (MessageApplication.State.initial runtime.application
            (State.initial whole input)))).support ∧
      next ∈ (runtime.application.invoke players environment execution instruction).support ∧
      ∃ ideal values bindings candidates clock enteredAt,
        execution.native.application =
          .running suffix ideal values bindings candidates site clock enteredAt ∧
        observe focal ideal = observation ∧
        State.RealizesOwnAction execution.native.application action next.native.application

/-- Build one partial action relation for the whole graph, keeping the original
initialized native game fixed while descending through its typed suffixes. -/
def reachedActionRelation (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (inputs : FinDist (VEnv L Γ₀))
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) (focal : Player) :
    {Γ : VCtx Player L} → (suffix : Graph Player L Γ Δ) → Nat →
      ObservationActionRelation focal suffix
  | _, .ret _, _ => PUnit.unit
  | _, .sample _ _ _ next, site =>
      reachedActionRelation runtime whole inputs players environment schedule focal next (site + 1)
  | _, .bind (payload := payload) name owner fresh next, site =>
      (fun _ observation action =>
        ReachedOwnAction runtime whole inputs players environment schedule focal
          (.bind name owner fresh next) site observation (.bind owner name payload action),
        reachedActionRelation runtime whole inputs players environment schedule focal
          next (site + 1))
  | _, .resolve output owner binding fresh source checks next, site =>
      (fun _ observation action =>
        ReachedOwnAction runtime whole inputs players environment schedule focal
          (.resolve output owner binding fresh source checks next) site observation
          (.resolve owner binding action),
        reachedActionRelation runtime whole inputs players environment schedule focal
          next (site + 1))

/-- The relation at an actual graph cursor is the corresponding restriction
of the whole-graph relation. -/
theorem reachedActionRelation_tail (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (inputs : FinDist (VEnv L Γ₀))
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) (focal : Player)
    {start : VCtx Player L} {cursor : Graph Player L start Δ}
    {suffix : Graph Player L Γ Δ} {length : Nat}
    (walk : Prefix Δ cursor suffix length) (base : Nat) :
    ObservationActionRelation.tail focal walk
        (runtime.reachedActionRelation whole inputs players environment schedule focal
          cursor base) =
      runtime.reachedActionRelation whole inputs players environment schedule focal
        suffix (base + length) := by
  induction walk generalizing base with
  | refl => simp [ObservationActionRelation.tail]
  | sample _ ih | bind _ ih | resolve _ ih =>
      simp only [ObservationActionRelation.tail, reachedActionRelation]
      rw [ih]
      congr 1
      omega

/-- Observation-locality of reached effective actions makes the complete
partial graph-policy relation single-valued. -/
theorem reachedActionRelation_functional (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (inputs : FinDist (VEnv L Γ₀))
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) (focal : Player)
    (locality : ∀ {target} (suffix : Graph Player L target Δ) site
      (observation : Observation L focal target) (left right : OwnAction Player L),
      ReachedOwnAction runtime whole inputs players environment schedule focal
        suffix site observation left →
      ReachedOwnAction runtime whole inputs players environment schedule focal
        suffix site observation right → left = right)
    (suffix : Graph Player L Γ Δ) (site : Nat) :
    ObservationActionRelation.Functional focal suffix
      (runtime.reachedActionRelation whole inputs players environment schedule focal
        suffix site) := by
  induction suffix generalizing site with
  | ret => trivial
  | sample _ _ _ _ ih => exact ih runtime whole players environment locality (site + 1)
  | bind name owner fresh next ih =>
      refine ⟨?_, ih runtime whole players environment locality (site + 1)⟩
      intro owned observation left right leftReached rightReached
      have same := locality (.bind name owner fresh next) site observation
        (.bind owner name _ left) (.bind owner name _ right) leftReached rightReached
      simpa only [OwnAction.bind.injEq, heq_eq_eq, true_and] using same
  | resolve output owner binding fresh source checks next ih =>
      refine ⟨?_, ih runtime whole players environment locality (site + 1)⟩
      intro owned observation left right leftReached rightReached
      have same := locality (.resolve output owner binding fresh source checks next)
        site observation
        (.resolve owner binding left) (.resolve owner binding right) leftReached rightReached
      simpa only [OwnAction.resolve.injEq, true_and] using same

/-- The observation-only graph policy selected by effective native phase
changes. Locality is required to prove its realization law, not to define it. -/
def extractedObservationPolicy (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (inputs : FinDist (VEnv L Γ₀))
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) (focal : Player) :
    BehavioralPolicy focal whole :=
  ObservationActionRelation.complete focal whole
    (runtime.reachedActionRelation whole inputs players environment schedule focal whole 0)

theorem extractedObservationPolicy_ignoresOwnHistory (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (inputs : FinDist (VEnv L Γ₀))
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) (focal : Player) :
    PolicyIgnoresOwnHistory focal whole
      (runtime.extractedObservationPolicy whole inputs players environment schedule focal) :=
  ObservationActionRelation.complete_ignoresOwnHistory focal whole _

/-- At every actual typed cursor, completing the reached actions selects
exactly their normalized source action, independently of logical history. -/
theorem extractedObservationPolicy_realizesAt (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (inputs : FinDist (VEnv L Γ₀))
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player)) (focal : Player)
    (locality : ∀ {target} (suffix : Graph Player L target Δ) site
      (observation : Observation L focal target) (left right : OwnAction Player L),
      ReachedOwnAction runtime whole inputs players environment schedule focal
        suffix site observation left →
      ReachedOwnAction runtime whole inputs players environment schedule focal
        suffix site observation right → left = right)
    {suffix : Graph Player L Γ Δ} {site : Nat} (walk : Prefix Δ whole suffix site) :
    ObservationActionRelation.RealizedBy focal suffix
      (runtime.reachedActionRelation whole inputs players environment schedule focal suffix site)
      (walk.policyTail focal
        (runtime.extractedObservationPolicy whole inputs players environment schedule focal)) := by
  have realized := ObservationActionRelation.complete_realizes focal whole _
    (runtime.reachedActionRelation_functional whole inputs players environment schedule focal
      locality whole 0)
  have restricted := ObservationActionRelation.realizedBy_tail focal walk _ _ realized
  rw [runtime.reachedActionRelation_tail whole inputs players environment schedule focal walk 0,
    Nat.zero_add] at restricted
  exact restricted

/-- info: 'Vegas.GraphRuntime.extractedObservationPolicy_realizesAt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.extractedObservationPolicy_realizesAt

end Vegas.GraphRuntime
