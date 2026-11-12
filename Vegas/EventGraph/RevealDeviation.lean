module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.SchedulerReplay
public import Vegas.EventGraph.RevealRelaxedScheduling

@[expose] public section

/-! # Deviations against concurrent-reveal-oblivious profiles

On a graph whose only concurrency is between independent reveals, fix a profile
whose kernels ignore the observation at publications and normalize it. Let one
player deviate to any policy that also ignores the observation at its own
publications. That policy may still read the completion order, which a
randomized public scheduler reveals gradually. Its law under every public
scheduler is a mixture of canonical laws of normalized deviations: the scheduler
is a mixture of deterministic schedulers, under each of which the completion
order is recomputable from public data.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

variable (graph) in
/-- At every publication of its owner the policy ignores the observation. -/
def PolicyObliviousAtPublications (who : Player) (policy : graph.BehavioralPolicy who) : Prop :=
  ∀ event (actor : graph.actor? event = some who),
    (graph.outputLayout event).IsPublication →
      ∀ (left right : graph.PlayerObservation who) leftActive rightActive,
        policy event actor left leftActive = policy event actor right rightActive

theorem PolicyObliviousAtPublications.replay {profile : graph.BehavioralProfile}
    {assignment : graph.ScheduleSite → Option graph.EventId} {who : Player}
    {policy : graph.BehavioralPolicy who}
    (oblivious : graph.PolicyObliviousAtPublications who policy) :
    graph.PolicyObliviousAtPublications who (replayPolicy profile assignment who policy) := by
  intro event actor publication left right leftActive rightActive
  unfold replayPolicy
  split <;> split <;> exact oblivious event actor publication _ _ _ _

theorem ObliviousAtPublications.update {profile : graph.BehavioralProfile}
    (oblivious : graph.ObliviousAtPublications profile) {who : Player}
    {policy : graph.BehavioralPolicy who}
    (policyOblivious : graph.PolicyObliviousAtPublications who policy) :
    graph.ObliviousAtPublications
      (Profile.update (sig := graph.gameSignature) profile who policy) := by
  intro owner event actor publication left right leftActive rightActive
  by_cases same : owner = who
  · subst owner
    simp only [Profile.update_same]
    exact policyOblivious event actor publication left right leftActive rightActive
  · simp only [Profile.update_of_ne _ _ same]
    exact oblivious owner event actor publication left right leftActive rightActive

/-- **Deviation mixture.** Against the normalization of a profile oblivious at
publications, a deviation oblivious at its own publications has, under every
public scheduler, a mixture of canonical laws of normalized deviations. -/
theorem RevealsOnlyConcurrent.deviation_mixture (only : graph.RevealsOnlyConcurrent)
    (finite : graph.FiniteActions) (profile : graph.BehavioralProfile)
    (oblivious : graph.ObliviousAtPublications profile) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (policyOblivious : graph.PolicyObliviousAtPublications who policy)
    (scheduler : graph.PublicScheduler) (inputs : PMF graph.Inputs)
    (finiteInputs : inputs.support.Finite) :
    ∃ mixture : PMF (graph.ScheduleSite → Option graph.EventId),
      (inputs.bind (graph.runPolicies scheduler
          (Profile.update (sig := graph.gameSignature) (graph.normalizeProfile profile) who
            policy))).map runKey =
        mixture.bind fun assignment =>
          (inputs.bind (graph.runPolicies graph.canonicalScheduler
            (graph.normalizeProfile (Profile.update (sig := graph.gameSignature) profile who
              (replayPolicy (Profile.update (sig := graph.gameSignature)
                (graph.normalizeProfile profile) who policy) assignment who policy))))).map
            runKey := by
  let deviating := Profile.update (sig := graph.gameSignature) (graph.normalizeProfile profile)
    who policy
  obtain ⟨mixture, law⟩ := exists_scheduler_mixture deviating
    (finite.profileFiniteSupport deviating) scheduler inputs finiteInputs
  refine ⟨mixture, ?_⟩
  rw [bind_congr_on_support _ fun initial supported => (law initial supported).symm,
    PMF.bind_comm, PMF.map_bind]
  apply bind_congr_on_support _
  intro assignment _
  let replayed := replayPolicy deviating assignment who policy
  have normalized : Profile.update (sig := graph.gameSignature) deviating who
        (graph.normalizePolicy who replayed) =
      graph.normalizeProfile (Profile.update (sig := graph.gameSignature) profile who
        replayed) := by
    rw [normalizeProfile_update]
    funext owner
    by_cases same : owner = who
    · subst owner
      simp only [deviating, Profile.update_same]
    · simp only [deviating, Profile.update_of_ne _ _ same]
  have replay (initial : graph.Inputs) := runPolicies_replay deviating assignment who initial
  simp only [deviating, Profile.update_same] at replay
  rw [PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro initial _
  rw [← replay initial]
  change (graph.runPolicies _ (Profile.update (sig := graph.gameSignature) deviating who
    (graph.normalizePolicy who replayed)) initial).map runKey = _
  rw [normalized]
  exact only.runPolicies_map_runKey _ (oblivious.update policyOblivious.replay) _ initial

end Vegas.EventGraph
