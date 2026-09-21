/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.SchedulerMixture
import GameTheoryExtensions.Core.MixtureSimulation

/-! # Strategic equivalence of canonical and publicly scheduled EventGraphs -/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Observe the complete typed terminal store while forgetting its terminality
certificate and chronological trace. -/
def terminalStore (result : graph.gameSignature.Outcome) :
    EventGraph.Store graph.layout := result.1.store

private theorem gameForm_play_map_terminalStore
    (inputs : FinDist graph.Inputs) (scheduler : graph.PublicScheduler)
    (profile : graph.BehavioralProfile) :
    ((graph.gameForm inputs scheduler).play profile).map graph.terminalStore =
      inputs.bind fun initial =>
        (graph.runPolicies scheduler profile initial).map Config.store := by
  unfold gameForm terminalStore
  rw [FinDist.map_bind]
  apply FinDist.bind_congr
  intro initial _
  calc
    (graph.terminalOutcomes scheduler profile initial).map
        (fun result => result.1.store) =
      ((graph.terminalOutcomes scheduler profile initial).map Subtype.val).map
        Config.store := by rw [FinDist.map_comp]; rfl
    _ = (graph.runPolicies scheduler profile initial).map Config.store := by
      rw [graph.terminalOutcomes_map_val]

/-- Canonical execution and execution under an arbitrary adaptive public
scheduler form an exact unilateral-mixture simulation on typed terminal stores. -/
def eventSchedulingSimulation (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (scheduler : graph.PublicScheduler) :
    GameForm.MixtureSimulationOn (graph.canonicalGame inputs)
      (graph.gameForm inputs scheduler) graph.terminalStore graph.terminalStore
      (fun _ _ => True) where
  compileStrategy := graph.normalizePolicy
  honest_law profile := by
    change graph.BehavioralProfile at profile
    unfold canonicalGame
    have targetProfile :
        (fun who => graph.normalizePolicy who (profile who)) =
          graph.normalizeProfile profile := rfl
    rw [targetProfile, gameForm_play_map_terminalStore,
      gameForm_play_map_terminalStore]
    apply FinDist.bind_congr
    intro initial _
    calc
      (graph.runPolicies scheduler (graph.normalizeProfile profile) initial).map
          Config.store =
        (graph.runPolicies graph.canonicalScheduler
          (graph.normalizeProfile profile) initial).map Config.store :=
            ordered.runPolicies_store_eq_canonical profile scheduler initial
      _ = (graph.runPolicies graph.canonicalScheduler profile initial).map
          Config.store := by
            rw [← graph.runPolicies_canonical_normalize_eq profile initial]
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    change graph.BehavioralProfile at profile
    unfold canonicalGame
    obtain ⟨mixture, law⟩ := ordered.exists_deviation_mixture inputs scheduler
      profile who replacement
    have sourceProfile :
        (fun player => graph.normalizePolicy player (profile player)) =
          graph.normalizeProfile profile := rfl
    refine ⟨mixture, ?_⟩
    rw [sourceProfile]
    rw [gameForm_play_map_terminalStore]
    calc
      _ = mixture.bind (fun alternative => inputs.bind fun initial =>
          (graph.runPolicies graph.canonicalScheduler
            (Profile.update (sig := graph.gameSignature) profile who alternative)
            initial).map Config.store) := by
              simpa only [FinDist.map_bind] using law
      _ = _ := by
        apply FinDist.bind_congr
        intro alternative _
        exact (gameForm_play_map_terminalStore inputs graph.canonicalScheduler
          (Profile.update (sig := graph.gameSignature) profile who alternative)).symm

omit [DecidableEq Player] in
/-- An observation the terminal store determines, presented as a total decoder
that succeeds on every play. Stating it this way introduces no payload default,
and it is exactly the restriction the edge needs: schedulers agree on stores,
and disagree about completion order, so an observation of the order is not
recoverable. -/
private theorem map_some_observe {Ω : Type}
    (observe : graph.gameSignature.Outcome → Ω)
    (decode : EventGraph.Store graph.layout → Option Ω)
    (factors : ∀ outcome, decode (graph.terminalStore outcome) = some (observe outcome))
    (law : FinDist graph.gameSignature.Outcome) :
    (law.map observe).map some = (law.map graph.terminalStore).map decode := by
  rw [FinDist.map_comp, FinDist.map_comp]
  congr 1
  funext outcome
  exact (factors outcome).symm

/-- The canonical-to-scheduled edge read through any observation the terminal
store determines. This is what composes: an edge below supplies its own reading
of a completed play, and the scheduler is invisible to it. -/
def eventSchedulingSimulationOn {Ω : Type} (ordered : graph.BarrierOrdered)
    (inputs : FinDist graph.Inputs) (scheduler : graph.PublicScheduler)
    (observe : graph.gameSignature.Outcome → Ω)
    (decode : EventGraph.Store graph.layout → Option Ω)
    (factors : ∀ outcome, decode (graph.terminalStore outcome) = some (observe outcome)) :
    GameForm.MixtureSimulationOn (graph.canonicalGame inputs)
      (graph.gameForm inputs scheduler) observe observe (fun _ _ => True) where
  compileStrategy := graph.normalizePolicy
  honest_law profile := by
    have base := (graph.eventSchedulingSimulation ordered inputs scheduler).honest_law profile
    simp only [eventSchedulingSimulation] at base
    refine FinDist.map_injective (Option.some_injective _) ?_
    rw [graph.map_some_observe observe decode factors,
      graph.map_some_observe observe decode factors, base]
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement considered := by
    obtain ⟨mixture, law⟩ := (graph.eventSchedulingSimulation ordered inputs scheduler
      ).deviation_mixture profile who replacement considered
    simp only [eventSchedulingSimulation] at law
    refine ⟨mixture, FinDist.map_injective (Option.some_injective _) ?_⟩
    rw [graph.map_some_observe observe decode factors, law, FinDist.map_bind]
    rw [FinDist.map_bind]
    exact FinDist.bind_congr fun alternative _ =>
      (graph.map_some_observe observe decode factors _).symm

/-- Same-error Nash correspondence for every utility of the typed terminal
store. -/
theorem eventScheduling_approximate_nash_iff
    (ordered : graph.BarrierOrdered) (inputs : FinDist graph.Inputs)
    (scheduler : graph.PublicScheduler)
    (utility : EventGraph.Store graph.layout → Player → ℝ)
    (ε : ℝ) (profile : graph.BehavioralProfile) :
    IsεNash (graph.gameForm inputs scheduler)
        (fun outcome who => utility (graph.terminalStore outcome) who) ε
        (graph.normalizeProfile profile) ↔
      IsεNash (graph.canonicalGame inputs)
        (fun outcome who => utility (graph.terminalStore outcome) who) ε profile := by
  exact (graph.eventSchedulingSimulation ordered inputs scheduler).isεNash_compileProfile_iff
    utility ε profile (fun _ _ => trivial)

end Vegas.EventGraph
