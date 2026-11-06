/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveStopping
import GameTheoryExtensions.Math.Probability.Support

/-! # Simulating a deviation phase by phase

A deviation is simulated by a family of target laws indexed by policies when,
from every coupled prior over executions whose deviator traffic factors through
the deviator's view of the reached point, the run to the horizon has the target
law of some policy. One phase extends such a simulation backwards: if the phase
has a joint successor and traffic law of the same factored form, and the target
of a built policy takes the phase's step before the target of its tail, then
the simulation holds before the phase.
-/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability Interaction

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (scheduler : app.Scheduler) (players : Principal → app.Policy) (horizon : Nat)
  {Point Outcome Traffic View Policy : Type}
  (read : Point → Outcome) (point : app.Execution → Point) (traffic : app.Execution → Traffic)
  (view : Point → View) (target : Policy → Point → PMF Outcome)

/-- **A simulation of the run.** From every coupled prior over executions that
satisfy `good`, whose traffic factors through the view of their point, the run
to the horizon has the target law of one policy. -/
def DeviationSimulation (good : app.Execution → Prop) : Prop :=
  ∀ {Seed : Type} (prior : PMF Seed) (execution : Seed → app.Execution),
    (∀ seed ∈ prior.support, good (execution seed)) →
    ∀ noise : View → PMF Traffic,
    prior.map (fun seed => (point (execution seed), traffic (execution seed))) =
      (prior.map fun seed => point (execution seed)).bind (fun current =>
        (noise (view current)).map fun extra => (current, extra)) →
    ∃ policy : Policy,
      (prior.bind fun seed =>
        (app.runToHorizon scheduler players horizon (execution seed)).map fun final =>
          read (point final)) =
      prior.bind fun seed => target policy (point (execution seed))

variable {scheduler players horizon read point traffic view target}

/-- **One phase.** A phase with a factored joint successor and traffic law,
whose endpoints satisfy the tail's condition, extends the tail's simulation to
the phase's start when the target of a built policy takes the phase's step
first. -/
theorem DeviationSimulation.of_phase {good next : app.Execution → Prop}
    (tail : DeviationSimulation scheduler players horizon read point traffic view target next)
    (phase : app.Execution → PMF app.Execution)
    (markov : ∀ execution, good execution →
      app.runToHorizon scheduler players horizon execution =
        (phase execution).bind (app.runToHorizon scheduler players horizon))
    (endpoint : ∀ execution, good execution → ∀ final ∈ (phase execution).support, next final)
    (step : Point → PMF Point)
    (joint : ∀ {Seed : Type} (prior : PMF Seed) (execution : Seed → app.Execution),
      (∀ seed ∈ prior.support, good (execution seed)) →
      ∀ noise : View → PMF Traffic,
      prior.map (fun seed => (point (execution seed), traffic (execution seed))) =
        (prior.map fun seed => point (execution seed)).bind (fun current =>
          (noise (view current)).map fun extra => (current, extra)) →
      ∃ nextNoise : View → PMF Traffic,
        (prior.bind fun seed => (phase (execution seed)).map fun final =>
          (point final, traffic final)) =
        ((prior.map fun seed => point (execution seed)).bind step).bind fun current =>
          (nextNoise (view current)).map fun extra => (current, extra))
    (build : Policy → Policy)
    (targetStep : ∀ policy current, target (build policy) current =
      (step current).bind (target policy)) :
    DeviationSimulation scheduler players horizon read point traffic view target good := by
  intro Seed prior execution goods noise factor
  obtain ⟨nextNoise, phaseJoint⟩ := joint prior execution goods noise factor
  let staged := prior.bind fun seed => (phase (execution seed)).map fun final => (seed, final)
  have supported (pair : Seed × app.Execution) (member : pair ∈ staged.support) :
      pair.1 ∈ prior.support ∧ pair.2 ∈ (phase (execution pair.1)).support := by
    change pair ∈ (prior.bind fun seed =>
      (phase (execution seed)).map fun final => (seed, final)).support at member
    simp only [PMF.support_bind] at member
    obtain ⟨seed, present, later⟩ := Set.mem_iUnion₂.mp member
    obtain ⟨final, reached, equal⟩ := (PMF.mem_support_map_iff ..).mp later
    rw [← equal]
    exact ⟨present, reached⟩
  let nextPrior := pmfToSubtype staged (fun _ member => member)
  let nextExecution := fun pair : {pair // pair ∈ staged.support} => pair.val.2
  have nextGood : ∀ pair ∈ nextPrior.support, next (nextExecution pair) := by
    intro pair _
    obtain ⟨present, reached⟩ := supported pair.val pair.property
    exact endpoint _ (goods _ present) _ reached
  have nextJoint : nextPrior.map (fun pair => (point (nextExecution pair),
      traffic (nextExecution pair))) =
      ((prior.map fun seed => point (execution seed)).bind step).bind fun current =>
        (nextNoise (view current)).map fun extra => (current, extra) := by
    rw [map_pmfToSubtype staged (fun _ member => member)
      (fun pair => (point pair.2, traffic pair.2))]
    simpa only [staged, PMF.map_bind, PMF.map_comp, Function.comp_def] using phaseJoint
  have nextMarginal : nextPrior.map (fun pair => point (nextExecution pair)) =
      (prior.map fun seed => point (execution seed)).bind step := by
    have projected := congrArg (PMF.map Prod.fst) nextJoint
    simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, pmf_map_fun_const,
      PMF.bind_pure] using projected
  have nextFactor : nextPrior.map (fun pair => (point (nextExecution pair),
      traffic (nextExecution pair))) =
      (nextPrior.map fun pair => point (nextExecution pair)).bind fun current =>
        (nextNoise (view current)).map fun extra => (current, extra) := by
    rw [nextMarginal]
    exact nextJoint
  obtain ⟨policy, tailLaw⟩ := tail nextPrior nextExecution nextGood nextNoise nextFactor
  refine ⟨build policy, ?_⟩
  calc
    _ = staged.bind (fun pair =>
        (app.runToHorizon scheduler players horizon pair.2).map fun final =>
          read (point final)) := by
      simp only [staged, PMF.bind_bind, PMF.bind_map, Function.comp_def]
      apply bind_congr_on_support _
      intro seed present
      rw [markov _ (goods seed present), PMF.map_bind]
    _ = nextPrior.bind (fun pair =>
        (app.runToHorizon scheduler players horizon (nextExecution pair)).map fun final =>
          read (point final)) := by
      conv_lhs => rw [← map_val_pmfToSubtype staged (fun _ member => member)]
      rw [PMF.bind_map]
      rfl
    _ = nextPrior.bind (fun pair => target policy (point (nextExecution pair))) := tailLaw
    _ = (nextPrior.map fun pair => point (nextExecution pair)).bind (target policy) :=
      (PMF.bind_map _ _ _).symm
    _ = _ := by
      rw [nextMarginal, PMF.bind_bind, PMF.bind_map]
      apply bind_congr_on_support _
      intro seed _
      exact (targetStep policy _).symm


/-- **Frozen executions.** When the run from every execution keeps its read
point, and one policy's target is that point, the simulation holds. -/
theorem DeviationSimulation.of_frozen {good : app.Execution → Prop}
    (frozen : ∀ execution, good execution →
      (app.runToHorizon scheduler players horizon execution).map (fun final => read (point final)) =
        PMF.pure (read (point execution)))
    (policy : Policy)
    (settled : ∀ execution, good execution →
      target policy (point execution) = PMF.pure (read (point execution))) :
    DeviationSimulation scheduler players horizon read point traffic view target good := by
  intro Seed prior execution goods noise _
  refine ⟨policy, ?_⟩
  apply bind_congr_on_support _
  intro seed present
  rw [frozen _ (goods seed present), settled _ (goods seed present)]

end Vegas
