module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ClientSpecification
public import Vegas.Game.IntendedHistory
public import Vegas.Game.SourceServiceChoiceSupport
public import Vegas.Game.ClientContinuation
public import Vegas.Game.OnePacketEquilibriumPreservation
public import Vegas.Game.OnePacketRawDistribution

@[expose] public section

/-! # Intended sequential equilibria in the audited native raw runtime

The actual bounded raw menu retains the source equilibrium's joint complete
configuration and settled payoff law. Sequential rationality covers whole
continuation policies in that supplied bounded menu. Supported play has no
public defaults and pays no count-audit charge.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability GameTheory.Enforcement
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts setup.informationGraph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
  {bounds : MessageBounds setup.informationGraph} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

local notation "Initial" => initialDistribution setup

variable {Parameter : Type} {parameter : State L setup.context → Parameter}
  {utility : Parameter × PublicOutcome setup.program → Player → ℝ}
  {excludedPayoff : Player → ℝ}

/-- The encoded initial law retains every source input, and the wire catalogue
covers every binding value. These two finiteness conditions bound the entire
intended history tree, including off-path decisions. -/
theorem ClientSpec.finiteSource
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff) : Finite setup.intendedProtocol.History := by
  have imageFinite := spec.finiteNature.initial_finite
  change ((setup.initialDistribution.map fun draw => EventGraphRuntime.State.initial
    (graph := setup.informationGraph) (setup.eventInputs draw)).support).Finite at imageFinite
  rw [PMF.support_map] at imageFinite
  have : setup.FiniteInitialSupport := ⟨imageFinite.of_finite_image (by
    intro x _ y _ same
    exact eventInputs_injective (congrArg
      (fun state : EventGraphRuntime.State setup.informationGraph => state.config.inputs) same))⟩
  have covered : bounds.CoversBindingValues := by
    intro event
    have allValues := spec.outputValues event
    cases layout : setup.informationGraph.outputLayout event <;>
      first | trivial | simpa only [layout] using allValues
  exact setup.intended_finite_history
    (sourceService_finiteBindingTypes setup (deps := setup.informationDependencies) bounds covered)

open Classical in
/-- An intended sequential equilibrium compiles to an actual native assessment
that is sequentially rational against every policy in the supplied bounded raw
menu and preserves the joint complete source configuration and settled payoff. -/
theorem intended_raw_sequentialEquilibrium_preserved
    (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
      parameter utility excludedPayoff)
    (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended) :
    Nonempty (ClientCompilation spec intended) := by
  let := spec.finiteNature
  let := spec.finiteSource
  obtain ⟨native, fidelity, nativeSE, nativeClear, nativeDistribution⟩ :=
    intended_onePacket_sequentialEquilibrium_preserved (timeouts := timeouts) parameter utility
      excludedPayoff spec.wellFormed spec.prior spec.opportunity
      spec.inclusion spec.completes spec.timely spec.exitBelow intended equilibrium
      spec.outputValues spec.inputValues spec.capacity
  obtain ⟨target, refinement, targetSE, clean, states, joint⟩ :=
    intended_raw_sequentialEquilibrium_of_onePacket (timeouts := timeouts) (initial := Initial)
      parameter utility excludedPayoff intended native nativeSE nativeDistribution
        spec.evidenceService
      spec.observationRate spec.deliveryRate spec.delivery_nonnegative spec.coverage
      spec.deposit spec.deposit_nonnegative spec.funded
  have fullSE := (target.isSequentialEquilibrium_iff_truncated_of_bounded _ _
    ((bounds.rawMenu timeouts leaks).bounded Initial horizon scheduler).wellFoundedHistories
    ((bounds.rawMenu timeouts leaks).bounded Initial horizon scheduler) _).mpr targetSE
  have fullNativeSE := (native.isSequentialEquilibrium_iff_truncated_of_bounded _ _
    ((bounds.onePacketMenu timeouts leaks).bounded Initial horizon scheduler).wellFoundedHistories
    ((bounds.onePacketMenu timeouts leaks).bounded Initial horizon scheduler) _).mpr nativeSE
  let assessmentRefinement : ClientAssessmentRefinement setup timeouts leaks bounds horizon
      scheduler intended target := ⟨native, fidelity, refinement,
    bounds.exists_raw_site_of_onePacket_site timeouts leaks Initial horizon scheduler,
    MessageBounds.ExtendsOnePacketAssessment.runFrom_history_map bounds timeouts leaks Initial
      horizon scheduler refinement⟩
  refine ⟨⟨target, assessmentRefinement, fullNativeSE, fullSE,
    assessmentRefinement.continuation_correct spec, ?_, clean, joint⟩⟩
  intro final supported control current
  let raw := bounds.rawMenu timeouts leaks
  let normalize := ((reactiveNormalization timeouts) leaks).state
  have represented : normalize final.state ∈
      (((raw.information Initial horizon scheduler).runBehavioral target.strategy
        (2 * horizon + 1)).map (fun history => normalize history.state)).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨final, supported, rfl⟩
  rw [states] at represented
  obtain ⟨original, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp represented
  rw [current] at same
  exact nativeClear original reached
    { control with execution :=
      ((reactiveNormalization timeouts) leaks).execution control.execution } same

end Vegas
