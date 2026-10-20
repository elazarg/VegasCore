/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ConcurrentRawSequentialPreservation
import Vegas.Examples.ReservedEpochCertifiedConcurrency
import Vegas.Examples.CommitTimingInformationAudit

/-! # Nonvacuity of the concurrent reserved-service hypotheses

The source and correlated two-order tape are the hidden-bit fixture.
This instance uses the contract's actual concurrent graph. The pending
packet demonstration additionally relaxes independent reveals; that graph is
not substituted for the graph named by the preservation contract.
-/

noncomputable section

namespace VegasTests.ConcurrentRawHypotheses

open Vegas Vegas.SourceProgram Vegas.EventGraph Vegas.EventGraphRuntime Interaction
  GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

abbrev Player := Vegas.Examples.CommitTimingInformation.Player
abbrev setup := Vegas.Examples.CommitTimingInformation.setup
abbrev graph := serviceGraph setup .concurrent

def runtime : EventGraphRuntime graph where
  deadline := fun _ => 7

def leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph) :=
  MessageNetwork.completePendingObservation

def plan : RuntimePhasePlan graph :=
  compiledRuntimePhasePlan Vegas.Examples.CommitTimingInformation.program .concurrent

def bounds : MessageBounds graph where
  candidateCount := ReservedEpoch.executionHorizon runtime
  values := Finset.univ.image fun bit : Bool => (⟨.bool, bit⟩ : Raw simpleExpr)

abbrev prior := Vegas.Examples.ReservedEpochConcurrency.prior

def bindingEvent (owner : Player) : graph.EventId :=
  ⟨owner.val, by have bound := owner.isLt; change owner.val < 4; omega⟩

theorem bindingLayout (owner : Player) :
    graph.outputLayout (bindingEvent owner) = .binding owner .bool := by
  fin_cases owner <;> rfl

theorem bindingEvent_injective : Function.Injective bindingEvent := by
  intro first second same
  apply Fin.ext
  exact congrArg (fun event : graph.EventId => event.val) same

theorem bindingPredecessors (owner : Player) :
    graph.order.predecessors (bindingEvent owner) = ∅ := by
  fin_cases owner <;> decide

theorem initialCurrent (inputs : graph.Inputs) :
    (PhaseRuntimeState.initial plan inputs).current =
      (⟨EventGraphRuntime.State.initial inputs, ∅⟩ : RecoveryState graph) := by
  classical
  let native := EventGraphRuntime.State.initial inputs
  cases phases : plan.phases with
  | nil => simp [PhaseRuntimeState.initial, phases, PhaseRuntimeState.settle]
  | cons phase remaining =>
      have drained : phase.drain (⟨native, ∅⟩ : RecoveryState graph) = ⟨native, ∅⟩ := by
        apply RuntimePhase.drain_eq_of_clear
        intro event eligible
        rcases eligible.2 with ⟨_ready, excluded⟩
        cases actor : graph.actor? event <;> simp [actor] at excluded
      have unfinished : ¬ phase.Finished (⟨native, ∅⟩ : RecoveryState graph) := by
        intro finished
        let event : graph.EventId :=
          ⟨phase.low, lt_of_lt_of_le phase.nonempty phase.bounded⟩
        have member := finished ((RuntimePhase.mem_events phase event).mpr
          ⟨le_rfl, phase.nonempty⟩)
        change event ∈ (EventOrder.Cut.empty graph.order).completed at member
        exact Finset.notMem_empty _ member
      change (PhaseRuntimeState.settle plan.phases 0 ⟨native, ∅⟩ ⟨native, ∅⟩ []).current = _
      simp only [phases, PhaseRuntimeState.settle, drained, unfinished, ↓reduceIte]
      rfl

/-- The actual contract graph permits both owned bindings at the same frontier. -/
theorem initialBindingsReady (inputs : graph.Inputs) (owner : Player) :
    (PhaseRuntimeState.initial plan inputs).current.native.config.cut.Ready
      (bindingEvent owner) := by
  rw [initialCurrent]
  constructor
  · exact Finset.notMem_empty _
  · intro predecessor present
    rw [bindingPredecessors] at present
    exact (Finset.notMem_empty _ present).elim

theorem outputValues : bounds.CoversOutputValues := by
  intro event
  fin_cases event <;>
    change ∀ bit : Bool, (⟨.bool, bit⟩ : Raw simpleExpr) ∈ bounds.values
  all_goals
    intro bit
    exact Finset.mem_image.mpr ⟨bit, Finset.mem_univ _, rfl⟩

theorem maximalPhases : plan.phases.IsChain (fun first last =>
    first.kind ≠ last.kind ∨ first.kind = .sample) :=
  compiledRuntimePhasePlan_maximal Vegas.Examples.CommitTimingInformation.program .concurrent

theorem boundedGaps : ∀ tape ∈ prior.support,
    tape.BoundedGaps (ReservedEpoch.completionCycles runtime) 1 2 := by
  intro tape supported
  exact Vegas.Examples.ReservedEpochConcurrency.supported_tape_boundedGaps tape supported _

theorem timely : runtime.AsyncTimely (fun _ => 1 + 1) (fun _ => 2 + 1) :=
  ReservedEpoch.asyncTimely runtime 1 2 (fun _ _ => by change 5 < 7; decide)

/-- Every authentic evidence item is observed and delivered at settlement. -/
def evidenceService : EvidenceReportService (PhaseCount.Evidence graph) where
  window := ⟨0, 0, 0, by omega⟩
  observations := PMF.pure
  reports := fun observed => PMF.pure (observed.map fun evidence => ⟨evidence, 0, 0⟩)
  observations_authentic := by
    intro actual observed supported
    cases (PMF.mem_support_pure_iff _ _).mp supported
    exact List.Subset.refl _
  reports_authentic := by
    intro observed delivered supported report member
    cases (PMF.mem_support_pure_iff _ _).mp supported
    obtain ⟨evidence, present, rfl⟩ := List.mem_map.mp member
    exact present
  reports_timelySubmitted := by
    intro observed delivered supported report member
    cases (PMF.mem_support_pure_iff _ _).mp supported
    obtain ⟨evidence, _, rfl⟩ := List.mem_map.mp member
    exact ⟨le_rfl, le_rfl⟩

theorem everyEvidenceDelivered (actual : List (PhaseCount.Evidence graph)) :
    evidenceService.sample actual = PMF.pure actual := by
  classical
  simp only [EvidenceReportService.sample, evidenceService, PMF.pure_bind, PMF.pure_map]
  congr 1
  induction actual with
  | nil => rfl
  | cons first rest ih =>
      simpa [EvidenceReport.deliveredEvidence] using congrArg (first :: ·) ih

theorem coverage :
    PhaseCount.EvidenceCoverage evidenceService (fun _ => 1) (fun _ => 1) := by
  classical
  intro actual report member _
  constructor
  · simp [evidenceService, PMF.toOuterMeasure_pure_apply, member]
  · intro seen supported present
    cases (PMF.mem_support_pure_iff _ _).mp supported
    have delivered : report ∈ EvidenceReport.deliveredEvidence 0
        (actual.map fun evidence => (⟨evidence, 0, 0⟩ : EvidenceReport _)) := by
      rcases report with ⟨left, right⟩
      simpa [EvidenceReport.deliveredEvidence, List.map_map, Function.comp_def] using
        (show ∃ a b, (a, b) ∈ actual ∧ (a, b) = (left, right) from
          ⟨left, right, present, rfl⟩)
    simp [evidenceService, PMF.toOuterMeasure_pure_apply, delivered]

abbrev utility := Vegas.Examples.CommitTimingInformation.utility

theorem utilityBounds (terminal : State simpleExpr setup.program.terminalCtx) (who : Player) :
    utility terminal who ∈ Set.Icc (-1 : ℝ) 1 :=
  Vegas.Examples.CommitTimingInformation.utility_mem_Icc terminal who

theorem nonconstantUtility :
    utility (Vegas.Examples.CommitTimingInformation.finalState false false true)
        Vegas.Examples.CommitTimingInformation.alice ≠
      utility (Vegas.Examples.CommitTimingInformation.finalState false true true)
        Vegas.Examples.CommitTimingInformation.alice := by
  dsimp only [utility]
  rw [(Vegas.Examples.CommitTimingInformation.utility_finalState false false true).1,
    (Vegas.Examples.CommitTimingInformation.utility_finalState false true true).1]
  norm_num

/-- A strictly positive deposit funds the entire nonconstant payoff range. -/
theorem fundedDeposit :
    max 0 (max (-1 : ℝ) 1) - min 0 (min (-1 : ℝ) (-1)) ≤
      (1 : ℝ) * 1 * 2 := by
  norm_num

/-- Both distinct owner orders have positive probability under the actual prior. -/
theorem bothOrders :
    Vegas.Examples.ReservedEpochConcurrency.tape false ∈ prior.support ∧
    Vegas.Examples.ReservedEpochConcurrency.tape true ∈ prior.support ∧
    (Vegas.Examples.ReservedEpochConcurrency.tape false).owner 0 0 ≠
      (Vegas.Examples.ReservedEpochConcurrency.tape true).owner 0 0 := by
  refine ⟨Vegas.Examples.ReservedEpochConcurrency.tape_supported false,
    Vegas.Examples.ReservedEpochConcurrency.tape_supported true, ?_⟩
  rw [Vegas.Examples.ReservedEpochConcurrency.tape_owner_first,
    Vegas.Examples.ReservedEpochConcurrency.tape_owner_first]
  decide

def implementation : ReservedConcurrentImplementation setup where
  runtime := runtime
  leaks := leaks
  bounds := bounds
  plan := plan
  tapeLength := 2
  prior := prior
  activationGap := 1
  processingGap := 2

def payoffData : ConcurrentPayoffs setup where
  utility := utility
  excludedPayoff := fun _ => -1
  lowerUtility := fun _ => -1
  upperUtility := fun _ => 1

def countAudit : ConcurrentCountAudit setup where
  service := evidenceService
  observationRate := fun _ => 1
  deliveryRate := fun _ => 1
  deposit := fun _ => 2

/-- All operational, payoff and funded-audit assumptions hold jointly. -/
theorem valid : implementation.Valid payoffData countAudit where
  operational :=
    { finiteInitial := inferInstance
      finiteBindings := Vegas.Examples.CommitTimingInformation.finiteBindingTypes
      wellFormed := Vegas.Examples.CommitTimingInformation.wellFormed
      completePending := rfl
      outputValues := outputValues
      maximalPhases := maximalPhases
      boundedGaps := boundedGaps
      timely := timely
      candidateReserve := le_rfl }
  payoffs :=
    { lower_le := fun terminal who => (utilityBounds terminal who).1
      le_upper := fun terminal who => (utilityBounds terminal who).2
      excluded_nonpositive := fun _ => by norm_num [payoffData]
      excluded_le := fun terminal who => (utilityBounds terminal who).1 }
  audit :=
    { delivery_nonnegative := fun _ => by norm_num [countAudit]
      coverage := coverage
      deposit_nonnegative := fun _ => by norm_num [countAudit]
      sufficient := fun _ => fundedDeposit }

/-- The intended source equilibrium assumption has a genuine witness too. -/
theorem sourceEquilibrium :
    ∃ source : setup.intendedModel.BehavioralAssessment,
      payoffData.SourceEquilibrium source := by
  exact Vegas.Examples.CommitTimingInformation.exists_honest_sequentialEquilibrium

end VegasTests.ConcurrentRawHypotheses
