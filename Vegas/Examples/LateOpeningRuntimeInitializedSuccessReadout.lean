/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeInitializedTypeLikelihood
import Vegas.Examples.LateOpeningRuntimeSuccessPosterior

/-! # Actual initialized type groups and the receiver's label posterior

A successful public opening fixes the initialized bit throughout the entire
receiver information class. Filtering each actual hidden history by its
private label is therefore exactly the same as filtering its full immutable
initialized inputs by that public bit and the label. No belief support or
posterior formula is assumed.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeInitializedSuccessReadout

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeReadout LateOpeningRuntimeService
  LateOpeningRuntimeBindingPrefix LateOpeningRuntimeInitializedTypeLikelihood
  LateOpeningRuntimeBobSuccessInformation LateOpeningRuntimeBobSuccessPayoff
  LateOpeningRuntimeBobSuccessDecision LateOpeningRuntimeSuccessPosterior

variable (weight : ℝ) (nonnegative : 0 ≤ weight)
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1)
  (decision : DecisionHistory weight nonnegative)
  (current : representative.1.state = some ⟨14, some bob, decision.execution⟩)

include current in
/-- Every compatible legal history, including one with zero assessment belief,
retains the published initial bit and one of the actual three private labels. -/
theorem initialized_type_of_information
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1) :
    ∃ label : Fin 3,
      initializedInputs history.1.state =
          some (setup.eventInputs (sourceInitial decision.bit label)) ∧
        initializedLabel history.1.state = some label := by
  let recovered := decisionOfInformation weight nonnegative site representative decision
    current history
  have facts := decisionOfInformation_spec weight nonnegative site representative decision
    current history
  obtain ⟨bit, label, valid⟩ := history_initial_invariant LateOpeningRuntimeService.runtime leaks
    LateOpeningRuntimeService.horizon (LateOpeningRuntimeService.scheduler weight nonnegative)
      ⟨14, some bob, recovered.execution⟩ recovered.trace
  have publication : recovered.execution.application.config.store (.inr aliceEvent) =
      some (.success decision.bit : PublicationResult Bool) :=
    (LateOpeningRuntimeBobBindingInformation.alice_result_same_view _ _ facts.2.2).symm.trans
      decision.published
  have known := alice_success_from_initialized_bit recovered.execution.application bit label
    valid decision.bit publication
  refine ⟨label, ?_, ?_⟩
  · rw [initializedInputs, facts.1, Option.map_some]
    change some recovered.execution.application.config.inputs = _
    rw [valid.reachable.inputs_eq, ← known]
  · rw [initializedLabel, facts.1, Option.map_some]
    exact congrArg some (originalLabel_initialized recovered.execution bit label valid)

include current in
theorem initialized_inputs_iff_label
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory bob site.1)
    (label : Fin 3) :
    initializedInputs history.1.state =
        some (setup.eventInputs (sourceInitial decision.bit label)) ↔
      initializedLabel history.1.state = some label := by
  obtain ⟨actualLabel, inputs, actual⟩ := initialized_type_of_information weight nonnegative
    site representative decision current history
  rw [inputs, actual, Option.some.injEq, Option.some.injEq]
  constructor
  · intro equal
    have same : (decision.bit, actualLabel) = (decision.bit, label) :=
      input_parameter_injective equal
    exact congrArg Prod.snd same
  · intro equal
    rw [equal]

include current in
/-- The two groupings are equal as finite sets of actual complete raw histories. -/
theorem label_histories_eq_initialized_type (label : Fin 3) :
    readoutHistories weight nonnegative site initializedLabel (some label) =
      readoutHistories weight nonnegative site initializedInputs
        (some (setup.eventInputs (sourceInitial decision.bit label))) := by
  classical
  ext history
  simp only [readoutHistories, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (initialized_inputs_iff_label weight nonnegative site representative decision current
    history label).symm

theorem label_mass_eq_initialized_type
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (label : Fin 3) :
    labelMass weight nonnegative site representative decision current assessment label =
      InformationModel.finiteHistoryBelief assessment bob site
        (readoutHistories weight nonnegative site initializedInputs
          (some (setup.eventInputs (sourceInitial decision.bit label)))) := by
  rw [label_mass_eq_readout weight nonnegative site representative decision current]
  unfold LateOpeningRuntimeBindingPosterior.readoutBelief
  rw [label_histories_eq_initialized_type weight nonnegative site representative decision current]

end Vegas.Examples.LateOpeningRuntimeInitializedSuccessReadout
