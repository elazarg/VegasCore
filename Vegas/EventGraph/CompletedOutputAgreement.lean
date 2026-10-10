/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Execution

/-! # Retained semantic outputs through physical settlement -/

noncomputable section
namespace Vegas.EventGraph.Config
open GameTheory.Math.Probability
variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The semantic frontier has retained every output already physically settled. -/
def CompletedOutputAgreement (physical frontier : graph.Config) : Prop :=
  ∀ event ∈ physical.cut.completed, physical.outputs event = frontier.outputs event

theorem CompletedOutputAgreement.refl (config : graph.Config) :
    config.CompletedOutputAgreement config := fun _ _ => rfl

theorem CompletedOutputAgreement.frontier_step
    (physical frontier next : graph.Config)
    (agreement : physical.CompletedOutputAgreement frontier)
    (event : graph.EventId) (ready : frontier.cut.Ready event)
    (action : graph.Action event)
    (supported : next ∈ (frontier.step event ready action).support) :
    physical.CompletedOutputAgreement next := by
  intro query completed
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
    ((physical.output_available query).mpr completed)
  have frontierStored : frontier.store (.inr query) = some value :=
    (agreement query completed).symm.trans stored
  exact stored.trans
    (frontier.step_store_of_some next event ready action supported (.inr query)
      value frontierStored).symm

theorem CompletedOutputAgreement.physical_step
    (physical frontier next : graph.Config)
    (agreement : physical.CompletedOutputAgreement frontier)
    (event : graph.EventId) (ready : physical.cut.Ready event)
    (action : graph.Action event)
    (supported : next ∈ (physical.step event ready action).support)
    (settled : next.outputs event = frontier.outputs event) :
    next.CompletedOutputAgreement frontier := by
  intro query completed
  rw [physical.step_cut event ready action next supported,
    EventOrder.Cut.mem_complete] at completed
  rcases completed with same | old
  · subst query
    exact settled
  · obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp
      ((physical.output_available query).mpr old)
    exact (physical.step_store_of_some next event ready action supported
      (.inr query) value stored).trans
        (stored.symm.trans (agreement query old))
theorem CompletedOutputAgreement.completed_subset
    (physical frontier : graph.Config)
    (agreement : physical.CompletedOutputAgreement frontier) :
    physical.cut.completed ⊆ frontier.cut.completed := by
  intro event completed
  apply (frontier.output_available event).mp
  rw [← agreement event completed]
  exact (physical.output_available event).mpr completed

theorem CompletedOutputAgreement.terminal
    (physical frontier : graph.Config)
    (agreement : physical.CompletedOutputAgreement frontier)
    (terminal : physical.cut.Terminal) : frontier.cut.Terminal := by
  apply Finset.eq_univ_of_forall
  intro event
  exact (CompletedOutputAgreement.completed_subset physical frontier agreement)
    (by rw [terminal]; exact Finset.mem_univ event)

/-- Physical completion turns retained sampled outputs into equality of full stores. -/
theorem CompletedOutputAgreement.terminal_store
    (physical frontier : graph.Config)
    (agreement : physical.CompletedOutputAgreement frontier)
    (inputs : physical.inputs = frontier.inputs)
    (terminal : physical.cut.Terminal) : physical.store = frontier.store := by
  funext field
  cases field with
  | inl input => exact congrArg (fun values : graph.Inputs => some (values input)) inputs
  | inr event => exact agreement event (by rw [terminal]; exact Finset.mem_univ event)

/-- Retained physical outputs determine every physically available field. -/
theorem CompletedOutputAgreement.store_eq_of_available
    (physical frontier : graph.Config)
    (agreement : physical.CompletedOutputAgreement frontier)
    (inputs : physical.inputs = frontier.inputs)
    (field : graph.Field) (available : (physical.store field).isSome) :
    physical.store field = frontier.store field := by
  cases field with
  | inl input => exact congrArg (fun values : graph.Inputs => some (values input)) inputs
  | inr event => exact agreement event ((physical.output_available event).mp available)

/-- Every physically ready event evaluates identically in the sampled frontier,
including chance events and private read fields. -/
theorem CompletedOutputAgreement.ready_eval
    (physical frontier : graph.Config)
    (agreement : physical.CompletedOutputAgreement frontier)
    (inputs : physical.inputs = frontier.inputs)
    (event : graph.EventId) (ready : physical.cut.Ready event)
    (action : graph.Action event) :
    (graph.nodes event).eval? action physical.store =
      (graph.nodes event).eval? action frontier.store := by
  exact EventCode.eval?_congr (graph.nodes event) action _ _
    (fun field member => CompletedOutputAgreement.store_eq_of_available physical frontier
      agreement inputs field (physical.read_available ready member))

/-- Couple the actual and semantic frontier completions through their identical
ready-event evaluator, retaining the full chance law. -/
theorem CompletedOutputAgreement.coupled_step
    (physical frontier : graph.Config)
    (agreement : physical.CompletedOutputAgreement frontier)
    (inputs : physical.inputs = frontier.inputs)
    (event : graph.EventId) (ready : physical.cut.Ready event)
    (frontierReady : frontier.cut.Ready event) (action : graph.Action event) :
    ∃ joint : PMF (graph.Config × graph.Config),
      joint.map Prod.fst = physical.step event ready action ∧
      joint.map Prod.snd = frontier.step event frontierReady action ∧
      ∀ pair ∈ joint.support, pair.1.CompletedOutputAgreement pair.2 ∧
        pair.1.inputs = pair.2.inputs := by
  obtain ⟨law, evaluates⟩ := Option.isSome_iff_exists.mp
    (EventCode.eval?_isSome_of_reads (graph.nodes event) action physical.store
      (fun _ read => physical.read_available ready read))
  have frontierEval : (graph.nodes event).eval? action frontier.store = some law :=
    (CompletedOutputAgreement.ready_eval physical frontier agreement inputs event ready
      action).symm.trans evaluates
  refine ⟨law.map (fun value => (physical.complete event ready action value,
    frontier.complete event frontierReady action value)), ?_, ?_, ?_⟩
  · rw [PMF.map_comp, physical.step_eq_map_of_eval event ready action law evaluates]
    rfl
  · rw [PMF.map_comp, frontier.step_eq_map_of_eval event frontierReady action law frontierEval]
    rfl
  · intro pair member
    rw [PMF.support_map] at member
    obtain ⟨value, supported, rfl⟩ := member
    have physicalStep : physical.complete event ready action value ∈
        (physical.step event ready action).support := by
      rw [physical.step_eq_map_of_eval event ready action law evaluates, PMF.support_map]
      exact ⟨value, supported, rfl⟩
    have frontierStep : frontier.complete event frontierReady action value ∈
        (frontier.step event frontierReady action).support := by
      rw [frontier.step_eq_map_of_eval event frontierReady action law frontierEval, PMF.support_map]
      exact ⟨value, supported, rfl⟩
    refine ⟨?_, inputs⟩
    apply CompletedOutputAgreement.physical_step physical
      (frontier.complete event frontierReady action value)
      (physical.complete event ready action value)
      (CompletedOutputAgreement.frontier_step physical frontier
        (frontier.complete event frontierReady action value) agreement event frontierReady action
          frontierStep) event ready action physicalStep
    simp

end Vegas.EventGraph.Config
