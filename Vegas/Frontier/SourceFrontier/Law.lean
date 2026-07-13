/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Machine.Adapter.RoundView

/-!
# Source/frontier block law facts

The law side of the proof decomposes a one-shot frontier legal-action PMF into
source-order choices.  The first source query samples a projection of the
frontier action; the conditioned remainder remains in that projection fiber.
-/

namespace Vegas

namespace SourceFrontier
namespace Law

open GameTheory

variable {Player : Type} [Fintype Player] {L : IExpr}

/-- Frontier legal-action laws disintegrate by any finite projection. -/
theorem legalActionLaw_disintegrate
    {M : Machine Player} (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    {β : Type} [Finite β]
    (project : view.BoundedLegalAction horizon h.lastState → β) :
    view.legalActionLaw horizon σ h hterm =
      (Math.ProbabilityMassFunction.pushforward
          (view.legalActionLaw horizon σ h hterm) project).bind
        (fun value =>
          Math.ProbabilityMassFunction.condOn
            (view.legalActionLaw horizon σ h hterm) project value) :=
  Machine.RoundView.legalActionLaw_disintegrate
    view horizon σ h hterm project

/-- Frontier legal-action laws disintegrate by two successive finite
projections. -/
theorem legalActionLaw_disintegrate_two
    {M : Machine Player} (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    {β γ : Type} [Finite β] [Finite γ]
    (first : view.BoundedLegalAction horizon h.lastState → β)
    (second : view.BoundedLegalAction horizon h.lastState → γ) :
    view.legalActionLaw horizon σ h hterm =
      (Math.ProbabilityMassFunction.pushforward
          (view.legalActionLaw horizon σ h hterm) first).bind
        (fun firstValue =>
          (Math.ProbabilityMassFunction.pushforward
              (Math.ProbabilityMassFunction.condOn
                (view.legalActionLaw horizon σ h hterm) first firstValue)
              second).bind
            (fun secondValue =>
              Math.ProbabilityMassFunction.condOn
                (Math.ProbabilityMassFunction.condOn
                  (view.legalActionLaw horizon σ h hterm) first firstValue)
                second secondValue)) :=
  Machine.RoundView.legalActionLaw_disintegrate_two
    view horizon σ h hterm first second

/-- Frontier legal-action laws disintegrate by any finite list of projections.

This is the same-round serialization law used to consume one simultaneous
frontier action through a source-order block of commit queries. -/
theorem legalActionLaw_disintegrate_list
    {M : Machine Player} (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    (projections :
      List
        (Math.ProbabilityMassFunction.FiniteProjection
          (view.BoundedLegalAction horizon h.lastState))) :
    view.legalActionLaw horizon σ h hterm =
      Math.ProbabilityMassFunction.iterCondOn
        (view.legalActionLaw horizon σ h hterm) projections :=
  Math.ProbabilityMassFunction.bind_pushforward_condOn_pure_list
    (view.legalActionLaw horizon σ h hterm) projections

/-- Iterated source-order conditioning of one frontier legal-action law never
creates an action outside the original frontier legal-action support. -/
theorem legalActionLaw_iterCondOn_support_subset
    {M : Machine Player} (view : M.RoundView) (horizon : Nat)
    [∀ player, Fintype (Option (view.Act player))]
    (σ : view.BoundedBehavioralProfile horizon)
    (h : view.BoundedHistory horizon)
    (hterm : ¬ view.boundedTerminal horizon h.lastState)
    (projections :
      List
        (Math.ProbabilityMassFunction.FiniteProjection
          (view.BoundedLegalAction horizon h.lastState))) :
    (Math.ProbabilityMassFunction.iterCondOn
        (view.legalActionLaw horizon σ h hterm) projections).support ⊆
      (view.legalActionLaw horizon σ h hterm).support :=
  Math.ProbabilityMassFunction.iterCondOn_support_subset
    (view.legalActionLaw horizon σ h hterm) projections

variable [DecidableEq Player]

/-- A conditioned frontier node-value law only supports legal actions that
commit the sampled node value. -/
theorem conditioned_nodeValue_commitAvailable
    {G : EventGraph.Graph Player L}
    (spec : EventGraph.ToMachine.GraphMachineSpec G)
    (presentation : EventGraph.CheckpointPresentation G)
    (semantics : EventGraph.FrontierRoundSemantics spec presentation)
    {horizon : Nat}
    [∀ player,
      Fintype
        (Option
          ((EventGraph.frontierRoundView spec presentation semantics).Act
            player))]
    (σ :
      Machine.RoundView.BoundedBehavioralProfile
        (EventGraph.frontierRoundView spec presentation semantics) horizon)
    (h :
      Machine.RoundView.BoundedHistory
        (EventGraph.frontierRoundView spec presentation semantics) horizon)
    (hterm :
      ¬ Machine.RoundView.boundedTerminal
          (EventGraph.frontierRoundView spec presentation semantics)
          horizon h.lastState)
    {who : Player} {node : Fin G.nodeCount}
    (value : L.Val (G.nodeRow node).ty)
    {action :
      Machine.RoundView.BoundedLegalAction
        (EventGraph.frontierRoundView spec presentation semantics)
        horizon h.lastState}
    (hvalueMass :
      Math.ProbabilityMassFunction.pushforward
          (Machine.RoundView.legalActionLaw
            (EventGraph.frontierRoundView spec presentation semantics)
            horizon σ h hterm)
          (fun action :
              Machine.RoundView.BoundedLegalAction
                (EventGraph.frontierRoundView spec presentation semantics)
                horizon h.lastState =>
            match action.1 who with
            | some frontierAction => frontierAction.value? node
            | none => none)
          (some value) ≠ 0)
    (hactionSupport :
      action ∈
        (Math.ProbabilityMassFunction.condOn
          (Machine.RoundView.legalActionLaw
            (EventGraph.frontierRoundView spec presentation semantics)
            horizon σ h hterm)
          (fun action :
              Machine.RoundView.BoundedLegalAction
                (EventGraph.frontierRoundView spec presentation semantics)
                horizon h.lastState =>
            match action.1 who with
            | some frontierAction => frontierAction.value? node
            | none => none)
          (some value)).support) :
    EventGraph.CommitAvailable G h.lastState.state.1 who
      { node := node, value := G.nodeTypedValue node value } := by
  let view := EventGraph.frontierRoundView spec presentation semantics
  let project :
      Machine.RoundView.BoundedLegalAction view horizon h.lastState →
        Option (L.Val (G.nodeRow node).ty) :=
    fun action =>
      match action.1 who with
      | some frontierAction => frontierAction.value? node
      | none => none
  have hvalueMass' :
      Math.ProbabilityMassFunction.pushforward
          (Machine.RoundView.legalActionLaw view horizon σ h hterm)
          project (some value) ≠ 0 := by
    exact hvalueMass
  have hactionSupport' :
      action ∈
        (Math.ProbabilityMassFunction.condOn
          (Machine.RoundView.legalActionLaw view horizon σ h hterm)
          project (some value)).support := by
    exact hactionSupport
  have hproject : project action = some value :=
    Machine.RoundView.legalActionLaw_condOn_support_project
      view horizon σ h hterm project (some value)
      hvalueMass' hactionSupport'
  dsimp [project] at hproject
  cases hmove : action.1 who with
  | none =>
      simp [hmove] at hproject
  | some frontierAction =>
      have hnodeValue : frontierAction.value? node = some value := by
        simpa [hmove] using hproject
      exact
        EventGraph.frontierRoundView_commitAvailable_of_boundedLegal_value
          spec presentation semantics hterm hmove hnodeValue

end Law
end SourceFrontier

end Vegas
