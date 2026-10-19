/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowHistory
import Vegas.Game.PhaseProposalRepairChance

/-! # Designated-owner repair inside the exact native information fiber -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "model" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds)
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler

/-- The whole initialized repair remains in the observer's ENTIRE native
information fiber. It retains every non-designated own-action word, the literal
initial draw, physical network and old public failure/proposal controls. -/
theorem repair_information_history
    (covered : bounds.CoversOutputValues) (ordered : graph.RevealRelaxedOrdered)
    (owner observer : Player) (different : observer ≠ owner)
    (site : (model).InformationSite observer)
    (history : (model).InformationHistory observer site.1) :
    ∃ image : (model).InformationHistory observer site.1,
      (∀ who, who ≠ owner →
        (model).ownPlay who history.val.trace = (model).ownPlay who image.val.trace) ∧
      ∃ (original imageControl : (app).Control), history.val.state = some original ∧
        image.val.state = some imageControl ∧
        original.actor = some observer ∧ imageControl.actor = some observer ∧
        original.execution.application.current.native.config.inputs =
          imageControl.execution.application.current.native.config.inputs ∧
        phaseExternalObservation runtime leaks owner original.execution =
          phaseExternalObservation runtime leaks owner imageControl.execution ∧
        BindingShadow.PreparedBindings runtime leaks owner original.execution
          imageControl.execution := by
  have present : site.1 ≠ none := by
    intro absent
    obtain ⟨_history, _running, action, offered⟩ := site.property
    rw [absent] at offered
    change some action = none at offered
    cases offered
  rcases history with ⟨⟨state, trace⟩, observed⟩
  change ((menu).signals initial horizon scheduler).infoOf observer trace = site.1 at observed
  rw [(menu).info] at observed
  cases state with
  | none => exact (present observed.symm).elim
  | some original =>
      have active : original.actor = some observer := by
        by_contra inactive
        change (if original.actor = some observer then _ else none) = site.1 at observed
        rw [ite_eq_right inactive] at observed
        exact present observed.symm
      obtain ⟨memory, execution, imageTrace, _frame, prepared, external, immutable, words⟩ :=
        BindingShadow.repair_counted_history_ownPlay runtime leaks bounds covered plan ordered
          inputs horizon scheduler owner original trace
      let imageControl : (app).Control := ⟨original.remaining, original.actor, execution⟩
      have outside := congrFun (congrArg (fun view => view.2.2.2.2) external) observer
      change (if observer = owner then none else
        some (original.execution.recall observer, original.execution.observe app observer)) =
          (if observer = owner then none else
            some (execution.recall observer, execution.observe app observer)) at outside
      rw [ite_eq_right different, ite_eq_right different] at outside
      have imageInfo : (model).infoOf observer imageTrace = site.1 := by
        change ((menu).signals initial horizon scheduler).infoOf observer imageTrace = _
        rw [(menu).info]
        change (if original.actor = some observer then _ else none) = _
        rw [ite_eq_left active, ← outside]
        simpa only [ReactiveApplication.observe, active, ite_true] using observed
      refine ⟨⟨⟨some imageControl, imageTrace⟩, imageInfo⟩, words, original, imageControl,
        rfl, rfl, active, active, immutable, external, prepared⟩

end Vegas.EventGraphRuntime.PhaseProposal
