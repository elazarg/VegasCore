/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseOpeningBindingPrefix
import Vegas.Game.PhaseSourceResponseLaw

/-! # Earlier opening waits in prefixes ending at a clear binding callback -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- In a prefix that actually reaches a clear binding callback, an earlier
unsent opening callback has no prescribed WAIT mass. Its complete WAIT atom
is exactly the raw-noise weight times the actual counted uniform-menu atom.
The uniform menus are not identified with each other. -/
theorem phaseSourcePerturbedStrategy_opening_wait_before_binding
    (wellFormed : setup.WellFormed) (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (before after : (app).Control)
    (beforeTrace : (E).Trace (some before)) (afterTrace : (E).Trace (some after))
    (isPrefix : TracePrefix beforeTrace afterTrace)
    (clear : after.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    (request : before.execution.application.SeedRequest owner
      ⟨before.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (before.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨before.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (bindingEvent : (serviceGraph setup mode).EventId) (bindingOwner : Player)
    (bindingPayload : L.Ty)
    (bindingOutput : (serviceGraph setup mode).outputLayout bindingEvent =
      .binding bindingOwner bindingPayload)
    (requested : after.execution.application.SeedRequest bindingOwner
      ⟨after.execution.application.attempt, bindingEvent⟩)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (choice : (N).Choice owner (some (before.execution.recall owner,
      before.execution.observe app owner))) (selected : choice.1 = some ⟨none⟩) :
    let input := some (before.execution.recall owner, before.execution.observe app owner)
    let main := mix slotWeight slotNonnegative slotBounded
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler owner input)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler owner input)
    main choice = 0 ∧
      ((phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
        wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded owner input) choice).toReal =
        noise * (((PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy initial horizon
          scheduler owner input) choice).toReal := by
  intro input main
  obtain ⟨value, stored⟩ := phase_opening_binding_success_before_binding runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler before after
      beforeTrace afterTrace isPrefix clear event owner payload binding checks outputEq codeEq node
        request.2.2.1 bindingEvent bindingOwner bindingPayload bindingOutput requested
  obtain ⟨candidate, accepted, canonical⟩ := phaseSourcePolicy_opening_of_history setup mode runtime
    leaks bounds wellFormed assessment plan inputs horizon scheduler beforeTrace owner event payload
      binding checks outputEq codeEq node request unsent value stored (values value)
  obtain ⟨other, otherAccepted, slots⟩ := phaseSourceSlotPolicy_opening_of_history setup mode
    runtime
    leaks bounds wellFormed assessment plan inputs horizon scheduler beforeTrace owner event payload
      binding checks outputEq codeEq node request unsent value stored (values value)
  have same : other = candidate := Option.some.inj (otherAccepted.symm.trans accepted)
  subst other
  have projection : main.map Subtype.val =
      (PMF.pure (PhaseCount.phaseOpeningResponse runtime leaks event candidate ⟨payload,
    value⟩)).map
        some := by
    dsimp only [main, input]
    rw [mix_map, phaseSourceSlotStrategy_map_val, phaseSourceStrategy_map_val, canonical, slots]
    rw [mix_self]
  have absent : main choice = 0 := by
    rw [← pmf_map_apply_of_injective main Subtype.val_injective choice, projection, selected]
    simp [PhaseCount.phaseOpeningResponse]
  refine ⟨absent, ?_⟩
  change (mix noise noiseNonnegative noiseBounded _ main choice).toReal = _
  rw [mix_apply_toReal, absent, ENNReal.toReal_zero, mul_zero, add_zero]

end Vegas
