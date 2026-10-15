/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseOpeningWaitingLaw
import Vegas.Pending.PhaseOpeningMenuSymmetry
import Interaction.ReactiveUniformMenu

/-! # Exact opening response factors before a clear binding endpoint -/

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

/-- Directed repair preserves the entire opening response law at earlier
callbacks of a prefix ending at a clear binding request. Actual phase barriers
provide the successful binding; actual counted-menu equality also preserves
the raw-noise tier, including every evidence alias. -/
theorem phaseSourcePerturbedStrategy_opening_raw_eq_before_binding
    (wellFormed : setup.WellFormed) (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (owner : Player) (remaining : Nat) (original repaired : (app).Execution)
    (memory : BindingMemory runtime (PhaseBindingRepair.nativeLeaks (graph := serviceGraph setup
      mode)))
    (frame : PhaseBindingRepair.Frame runtime leaks memory owner original repaired)
    (leftTrace : (E).Trace (some ⟨remaining, some owner, original⟩))
    (rightTrace : (E).Trace (some ⟨remaining, some owner, repaired⟩))
    (final : (app).Control) (finalTrace : (E).Trace (some final))
    (isPrefix : TracePrefix leftTrace finalTrace)
    (clear : final.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    (leftRequest : original.application.SeedRequest owner ⟨original.application.attempt, event⟩)
    (rightRequest : repaired.application.SeedRequest owner ⟨repaired.application.attempt, event⟩)
    (leftUnsent : ∀ message ∈ (app).outputs (original.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨original.application.attempt, event⟩)
    (rightUnsent : ∀ message ∈ (app).outputs (repaired.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨repaired.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (bindingEvent : (serviceGraph setup mode).EventId) (bindingOwner : Player)
    (bindingPayload : L.Ty)
    (bindingOutput : (serviceGraph setup mode).outputLayout bindingEvent =
      .binding bindingOwner bindingPayload)
    (requested : final.execution.application.SeedRequest bindingOwner
      ⟨final.execution.application.attempt, bindingEvent⟩)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1) :
    let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
        slotNonnegative slotBounded
    let firstInput := some (original.recall owner, original.observe app owner)
    let secondInput := some (repaired.recall owner, repaired.observe app owner)
    (strategy owner firstInput).map Subtype.val = (strategy owner secondInput).map Subtype.val ∧
      ∀ (first : (N).Choice owner firstInput) (second : (N).Choice owner secondInput),
        first.1 = second.1 → strategy owner firstInput first = strategy owner secondInput
      second := by
  intro strategy firstInput secondInput
  have ordered := serviceGraph_revealRelaxedOrdered setup mode
  obtain ⟨value, successful⟩ := phase_opening_binding_success_before_binding runtime leaks bounds
    plan ordered maximal inputs horizon scheduler _ final leftTrace finalTrace isPrefix clear
      event owner payload binding checks outputEq codeEq node leftRequest.2.2.1 bindingEvent
        bindingOwner bindingPayload bindingOutput requested
  have rawLeft := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler leftTrace
  have rawRight := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler rightTrace
  have leftBinding := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler rawLeft
  have rightBinding := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler
      rawRight
  obtain ⟨imageStored, candidate, leftAccepted, rightAccepted, _owned, _leftFixed, _rightFixed⟩ :=
    frame.live.successful_opening leftBinding.active rightBinding.active binding value successful
  have menus := frame.opening_menu_eq bounds plan ordered inputs horizon scheduler remaining
    leftTrace rightTrace event payload binding checks outputEq codeEq node leftRequest rightRequest
      value successful
  have uniform := (PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy_map_eq_of_actions
    initial horizon scheduler owner (original.recall owner) (repaired.recall owner)
      (original.observe app owner) (repaired.observe app owner) menus
  obtain ⟨first, firstAccepted, firstLaw⟩ := phaseSourcePolicy_opening_of_history setup mode runtime
    leaks bounds wellFormed assessment plan inputs horizon scheduler leftTrace owner event payload
      binding checks outputEq codeEq node leftRequest leftUnsent value successful (values value)
  obtain ⟨second, secondAccepted, secondLaw⟩ := phaseSourcePolicy_opening_of_history setup mode
    runtime leaks bounds wellFormed assessment plan inputs horizon scheduler rightTrace owner event
      payload binding checks outputEq codeEq node rightRequest rightUnsent value imageStored
        (values value)
  obtain ⟨firstSlot, firstSlotAccepted, firstSlotLaw⟩ := phaseSourceSlotPolicy_opening_of_history
    setup mode runtime leaks bounds wellFormed assessment plan inputs horizon scheduler leftTrace
      owner event payload binding checks outputEq codeEq node leftRequest leftUnsent value
        successful (values value)
  obtain ⟨secondSlot, secondSlotAccepted, secondSlotLaw⟩ := phaseSourceSlotPolicy_opening_of_history
    setup mode runtime leaks bounds wellFormed assessment plan inputs horizon scheduler rightTrace
      owner event payload binding checks outputEq codeEq node rightRequest rightUnsent value
        imageStored (values value)
  have firstEq : first = candidate := Option.some.inj (firstAccepted.symm.trans leftAccepted)
  have secondEq : second = candidate := Option.some.inj (secondAccepted.symm.trans rightAccepted)
  have firstSlotEq : firstSlot = candidate :=
    Option.some.inj (firstSlotAccepted.symm.trans leftAccepted)
  have secondSlotEq : secondSlot = candidate :=
    Option.some.inj (secondSlotAccepted.symm.trans rightAccepted)
  subst first
  subst second
  subst firstSlot
  subst secondSlot
  have laws : (strategy owner firstInput).map Subtype.val =
      (strategy owner secondInput).map Subtype.val := by
    dsimp only [strategy, firstInput, secondInput, phaseSourcePerturbedStrategy]
    rw [mix_map, mix_map, mix_map, mix_map, uniform,
      phaseSourceSlotStrategy_map_val, phaseSourceStrategy_map_val,
      phaseSourceSlotStrategy_map_val, phaseSourceStrategy_map_val,
      firstLaw, secondLaw, firstSlotLaw, secondSlotLaw]
  refine ⟨laws, ?_⟩
  intro first second same
  have firstAtom := pmf_map_apply_of_injective (strategy owner firstInput)
    Subtype.val_injective first
  have secondAtom := pmf_map_apply_of_injective (strategy owner secondInput)
    Subtype.val_injective second
  exact firstAtom.symm.trans ((congrArg (fun law => law first.1) laws).trans
    ((congrArg (fun action => ((strategy owner secondInput).map Subtype.val) action) same).trans
      secondAtom))

end Vegas
