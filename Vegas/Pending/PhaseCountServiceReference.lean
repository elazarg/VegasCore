/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingEncodingLaw
import Interaction.ReactivePolicyMixture
import Vegas.Pending.PhaseBindingSlotHistory
import Vegas.Pending.PhaseBindingMenuShape
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Normalized local binding service with a separate counted send tier -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks

open Classical in
/-- Only the conditional encoder is uniform. Silence is not one of its atoms. -/
def countedSends (owner : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) : Finset (app).Action :=
  (onePacketActions runtime leaks bounds owner past view).filter fun response =>
    response.transmission.isSome

open Classical in
/-- Outside actual ready inputs the encoder waits if no counted send exists. -/
def countedSendLaw (owner : Player) : (app).Policy := fun past view =>
  if nonempty : (countedSends runtime leaks bounds owner past view).Nonempty then
    PMF.uniformOfFinset _ nonempty
  else PMF.pure ⟨none⟩

theorem countedSendLaw_covered (owner : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈ (countedSendLaw runtime leaks bounds owner past view).support) :
    response ∈ onePacketActions runtime leaks bounds owner past view := by
  classical
  unfold countedSendLaw at supported
  split at supported
  · exact (Finset.mem_filter.mp ((PMF.mem_support_uniformOfFinset_iff ..).mp supported)).1
  · cases (PMF.mem_support_pure_iff ..).mp supported
    exact silence_onePacket runtime leaks bounds owner past view

/-- At an eligible callback, encoding has unit SEND mass regardless of the
number of raw aliases or of the prepared private result. -/
theorem countedSendLaw_transmission (owner : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView)
    (nonempty : (countedSends runtime leaks bounds owner past view).Nonempty) :
    (countedSendLaw runtime leaks bounds owner past view).map
        (fun response => response.transmission.isSome) = PMF.pure true := by
  classical
  rw [countedSendLaw, dite_eq_left nonempty]
  calc
    _ = (PMF.uniformOfFinset _ nonempty).map (fun _ => true) := by
      apply map_congr_on_support
      intro response supported
      exact (Finset.mem_filter.mp
        ((PMF.mem_support_uniformOfFinset_iff ..).mp supported)).2
    _ = _ := PMF.map_const _ _

/-- Every real exploration SEND is a fresh binding at the actual requested
event, including histories after a different owner has been excluded. -/
theorem countedSendLaw_binding_of_history (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (payload : L.Ty)
    (output : graph.outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (material : WitnessedSubmission graph)
    (supported : (⟨some material⟩ : (app).Action) ∈
      (countedSendLaw runtime leaks bounds owner (execution.recall owner)
        (execution.observe (app) owner)).support) :
    ∃ serial preparation evidence,
      material = ⟨⟨.commitment event (owner, .prepared serial), preparation⟩, evidence⟩ ∧
      serial < bounds.candidateCount ∧
      execution.application.current.native.candidates.lookup (owner, .prepared serial) =
        .fresh := by
  exact onePacket_binding_shape runtime leaks bounds plan ordered inputs horizon scheduler
    remaining owner execution trace event payload output request material
      (countedSendLaw_covered runtime leaks bounds owner _ _ _ supported)

/-- The original typed-result draw is followed by an independent fresh-slot draw.
The canonical allocator handles the complementary slot component. -/
def bindingResultEncoder (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView → PMF (PublicationResult (L.Val payload)))
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1) :
    (app).Policy := fun past view =>
  mix slotWeight slotNonnegative slotBounded
    (phaseBindingSlotPolicy runtime leaks bounds owner event payload
      values past view)
    (phaseBindingPolicy runtime leaks bounds owner event payload
      values past view)

theorem bindingResultEncoder_covered (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView → PMF (PublicationResult (L.Val payload)))
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈ (bindingResultEncoder runtime leaks bounds owner event payload values
      slotWeight slotNonnegative slotBounded past view).support) :
    response ∈ onePacketActions runtime leaks bounds owner past view := by
  rcases support_mix_subset _ _ _ _ _ supported with first | second
  · exact phaseBindingSlotPolicy_covered runtime leaks bounds owner event payload _ _ _ _ first
  · exact phaseBindingPolicy_covered runtime leaks bounds owner event payload _ _ _ _ second

/-- The source failure parameter occurs only in the first-clock branch.
All other probabilities depend solely on the current local timing decision. -/
def bindingServiceEmissionLaw (clocks : List Nat) (choose : List Nat → Bool)
    (failure timing : ℝ) (firstNonnegative : 0 ≤ failure + timing)
    (firstBounded : failure + timing ≤ 1) (timingNonnegative : 0 ≤ timing)
    (timingBounded : timing ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1) : PMF Bool :=
  mix rawWeight rawNonnegative rawBounded (PMF.pure true)
    (if clocks.length = 1 then
      mix (failure + timing) firstNonnegative firstBounded (PMF.pure false) (PMF.pure true)
    else if choose clocks then
      mix timing timingNonnegative timingBounded (PMF.pure false) (PMF.pure true)
    else mix timing timingNonnegative timingBounded (PMF.pure true) (PMF.pure false))

/-- The actual total SEND atom has no raw-menu cardinality or source-value
factor. The original source failure parameter is absent at every later record. -/
theorem bindingServiceEmissionLaw_send (clocks : List Nat) (choose : List Nat → Bool)
    (failure timing : ℝ) (firstNonnegative : 0 ≤ failure + timing)
    (firstBounded : failure + timing ≤ 1) (timingNonnegative : 0 ≤ timing)
    (timingBounded : timing ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1) :
    ((bindingServiceEmissionLaw clocks choose failure timing firstNonnegative firstBounded
      timingNonnegative timingBounded rawWeight rawNonnegative rawBounded) true).toReal =
      rawWeight + (1 - rawWeight) *
        (if clocks.length = 1 then 1 - failure - timing
         else if choose clocks then 1 - timing else timing) := by
  unfold bindingServiceEmissionLaw
  split_ifs <;> simp only [mix_apply_toReal, PMF.pure_apply,
    Bool.true_eq_false, ite_true, ite_false, ENNReal.toReal_zero, ENNReal.toReal_one] <;> ring

/-- Genuine counted history discharges both encoder guards. Each conditional
encoder transmits with total mass one, separately from local timing and the
source result, including an accepted unusable binding. -/
theorem bindingEncoders_transmission_of_history
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView → PMF (PublicationResult (L.Val payload)))
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (menu : (app).ResponseMenu) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (capacity : horizon ≤ bounds.candidateCount)
    (control : (app).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control)) (active : control.actor = some owner)
    (output : graph.outputLayout event = .binding owner payload)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall owner),
      event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    (countedSendLaw runtime leaks bounds owner (control.execution.recall owner)
      (control.execution.observe app owner)).map (fun action => action.transmission.isSome) =
        PMF.pure true ∧
    (bindingResultEncoder runtime leaks bounds owner event payload values slotWeight slotNonnegative
      slotBounded (control.execution.recall owner) (control.execution.observe app owner)).map
        (fun action => action.transmission.isSome) = PMF.pure true := by
  classical
  let past := control.execution.recall owner
  let view := control.execution.observe (app) owner
  let results := values
  have slots := phaseBindingSlots_nonempty_of_history runtime leaks bounds menu plan inputs
    horizon scheduler capacity control trace owner active event payload output request unsent
      catalogue
  have rawNonempty : (countedSends runtime leaks bounds owner past view).Nonempty := by
    obtain ⟨serial, eligible⟩ := slots
    refine ⟨phaseBindingResponse runtime leaks owner event payload .failure serial, ?_⟩
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp eligible).2.2 .failure, by rfl⟩
  have rawLaw := countedSendLaw_transmission runtime leaks bounds owner past view rawNonempty
  have slotLaw : (phaseBindingSlotPolicy runtime leaks bounds owner event payload results
      past view).map (fun response => response.transmission.isSome) = PMF.pure true := by
    rw [phaseBindingSlotPolicy, dite_eq_left slots, PMF.map_bind]
    have each (serial : Nat) :
        ((results past view).map (phaseBindingResponse runtime leaks owner event payload
          · serial)).map (fun response => response.transmission.isSome) = PMF.pure true := by
      rw [PMF.map_comp]
      exact PMF.map_const _ _
    simp only [each, PMF.bind_const]
  obtain ⟨serial, _bounded, canonical, _meaning⟩ := phaseBindingPolicy_of_history runtime leaks
    bounds owner event payload output results menu plan inputs horizon scheduler capacity control
      trace active request unsent catalogue
  have canonicalLaw : (phaseBindingPolicy runtime leaks bounds owner event payload results
      past view).map (fun response => response.transmission.isSome) = PMF.pure true := by
    rw [canonical, PMF.map_comp]
    exact PMF.map_const _ _
  have encoder : (bindingResultEncoder runtime leaks bounds owner event payload values slotWeight
      slotNonnegative slotBounded past view).map
        (fun response => response.transmission.isSome) = PMF.pure true := by
    rw [bindingResultEncoder, mix_map]
    rw [slotLaw, canonicalLaw, mix_self]
  exact ⟨rawLaw, encoder⟩

end Vegas.EventGraphRuntime.PhaseCount
