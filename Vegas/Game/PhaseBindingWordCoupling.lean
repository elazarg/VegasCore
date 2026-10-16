/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingForeignResponseMemory
import Vegas.Pending.PhaseBindingMemorySlots
import Vegas.Pending.PhaseBindingWordKernel
import Vegas.Pending.PhaseBindingInvariant
import Vegas.Pending.PhaseClearHistory
import Vegas.Game.PhaseTimingRecallMemory

/-! # Actual hidden-word response kernels with evolved physical memory -/

noncomputable section

namespace Vegas

open EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Both actual response marginals use the original omission draw and the
same actual guarded serial or independent slot tier. Their evolved physical
memory and complete erased owner words are derived from the real responses. -/
theorem phaseBindingWordResponse_physical_coupling (bounds : MessageBounds graph)
    (menu : (app).ResponseMenu) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (left right : (app).Control)
    (leftTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some left))
    (rightTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some right))
    (owner : Player) (memory : BindingShadow graph) (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (application : left.execution.application = memory.phased owner right.execution.application)
    (network : left.execution.network = right.execution.network)
    (receipts : left.execution.receipts = right.execution.receipts)
    (service : left.execution.environmentRecall = right.execution.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.execution.recall who = right.execution.recall who)
    (past : (left.execution.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
      (right.execution.recall owner).map (fun entry =>
        (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)))
    (clear : right.execution.application.current.excluded = ∅)
    (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (request : right.execution.application.SeedRequest owner
      ⟨right.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (right.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨right.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (serial : Nat)
    (eligible : serial ∈ PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
      (right.execution.recall owner) (right.execution.observe app owner))
    (missing : PMF Bool) (slotWeight : ℝ)
    (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (firstResult secondResult : PublicationResult (L.Val payload)) :
    ∃ paired : PMF ((app).Execution × (app).Execution),
      paired.map Prod.fst =
        (PhaseCount.phaseBindingWordResponse runtime leaks bounds owner event payload missing
          serial slotWeight slotNonnegative slotBounded firstResult (left.execution.recall owner)
            (left.execution.observe app owner)).map (left.execution.respond app owner) ∧
      paired.map Prod.snd =
        (PhaseCount.phaseBindingWordResponse runtime leaks bounds owner event payload missing
          serial slotWeight slotNonnegative slotBounded secondResult
            (right.execution.recall owner) (right.execution.observe app owner)).map
              (right.execution.respond app owner) ∧
      ∀ pair ∈ paired.support, ∃ nextMemory : BindingShadow graph,
        nextMemory.OwnBindings owner ∧
        (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
        pair.1.application = nextMemory.phased owner pair.2.application ∧
        pair.1.network = pair.2.network ∧ pair.1.receipts = pair.2.receipts ∧
        pair.1.environmentRecall = pair.2.environmentRecall ∧
        (∀ who, who ≠ owner → pair.1.recall who = pair.2.recall who) ∧
        (pair.1.recall owner).map (fun entry =>
            (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
          (pair.2.recall owner).map (fun entry =>
            (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) := by
  classical
  let slots := PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
    (right.execution.recall owner) (right.execution.observe app owner)
  have offered : slots.Nonempty := ⟨serial, eligible⟩
  have sameSlots := BindingShadow.bindingSlots_eq_of_histories runtime leaks bounds menu plan
    inputs horizon scheduler left right leftTrace rightTrace memory owner valid application network
      event payload binding request unsent values
  have leftOffered : (PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
      (left.execution.recall owner) (left.execution.observe app owner)).Nonempty := by
    rw [sameSlots]
    exact offered
  have uniformEq :
      PMF.uniformOfFinset (PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
        (left.execution.recall owner) (left.execution.observe app owner)) leftOffered =
      PMF.uniformOfFinset slots offered := by
    congr 1
  let atSerial (chosen : Nat) : (app).Execution × (app).Execution :=
    (left.execution.respond app owner
      (phaseBindingResponse runtime leaks owner event payload firstResult chosen),
      right.execution.respond app owner
        (phaseBindingResponse runtime leaks owner event payload secondResult chosen))
  let silent : (app).Execution × (app).Execution :=
    (left.execution.respond app owner ⟨none⟩,
    right.execution.respond app owner ⟨none⟩)
  let sending : PMF ((app).Execution × (app).Execution) :=
    mix slotWeight slotNonnegative slotBounded
    ((PMF.uniformOfFinset slots offered).map atSerial) (PMF.pure (atSerial serial))
  let paired : PMF ((app).Execution × (app).Execution) :=
    missing.bind fun omitted => if omitted then PMF.pure silent else sending
  refine ⟨paired, ?_, ?_, ?_⟩
  · simp only [paired, PhaseCount.phaseBindingWordResponse, PMF.map_bind]
    apply congrArg (PMF.bind missing)
    funext omitted
    cases omitted with
    | true => simp only [↓reduceIte, PMF.pure_map, silent]
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, sending, mix_map, PMF.pure_map]
        rw [PhaseCount.phaseBindingSlotPolicy, dite_eq_left leftOffered]
        simp only [PMF.map_bind, PMF.pure_map]
        rw [uniformEq]
        simp only [PMF.map_comp]
        rfl
  · simp only [paired, PhaseCount.phaseBindingWordResponse, PMF.map_bind]
    apply congrArg (PMF.bind missing)
    funext omitted
    cases omitted with
    | true => simp only [↓reduceIte, PMF.pure_map, silent]
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, sending, mix_map, PMF.pure_map]
        rw [PhaseCount.phaseBindingSlotPolicy, dite_eq_left offered]
        simp only [PMF.map_bind, PMF.pure_map, PMF.map_comp]
        rfl
  · have raw := menu.toRawTrace _ horizon scheduler rightTrace
    have archive := (phase_clear_history runtime leaks plan inputs horizon scheduler right raw
      clear).2
    have fixed := (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).fixed
    have sendingGood (chosen : Nat) (member : chosen ∈ slots) :
        ∃ nextMemory : BindingShadow graph,
          nextMemory.OwnBindings owner ∧
          (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
          (atSerial chosen).1.application =
            nextMemory.phased owner (atSerial chosen).2.application ∧
          (atSerial chosen).1.network = (atSerial chosen).2.network ∧
          (atSerial chosen).1.receipts = (atSerial chosen).2.receipts ∧
          (atSerial chosen).1.environmentRecall = (atSerial chosen).2.environmentRecall ∧
          (∀ who, who ≠ owner → (atSerial chosen).1.recall who = (atSerial chosen).2.recall who) ∧
          ((atSerial chosen).1.recall owner).map (fun entry =>
              (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
            ((atSerial chosen).2.recall owner).map (fun entry =>
              (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) := by
      have fresh : right.execution.application.current.native.candidates.lookup
          (owner, .prepared chosen) = .fresh := (Finset.mem_filter.mp member).2.1
      have savedFresh : right.execution.application.entry.native.candidates.lookup
          (owner, .prepared chosen) = .fresh := by
        by_contra notFresh
        exact notFresh ((fixed (owner, .prepared chosen) notFresh).symm.trans fresh)
      let nextMemory := memory.rememberCandidate (.prepared chosen)
        ((atSerial chosen).1.application.current.native.candidates.lookup (owner, .prepared chosen))
      exact ⟨nextMemory, phaseTimingRecall_binding_memory runtime leaks memory owner owned valid
        left.execution right.execution application network receipts service recalled past archive
          event payload firstResult secondResult chosen fresh savedFresh⟩
    intro pair reached
    obtain ⟨omitted, _possible, reached⟩ := (PMF.mem_support_bind_iff ..).mp reached
    cases omitted with
    | true =>
        cases (PMF.mem_support_pure_iff ..).mp reached
        refine ⟨memory, owned, valid, application, network, receipts, service, ?_, ?_⟩
        · intro who different
          exact ((app).respond_recall_other left.execution owner who different _).trans
            ((recalled who different).trans
              ((app).respond_recall_other right.execution owner who different _).symm)
        · exact phaseOperationalRecall_response runtime leaks left.execution right.execution owner
            _ _ network past (phaseOperationalView_memory runtime leaks memory owner owned valid
              left.execution right.execution application network receipts) network
    | false =>
        have inSending : pair ∈ sending.support := reached
        rcases support_mix_subset slotWeight slotNonnegative slotBounded
          ((PMF.uniformOfFinset slots offered).map atSerial) (PMF.pure (atSerial serial))
            inSending with uniform | canonical
        · obtain ⟨chosen, member, rfl⟩ := (PMF.mem_support_map_iff ..).mp uniform
          exact sendingGood chosen ((PMF.mem_support_uniformOfFinset_iff ..).mp member)
        · cases (PMF.mem_support_pure_iff ..).mp canonical
          exact sendingGood serial eligible

end Vegas
