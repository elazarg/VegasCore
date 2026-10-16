/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingWordCoupling
import Vegas.Game.PhaseTimingWordResponse
import Vegas.Pending.PhaseBindingForeignResponse
import Vegas.Pending.PhaseBindingMemorySlots
import Vegas.Pending.PhaseBindingWordKernel
import Vegas.Pending.PhaseBindingInvariant
import Vegas.Pending.PhaseClearHistory
import Vegas.Game.PhaseTimingRecallMemory

/-! # Actual hidden-word response kernels with evolved physical memory -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

local notation "graph" => serviceGraph setup mode

local notation "app" => phaseApplication runtime leaks

/-- Every actual timing option couples arbitrary hidden word results through the real
response kernel, with original omission and guarded physical slots retained. -/
theorem phaseBindingTimingWordResponse_physical_coupling (bounds : MessageBounds (graph))
    (menu : (app).ResponseMenu) (plan : RuntimePhasePlan (graph)) (inputs : PMF (graph).Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (left right : (app).Control)
    (leftTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some left))
    (rightTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some right))
    (owner : Player) (memory : BindingShadow (graph)) (owned : memory.OwnBindings owner)
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
    (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding owner payload)
    (request : right.execution.application.SeedRequest owner
      ⟨right.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (right.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨right.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (serial : Nat)
    (eligible : serial ∈ PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
      (right.execution.recall owner) (right.execution.observe app owner))
    (missing : PMF Bool) (option : LateOption bounds.candidateCount) (slotWeight : ℝ)
    (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (firstResult secondResult : PublicationResult (L.Val payload)) :
    ∃ paired : PMF ((app).Execution × (app).Execution),
      paired.map Prod.fst =
        (phaseBindingTimingWordResponse setup mode runtime leaks bounds owner event payload missing
          option slotWeight slotNonnegative slotBounded firstResult (left.execution.recall owner)
            (left.execution.observe app owner)).map (left.execution.respond app owner) ∧
      paired.map Prod.snd =
        (phaseBindingTimingWordResponse setup mode runtime leaks bounds owner event payload missing
          option slotWeight slotNonnegative slotBounded secondResult
            (right.execution.recall owner) (right.execution.observe app owner)).map
              (right.execution.respond app owner) ∧
      ∀ pair ∈ paired.support, ∃ nextMemory : BindingShadow (graph),
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
  let related (pair : (app).Execution × (app).Execution) : Prop :=
    ∃ nextMemory : BindingShadow (graph),
        nextMemory.OwnBindings owner ∧
        (∀ slot, nextMemory.candidates slot ≠ some .fresh) ∧
        pair.1.application = nextMemory.phased owner pair.2.application ∧
        pair.1.network = pair.2.network ∧ pair.1.receipts = pair.2.receipts ∧
        pair.1.environmentRecall = pair.2.environmentRecall ∧
        (∀ who, who ≠ owner → pair.1.recall who = pair.2.recall who) ∧
        (pair.1.recall owner).map (fun entry =>
            (phaseOperationalView runtime leaks entry.beforeView, entry.emitted)) =
          (pair.2.recall owner).map (fun entry =>
            (phaseOperationalView runtime leaks entry.beforeView, entry.emitted))
  have tier := phaseBindingWordResponse_physical_coupling runtime leaks bounds menu plan inputs
    horizon scheduler left right leftTrace rightTrace owner memory owned valid application network
      receipts service recalled past clear event payload binding request unsent values serial
        eligible
        missing 1 (by norm_num) le_rfl firstResult secondResult
  obtain ⟨tier, firstTier, secondTier, tierRelated⟩ := tier
  let silent : (app).Execution × (app).Execution :=
    (left.execution.respond app owner ⟨none⟩, right.execution.respond app owner ⟨none⟩)
  have silentRelated : related silent := by
    refine ⟨memory, owned, valid, application, network, receipts, service, ?_, ?_⟩
    · intro who different
      exact ((app).respond_recall_other left.execution owner who different _).trans
        ((recalled who different).trans
          ((app).respond_recall_other right.execution owner who different _).symm)
    · exact phaseOperationalRecall_response runtime leaks left.execution right.execution owner
        _ _ network past (phaseOperationalView_memory runtime leaks memory owner owned valid
          left.execution right.execution application network receipts) network
  have sameSlots := BindingShadow.bindingSlots_eq_of_histories runtime leaks bounds menu plan
    inputs horizon scheduler left right leftTrace rightTrace memory owner valid application network
      event payload binding request unsent values
  have selected : ∃ chosen : PMF ((app).Execution × (app).Execution),
      chosen.map Prod.fst =
        (match option with
        | none => PMF.pure (⟨none⟩ : (app).Action)
        | some selected =>
          if selected.val ∈ PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
              (left.execution.recall owner) (left.execution.observe app owner) then
            PhaseCount.phaseBindingWordResponse runtime leaks bounds owner event payload missing
              selected.val 0 le_rfl (by norm_num) firstResult (left.execution.recall owner)
                (left.execution.observe app owner)
          else PMF.pure (⟨none⟩ : (app).Action)).map (left.execution.respond app owner) ∧
      chosen.map Prod.snd =
        (match option with
        | none => PMF.pure (⟨none⟩ : (app).Action)
        | some selected =>
          if selected.val ∈ PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
              (right.execution.recall owner) (right.execution.observe app owner) then
            PhaseCount.phaseBindingWordResponse runtime leaks bounds owner event payload missing
              selected.val 0 le_rfl (by norm_num) secondResult (right.execution.recall owner)
                (right.execution.observe app owner)
          else PMF.pure (⟨none⟩ : (app).Action)).map (right.execution.respond app owner) ∧
      ∀ pair ∈ chosen.support, related pair := by
    cases option with
    | none =>
        refine ⟨PMF.pure silent, ?_, ?_, ?_⟩
        · simp only [PMF.pure_map, silent]
        · simp only [PMF.pure_map, silent]
        · intro pair supported
          cases (PMF.mem_support_pure_iff ..).mp supported
          exact silentRelated
    | some selected =>
        by_cases member : selected.val ∈ PhaseCount.phaseBindingSlots runtime leaks bounds owner
            event payload (right.execution.recall owner) (right.execution.observe app owner)
        · obtain ⟨chosen, firstLaw, secondLaw, good⟩ :=
            phaseBindingWordResponse_physical_coupling runtime leaks bounds menu plan inputs
              horizon scheduler left right leftTrace rightTrace owner memory owned valid application
                network receipts service recalled past clear event payload binding request unsent
                  values selected.val member missing 0 le_rfl (by norm_num) firstResult secondResult
          refine ⟨chosen, ?_, ?_, good⟩
          · simpa only [sameSlots, member, ↓reduceIte] using firstLaw
          · simpa only [member, ↓reduceIte] using secondLaw
        · refine ⟨PMF.pure silent, ?_, ?_, ?_⟩
          · simp only [sameSlots, member, ↓reduceIte, PMF.pure_map, silent]
          · simp only [member, ↓reduceIte, PMF.pure_map, silent]
          · intro pair supported
            cases (PMF.mem_support_pure_iff ..).mp supported
            exact silentRelated
  obtain ⟨selected, firstSelected, secondSelected, selectedRelated⟩ := selected
  refine ⟨mix slotWeight slotNonnegative slotBounded tier selected, ?_, ?_, ?_⟩
  · rw [mix_map, firstTier, firstSelected]
    simp only [phaseBindingTimingWordResponse, mix_map]
    simp only [PhaseCount.phaseBindingWordResponse, mix_one, mix_zero]
    rfl
  · rw [mix_map, secondTier, secondSelected]
    simp only [phaseBindingTimingWordResponse, mix_map]
    simp only [PhaseCount.phaseBindingWordResponse, mix_one, mix_zero]
    rfl
  · intro pair supported
    rcases support_mix_subset slotWeight slotNonnegative slotBounded tier selected supported with
      first | second
    · exact tierRelated pair first
    · exact selectedRelated pair second

end Vegas
