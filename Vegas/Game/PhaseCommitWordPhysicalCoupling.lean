/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceTimingWordCoupling
import Vegas.Game.PhaseCommitTimingWordPolicy
import Vegas.Pending.PhaseNativeInvariant
import Vegas.Game.PhaseBindingWordOmission

/-! # Original source draws in actual timing-word physical coupling -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- Two genuine callbacks of complete-word timing members admit a real
physical response coupling, for arbitrary original words including failed
bindings. Actual capacity supplies a fresh fallback slot; the original source
omission laws are derived equal rather than supplied as a common kernel. -/
theorem phase_commit_timing_word_physical_coupling
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (owner : Player)
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (firstWord secondWord : DecisionView owner Δ)
    (n : Nat) (left right : (app).Control)
    (leftTrace : (E).Trace (some left)) (rightTrace : (E).Trace (some right))
    (memory : BindingShadow graph) (owned : memory.OwnBindings owner)
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
    (capacity : horizon ≤ bounds.candidateCount)
    (active : right.actor = some owner)
    (inside : low ≤ event.val ∧ event.val < low + block.length)
    (address : right.execution.application.attempt = ⟨low, generation⟩)
    (option : LateOption bounds.candidateCount) (slotWeight : ℝ)
    (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    :
    ∃ paired : PMF ((app).Execution × (app).Execution),
      paired.map Prod.fst =
        (phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed
          (approximation.sequence n) block low generation slotWeight slotNonnegative slotBounded
            option owner firstWord (left.execution.recall owner)
              (left.execution.observe app owner)).map (left.execution.respond app owner) ∧
      paired.map Prod.snd =
        (phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed
          (approximation.sequence n) block low generation slotWeight slotNonnegative slotBounded
            option owner secondWord (right.execution.recall owner)
              (right.execution.observe app owner)).map
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
  let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
  have countedLeft : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some left) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact leftTrace
  have countedRight : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some right) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact rightTrace
  obtain ⟨serial, eligible⟩ := PhaseCount.phaseBindingSlots_nonempty_of_history runtime leaks bounds
    (PhaseCount.onePacketMenu runtime leaks bounds) plan inputs horizon scheduler capacity right
      countedRight owner active event payload binding request unsent values
  have rawLeft := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler countedLeft
  have rawRight := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler countedRight
  obtain ⟨firstDraw, firstInvariant⟩ := phaseNativeInvariant_history runtime leaks plan inputs
    horizon scheduler rawLeft
  obtain ⟨secondDraw, secondInvariant⟩ := phaseNativeInvariant_history runtime leaks plan inputs
    horizon scheduler rawRight
  have firstRequest : left.execution.application.SeedRequest owner
      ⟨left.execution.application.attempt, event⟩ := by rw [application]; exact request
  have firstAddress : left.execution.application.attempt = ⟨low, generation⟩ := by
    rw [application]
    exact address
  let firstResult := (phaseRecoveryBindingData setup mode event owner payload binding
    (CommitRecoveryMove.lift (block.wordAction owner (event.val - low) firstWord))).1
  let secondResult := (phaseRecoveryBindingData setup mode event owner payload binding
    (CommitRecoveryMove.lift (block.wordAction owner (event.val - low) secondWord))).1
  obtain ⟨paired, firstLaw, secondLaw, related⟩ :=
    phase_source_timing_word_response_physical_coupling setup mode runtime leaks bounds plan horizon
      scheduler finite wellFormed target approximation maximal n left right leftTrace rightTrace
        owner memory owned valid application network receipts service recalled past clear event
          payload binding request unsent values serial eligible option slotWeight slotNonnegative
            slotBounded firstResult secondResult
  refine ⟨paired, ?_, ?_, related⟩
  · rw [phaseCommitTimingWordPolicy_binding setup mode runtime leaks bounds wellFormed
      (approximation.sequence n) block low generation slotWeight slotNonnegative slotBounded option
        owner firstWord left.execution firstInvariant event payload binding firstRequest inside
          firstAddress]
    exact firstLaw
  · rw [phaseCommitTimingWordPolicy_binding setup mode runtime leaks bounds wellFormed
      (approximation.sequence n) block low generation slotWeight slotNonnegative slotBounded option
        owner secondWord right.execution secondInvariant event payload binding request inside
          address]
    exact secondLaw

end Vegas
