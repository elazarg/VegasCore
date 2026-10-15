/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingSlotSupport
import Vegas.Pending.PhaseResponseNormalization
import Interaction.ReactiveRoundTrace

/-! # Supported phased binding responses with repaired private material -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

namespace PhaseCount

local notation "app" => phaseApplication runtime leaks

/-- Changing only a binding's private preparation preserves every opponent's
complete physical input jointly, as well as the scheduler's actual input. -/
theorem rawBinding_respond_hidden_congr (execution : (app).Execution)
    (owner : Player) (event : graph.EventId) (serial : Nat)
    (first second : Option (Raw L)) :
    let response (opening : Option (Raw L)) : (app).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
    let original := execution.respond (app) owner (response first)
    let repaired := execution.respond (app) owner (response second)
    original.network = repaired.network ∧ original.receipts = repaired.receipts ∧
      original.application.publicView = repaired.application.publicView ∧
      original.environmentRecall = repaired.environmentRecall ∧
      (∀ who, who ≠ owner →
        (original.recall who, original.observe (app) who) =
          (repaired.recall who, repaired.observe (app) who)) ∧
      original.observeEnvironment (app) = repaired.observeEnvironment (app) := by
  let material (opening : Option (Raw L)) : WitnessedSubmission graph :=
    ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩
  let response (opening : Option (Raw L)) : (app).Action := ⟨some (material opening)⟩
  let original := execution.respond (app) owner (response first)
  let repaired := execution.respond (app) owner (response second)
  have emitted : (execution.application.submit owner (material first)).emit owner
        (execution.network.known owner) (material first) =
      (execution.application.submit owner (material second)).emit owner
        (execution.network.known owner) (material second) := by
    rw [emit_after_submit, emit_after_submit]
    rfl
  have networks : original.network = repaired.network := by
    change (execution.network.submit owner _).2 = (execution.network.submit owner _).2
    exact congrArg (fun packet => (execution.network.submit owner packet).2) emitted
  have unchangedPublic (opening : Option (Raw L)) :
      (execution.respond (app) owner (response opening)).application.publicView =
        execution.application.publicView := submit_publicView _ _ _
  have other (opening : Option (Raw L)) (who : Player) (different : who ≠ owner) :
      (execution.respond (app) owner (response opening)).application.playerView who =
        execution.application.playerView who := by
    have native := (submitStep_playerView_other
      ((material opening).call.register execution.application.current.native owner)
        owner who different (material opening).call.packet).trans
          ((material opening).call.register_other execution.application.current.native
            owner who different)
    exact Prod.ext native (unchangedPublic opening)
  have publics : original.application.publicView = repaired.application.publicView :=
    (unchangedPublic first).trans (unchangedPublic second).symm
  refine ⟨networks, rfl, publics, rfl, ?_, ?_⟩
  · intro who different
    have recalls : original.recall who = repaired.recall who := by
      rw [(app).respond_recall_other execution owner who different,
        (app).respond_recall_other execution owner who different]
    refine Prod.ext recalls ?_
    change (⟨original.network.observe who, original.application.playerView who,
      original.receipts⟩ : (app).PlayerView) =
      ⟨repaired.network.observe who, repaired.application.playerView who, repaired.receipts⟩
    rw [networks, other first who different, other second who different]
    rfl
  · change (⟨original.network.publicView, original.application.publicView,
      original.receipts⟩ : (app).EnvironmentView) = _
    rw [networks, publics]
    rfl

variable [Fintype Player] (bounds : MessageBounds graph)

/-- The actual slot law supports a chosen successful replacement exactly when
its original typed source law admits that replacement. No target response
support is included among the premises. -/
theorem binding_replacement_mem_slotPolicy (owner : Player) (event : graph.EventId)
    (payload : L.Ty)
    (results : List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (serial : Nat)
    (eligible : serial ∈ phaseBindingSlots runtime leaks bounds owner event payload past view)
    (value : L.Val payload) (admitted : .success value ∈ (results past view).support) :
    phaseBindingResponse runtime leaks owner event payload (.success value) serial ∈
      (phaseBindingSlotPolicy runtime leaks bounds owner event payload
        results past view).support := by
  classical
  rw [phaseBindingSlotPolicy, dite_eq_left ⟨serial, eligible⟩, PMF.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨serial,
    (PMF.mem_support_uniformOfFinset_iff ..).mpr eligible, ?_⟩
  exact (PMF.mem_support_map_iff ..).mpr ⟨.success value, admitted, rfl⟩

/-- A permitted raw binding has an actual repaired response history under the
same scheduler and original prefix. Arbitrary evidence aliases are normalized
operationally, and arbitrary unusable or mistyped preparation is replaced by
the specified typed value at the very same globally fresh physical slot. -/
theorem binding_replacement_trace (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (remaining : Nat) (execution : (app).Execution) (owner : Player)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest graph)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ :
      (app).Action) ∈ onePacketActions runtime leaks bounds owner
        (execution.recall owner) (execution.observe (app) owner))
    (value : L.Val payload) :
    let originalResponse : (app).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩
    let repairedResponse := phaseBindingResponse runtime leaks owner event payload
      (.success value) serial
    let original := execution.respond (app) owner originalResponse
    let repaired := execution.respond (app) owner repairedResponse
    Nonempty (((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, none, repaired⟩)) ∧
      repaired.application.current.native.bindingResult (owner, .prepared serial) payload =
        .success value ∧
      original.network = repaired.network ∧ original.receipts = repaired.receipts ∧
      original.application.publicView = repaired.application.publicView ∧
      original.environmentRecall = repaired.environmentRecall ∧
      (∀ who, who ≠ owner → (original.recall who, original.observe (app) who) =
        (repaired.recall who, repaired.observe (app) who)) ∧
      original.observeEnvironment (app) = repaired.observeEnvironment (app) := by
  classical
  obtain ⟨_bounded, fresh, eligible⟩ := binding_slot_mem_of_onePacket runtime leaks bounds
    plan inputs horizon scheduler trace owner event payload outputEq request unsent values
      serial opening evidence member
  have legal := (Finset.mem_filter.mp eligible).2.2 (.success value)
  have targetTrace := (onePacketMenu runtime leaks bounds).trace_respond
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler remaining execution owner
      (phaseBindingResponse runtime leaks owner event payload (.success value) serial) trace legal
  have changed := rawBinding_respond_hidden_congr runtime leaks execution owner event serial
    opening (some ⟨payload, value⟩)
  let source : (app).Action :=
    ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩
  let plain : (app).Action :=
    ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩
  have permitted := ((mem_onePacketActions runtime leaks bounds owner _ _ _).mp member).2
  have actualPermits : permits ((app).outputs (execution.recall owner))
      (localEnvelope runtime leaks owner (execution.recall owner)
        (execution.observe (app) owner)
          ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩) = true := by
    rcases permitted with impossible | ⟨material, transmitted, allowed⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact allowed
  have normalized : (normalization runtime leaks).action owner (execution.recall owner)
      (execution.observe (app) owner) source = plain := by
    have evidenceNone := normalize_binding_evidence_none runtime leaks owner
      (execution.recall owner)
      (execution.observe (app) owner)
        ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩
          event (owner, .prepared serial) rfl actualPermits
    have effective : openingEffective owner
        (execution.observe (app) owner).application.1
          (.commitment event (owner, .prepared serial)) := ⟨rfl, fresh⟩
    have callEq : ((normalization runtime leaks).normalize owner
        (execution.observe (app) owner).application
        (ReactiveApplication.ResponseMenu.knownPackets (execution.recall owner)
          (execution.observe (app) owner))
        ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩).call =
          ⟨.commitment event (owner, .prepared serial), opening⟩ :=
      Submission.normalizeReactive_effective _ _ _ effective
    exact congrArg (fun material => (⟨some material⟩ : (app).Action))
      (congrArg₂ WitnessedSubmission.mk callEq evidenceNone)
  have effects := (normalization runtime leaks).effects execution owner source
    (countRecall_history runtime leaks
      ((onePacketMenu runtime leaks bounds).toRawTrace _ _ _ trace)).1
  rw [normalized] at effects
  refine ⟨targetTrace, phaseBindingResponse_result runtime leaks execution owner event payload
    (.success value) serial fresh, effects.2.1.symm.trans changed.1, effects.2.2.1.symm.trans
      changed.2.1, ?_, effects.2.2.2.1.symm.trans changed.2.2.2.1, ?_, ?_⟩
  · exact (congrArg PhaseRuntimeState.publicView effects.1).symm.trans changed.2.2.1
  · intro who different
    have recalls := effects.2.2.2.2 who different
    have observes : (execution.respond (app) owner plain).observe (app) who =
        (execution.respond (app) owner source).observe (app) who := by
      change (⟨_, _, _⟩ : (app).PlayerView) = _
      rw [effects.1, effects.2.1, effects.2.2.1]
      rfl
    exact (Prod.ext recalls observes).symm.trans (changed.2.2.2.2.1 who different)
  · have observes : (execution.respond (app) owner plain).observeEnvironment (app) =
        (execution.respond (app) owner source).observeEnvironment (app) := by
      change (⟨_, _, _⟩ : (app).EnvironmentView) = _
      rw [effects.1, effects.2.1, effects.2.2.1]
      rfl
    exact observes.symm.trans changed.2.2.2.2.2

end PhaseCount
end Vegas.EventGraphRuntime
