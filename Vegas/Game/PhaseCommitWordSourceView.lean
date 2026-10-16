/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.CommitPrefixWordAction
import Vegas.Compile.CommitPhaseLayout
import Vegas.Compile.CommitPrefixWordReadout
import Vegas.Game.PhaseCommitWordAcceptedPosterior
import Vegas.Source.CommitPrefixWordProjection

/-! # Actual accepted bindings identify the earlier complete source view -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- The actual whole-program decoder recovers precisely the addressed
original source action chosen from an owned complete word. -/
theorem phaseCommitWordAction_decode
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (who : Player) (index : Fin (eventCount (block.prepend suffix)))
    (inside : index.val < block.length) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout (embedding.event index) =
      .binding who payload) (word : DecisionView who Δ) :
    decodeEventAction setup.program (embedding.event index)
      (cast (congrArg EventField.Action binding.symm)
        (phaseRecoveryBindingData setup mode (embedding.event index) who payload binding
          (CommitRecoveryMove.lift (block.wordAction who index.val word))).1) =
      block.wordAction who index.val word := by
  have owned : eventOwner? (block.prepend suffix) index = some who := by
    rw [eventOwner?_eq_actor]
    exact EventGraph.actor?_of_outputLayout_binding (toEventGraph (block.prepend suffix))
      ((embedding.layout_eq index).symm.trans binding)
  obtain ⟨action, native, read, decoded⟩ := compiledCommitPrefix_wordAction_decodable
    block suffix who index inside owned word
  let graphAction : EventField.Action (outputLayout setup.program (embedding.event index)) :=
    cast (congrArg EventField.Action (embedding.layout_eq index).symm) native
  have actual : decodeEventAction setup.program (embedding.event index) graphAction =
      some action := by
    rw [actions]
    simpa only [graphAction, cast_cast, cast_eq] using decoded
  have encoded := encodeEventAction?_decodeEventAction_eq_some setup.program
    (embedding.event index) graphAction action actual
  rw [read]
  simpa only [phaseRecoveryBindingData, CommitRecoveryMove.lift, Option.map_some,
    Option.elim_some, Bool.false_eq_true, ↓reduceIte, Option.bind_some, encoded,
    Option.getD_some, cast_cast, cast_eq] using actual

/-- At an actual compiled owned slot, the complete-word result encoder is
injective on its genuine original source actions. Failed accepted values are
included, and arbitrary complete words need no support premise. -/
theorem phaseCommitWordAction_eq_iff_result
    (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (block.prepend suffix))
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (block.prepend suffix) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (who : Player) (index : Fin (eventCount (block.prepend suffix)))
    (inside : index.val < block.length) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout (embedding.event index) =
      .binding who payload) (left right : DecisionView who Δ) :
    block.wordAction who index.val left = block.wordAction who index.val right ↔
      (phaseRecoveryBindingData setup mode (embedding.event index) who payload binding
        (CommitRecoveryMove.lift (block.wordAction who index.val left))).1 =
      (phaseRecoveryBindingData setup mode (embedding.event index) who payload binding
        (CommitRecoveryMove.lift (block.wordAction who index.val right))).1 := by
  constructor
  · intro same
    rw [same]
  · intro same
    have compared := congrArg (fun result => decodeEventAction setup.program
      (embedding.event index) (cast (congrArg EventField.Action binding.symm) result)) same
    simpa only [phaseCommitWordAction_decode setup mode block suffix embedding actions who index
      inside payload binding] using compared

section ActualHistory

variable [Fintype Player]
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P)
  (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
    (block.prepend suffix)) (low generation : Nat)
  (rank : ∀ index, (embedding.event index).val = low + index.val)
  (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
    decodeEventAction (block.prepend suffix) index
      (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (who : Player)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  {control : (phaseApplication runtime leaks).Control}
  (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
  (clear : control.execution.application.current.excluded = ∅)
  (selected : (serviceGraph setup mode).EventId)
  (request : control.execution.application.SeedRequest who
    ⟨control.execution.application.attempt, selected⟩)
  (inside : low ≤ selected.val ∧ selected.val < low + block.length)
  (address : control.execution.application.attempt = ⟨low, generation⟩)

local notation "family" => phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed
  assessment block low generation slotWeight slotNonnegative slotBounded who

include rank actions trace clear request inside address in
/-- At an actual clear owned callback, accepted-result agreement is exactly
agreement of the original addressed source actions strictly before that callback.
The comparison uses the genuine compiler codec, including accepted failures. -/
theorem phaseCommitWordAgrees_iff_wordActions_of_history
    (original : DecisionView who Δ)
    (consistent : (family original).Consistent (control.execution.recall who))
    (word : DecisionView who Δ) :
    phaseCommitWordAgrees setup mode block low who control.execution.application.current.native
        selected.val word ↔
      ∀ index < selected.val - low, block.wordAction who index original =
        block.wordAction who index word := by
  classical
  let graph := serviceGraph setup mode
  let native := control.execution.application.current.native
  let raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  have coverage := (phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    raw).active
  let ordered := serviceGraph_revealRelaxedOrdered setup mode
  have originalMeaning (event : graph.EventId) (payload : L.Ty)
      (binding : graph.outputLayout event = .binding who payload) (candidate : Handle graph)
      (interval : low ≤ event.val ∧ event.val < selected.val)
      (accepted : native.accepted (.inr event) = some candidate) :
      native.bindingResult candidate payload =
        (phaseRecoveryBindingData setup mode event who payload binding
          (CommitRecoveryMove.lift (block.wordAction who (event.val - low) original))).1 := by
    obtain ⟨_entry, _serial, _retained, _attempt, _declared, _handle, meaning, _decoded⟩ :=
      phaseCommitWordRecall_accepted setup mode runtime leaks bounds wellFormed assessment block
        low generation slotWeight slotNonnegative slotBounded who original plan inputs
          horizon scheduler trace clear event payload binding (by omega) address candidate accepted
            consistent
    exact meaning
  constructor
  · intro agrees position before
    have blockBound : position < block.length := by omega
    let index : Fin (eventCount (block.prepend suffix)) :=
      ⟨position, by have count := block.eventCount_prepend suffix; omega⟩
    by_cases owned : eventOwner? (block.prepend suffix) index = some who
    · obtain ⟨owner, payload, _ownerMember, layout⟩ :=
        block.binding_before_length suffix index blockBound
      have sameOwner : owner = who := by
        have actor := EventGraph.actor?_of_outputLayout_binding
          (toEventGraph (block.prepend suffix)) layout
        rw [eventOwner?_eq_actor, actor] at owned
        exact Option.some.inj owned
      subst owner
      have binding : graph.outputLayout (embedding.event index) = .binding who payload :=
        (embedding.layout_eq index).trans layout
      have actor : graph.actor? (embedding.event index) = some who :=
        EventGraph.actor?_of_outputLayout_binding graph binding
      have below : (embedding.event index).val < selected.val := by
        rw [rank]
        dsimp only [index]
        omega
      have done : embedding.event index ∈ native.config.cut.completed :=
        (ordered.ready_visible_iff native.config.cut request.2.2.1 request.2.2.2.1
          (EventCode.output_visible_of_actor (graph.nodes (embedding.event index)) who actor)
          (IndependentReveals.not_of_actor_eq (by rw [actor, request.2.2.2.1]))
          (IndependentReveals.not_of_actor_eq (by rw [actor, request.2.2.2.1]))).mpr below
      have present : native.accepted (.inr (embedding.event index)) ≠ none := by
        intro absent
        have failed : native.PublicFailure (embedding.event index) := Or.inl
          ((native.publicView_missedBinding (embedding.event index) who payload binding).mpr
            ⟨done, absent⟩)
        have excluded := coverage.covered (embedding.event index) who actor failed
        rw [clear] at excluded
        exact Finset.notMem_empty _ excluded
      obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
      have interval : low ≤ (embedding.event index).val ∧
          (embedding.event index).val < selected.val := by
        exact ⟨by rw [rank]; omega, below⟩
      have originalResult := originalMeaning (embedding.event index) payload binding candidate
        interval accepted
      have targetResult := agrees (embedding.event index) payload binding candidate
        interval accepted
      have compared := originalResult.symm.trans targetResult
      have offset : (embedding.event index).val - low = index.val := by rw [rank]; omega
      rw [offset] at compared
      exact (phaseCommitWordAction_eq_iff_result setup mode block suffix embedding actions who
        index blockBound payload binding original word).mpr compared
    · rw [compiledCommitPrefix_wordAction_none_of_unowned block suffix who index owned original,
        compiledCommitPrefix_wordAction_none_of_unowned block suffix who index owned word]
  · intro same event payload binding candidate interval accepted
    have position : event.val - low < selected.val - low := by omega
    have compared := same (event.val - low) position
    rw [originalMeaning event payload binding candidate interval accepted, compared]

end ActualHistory
end Vegas
