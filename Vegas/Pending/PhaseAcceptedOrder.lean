/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.BindingReceiptOrder
import Vegas.Pending.PhaseRawExclusion
import Vegas.Pending.ReactiveSignedCommitments

/-! # Actual phase executions preserve source order of owned receipts -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Current accepted bindings have every earlier receipt of their owner and
cannot belong to an owner already excluded when this attempt was installed. -/
structure ReceiptRecord (state : PhaseRuntimeState graph) : Prop where
  exclusion : state.ExclusionRecord
  ordered : ∀ phase ∈ state.phases.head?, phase.kind = .commitment →
    BindingReceiptOrder phase.low state.entry.excluded state.current.native.accepted

omit [DecidableEq Player] in
theorem fresh_receiptRecord (phases : List (RuntimePhase graph)) (generation : Nat)
    (current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (frontier : Frontier
      (⟨phases, generation, current, current, retired⟩ : PhaseRuntimeState graph))
    (receipts : current.native.ReceiptsComplete) :
    ReceiptRecord
      (⟨phases, generation, current, current, retired⟩ : PhaseRuntimeState graph) := by
  have prefixes : ∀ phase ∈ phases.head?, current.native.config.cut.IsPrefix phase.low := by
    intro phase member
    cases phases with
    | nil => cases member
    | cons first rest =>
        simp only [List.head?_cons, Option.mem_some_iff] at member
        subst phase
        exact frontier.positioned.1
  exact ⟨⟨frontier, receipts, receipts, fun phase member =>
    ExclusionEvidence.of_prefix receipts (prefixes phase member) rfl⟩,
    fun phase member _commitment => BindingReceiptOrder.of_prefix receipts
      (prefixes phase member)⟩

/-- Local draining, retry restoration and chains of automatic phase advancement
all retain the causal accepted-receipt condition. -/
theorem settle_receiptRecord (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (valid : ReceiptRecord
      (⟨phases, generation, entry, current, retired⟩ : PhaseRuntimeState graph)) :
    (settle phases generation entry current retired).ReceiptRecord := by
  induction phases generalizing generation entry current retired with
  | nil => exact valid
  | cons phase remaining ih =>
      obtain ⟨adjacent, last, saved, within⟩ := valid.exclusion.frontier
      have member : phase ∈ (phase :: remaining).head? := by simp
      have record := valid.exclusion.installed phase member
      have drained := record.phase_drain phase
      have drainedWithin := phase.drain_within current within
      have restoredReceipts : (restore entry (phase.drain current)).native.ReceiptsComplete := by
        intro event candidate installed
        exact valid.exclusion.saved event candidate installed
      have restoredRecord := ExclusionEvidence.of_prefix restoredReceipts saved rfl
      have rebuilt := restoredRecord.phase_drain phase
      have restoredWithin : (restore entry (phase.drain current)).native.config.cut.Within
          phase.low phase.high := saved.within phase.nonempty.le
      have rebuiltWithin := phase.drain_within (restore entry (phase.drain current)) restoredWithin
      have drainedOrder : phase.kind = .commitment →
          BindingReceiptOrder phase.low entry.excluded (phase.drain current).native.accepted :=
        fun commitment => (valid.ordered phase member commitment).congr (phase.drain_tables _).1
      have rebuiltOrder : BindingReceiptOrder phase.low
          (restore entry (phase.drain current)).excluded
          (phase.drain (restore entry (phase.drain current))).native.accepted :=
        (BindingReceiptOrder.of_prefix restoredReceipts saved).congr (phase.drain_tables _).1
      simp only [settle]
      split
      · rename_i finished
        split
        · rename_i failure
          split
          · refine ⟨⟨⟨adjacent, last, saved, rebuiltWithin⟩, restoredReceipts,
              rebuilt.receipts, ?_⟩, ?_⟩
            · intro target named
              simp only [List.head?_cons, Option.mem_some_iff] at named
              subst target
              exact rebuilt
            · intro target named _commitment
              simp only [List.head?_cons, Option.mem_some_iff] at named
              subst target
              exact rebuiltOrder
          · rename_i exhausted
            have allExcluded : phase.owners ⊆ (restore entry (phase.drain current)).excluded := by
              intro owner owned
              by_contra outside
              exact exhausted ⟨owner, Finset.mem_sdiff.mpr ⟨owned, outside⟩⟩
            have completed := phase.drain_finished_of_excluded
              (restore entry (phase.drain current)) restoredWithin failure.1 allExcluded
            have next := positioned_next phase remaining _ adjacent last
              (phase.finished_prefix _ rebuiltWithin completed)
            exact ih _ _ _ _ (fresh_receiptRecord _ _ _ _
              ⟨next.adjacent, next.last, next.positioned⟩ rebuilt.receipts)
        · have next := positioned_next phase remaining _ adjacent last
            (phase.finished_prefix _ drainedWithin finished)
          exact ih _ _ _ _ (fresh_receiptRecord _ _ _ _
            ⟨next.adjacent, next.last, next.positioned⟩ drained.receipts)
      · refine ⟨⟨⟨adjacent, last, saved, drainedWithin⟩, valid.exclusion.saved,
          drained.receipts, ?_⟩, ?_⟩
        · intro target named
          simp only [List.head?_cons, Option.mem_some_iff] at named
          subst target
          exact drained
        · intro target named commitment
          simp only [List.head?_cons, Option.mem_some_iff] at named
          subst target
          exact drainedOrder commitment

/-- A permitted inclusion can install only a binding whose owned predecessors
already have receipts; subsequent normalization preserves this condition. -/
theorem ReceiptRecord.inclusionResult (runtime : EventGraphRuntime graph)
    (state : PhaseRuntimeState graph) (valid : state.ReceiptRecord)
    (message : Message Player (Payload graph)) (native : State graph)
    (authorized : state.allows message.payload = true)
    (notExcluded : state.current.excludedCall message.payload = false)
    (handled : EventGraphRuntime.handle runtime state.current.native message = some native)
    (ordered : graph.RevealRelaxedOrdered) :
    ReceiptRecord {state with current := state.current.inclusionResult message.payload native} := by
  refine ⟨valid.exclusion.inclusionResult runtime state message native authorized handled, ?_⟩
  intro phase member commitment
  have previous := valid.ordered phase member commitment
  rcases handle_tables_cases runtime state.current.native native message handled with
    ⟨event, candidate, call, _fixed, table, _owner⟩ | ⟨table, _fixed⟩
  · obtain ⟨selected, selectedMember, actual, named, inside⟩ :=
      allows_event state message.payload authorized
    rw [call] at named
    have sameEvent : actual = event := Option.some.inj named.symm
    subst actual
    have samePhase : selected = phase := by
      cases phases : state.phases with
      | nil => simp only [phases, List.head?_nil, Option.not_mem_none] at member
      | cons first rest =>
          simp only [phases, List.head?_cons, Option.mem_some_iff] at member selectedMember
          exact selectedMember.symm.trans member
    subst selected
    obtain ⟨lower, upper⟩ := (phase.mem_events event).mp inside
    have binding := phase.fields event lower upper
    rw [commitment] at binding
    obtain ⟨owner, payload, output⟩ := binding
    have actor := EventGraph.actor?_of_outputLayout_binding graph output
    have active : owner ∉ state.current.excluded := by
      rw [call] at notExcluded
      simpa only [RecoveryState.excludedCall, Payload.event?, RecoveryState.excludedEvent,
        actor, Option.any_some, decide_eq_false_iff_not] using notExcluded
    obtain ⟨actual, namedActual, ready, _action, _supported⟩ :=
      handle_config_mem_step runtime state.current.native native message handled
    rw [call] at namedActual
    have same : actual = event := Option.some.inj namedActual.symm
    subst actual
    obtain ⟨atEntry, predecessors⟩ :=
      (valid.exclusion.installed phase member).ready_binding_receipts ordered event ready
        owner payload output active
    exact (previous.install event candidate owner payload output atEntry predecessors).congr table
  · exact previous.congr table

/-- Native chance, clock and expiry never install accepted commitment handles. -/
theorem ReceiptRecord.environmentResult (runtime : EventGraphRuntime graph)
    (state : PhaseRuntimeState graph) (valid : state.ReceiptRecord)
    (command : EnvironmentCommand graph) (native : State graph)
    (authorized : state.commandAllowed command = true)
    (supported : native ∈ (environmentStep runtime state.current.native command).support) :
    ReceiptRecord {state with current := state.current.environmentResult command native} := by
  refine ⟨valid.exclusion.environmentResult runtime state command native authorized supported, ?_⟩
  intro phase member commitment
  exact (valid.ordered phase member commitment).congr
    (environmentStep_tables runtime _ native command supported).1

/-- The actual native input state has no receipt for a source event. -/
theorem initial_receiptRecord (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).ReceiptRecord := by
  apply settle_receiptRecord
  have rawFrontier : Frontier (⟨plan.phases, 0, ⟨State.initial inputs, ∅⟩,
      ⟨State.initial inputs, ∅⟩, []⟩ : PhaseRuntimeState graph) := by
    refine ⟨plan.adjacent, plan.last, ?_⟩
    cases phases : plan.phases with
    | nil =>
        have noEvents := plan.empty phases
        constructor
        · omega
        · intro event
          exact Fin.elim0 (noEvents ▸ event)
    | cons phase remaining =>
        have low := plan.first phase (by simp only [phases, List.head?_cons, Option.mem_some_iff])
        have atLow : (State.initial inputs).config.cut.IsPrefix phase.low := by
          constructor
          · omega
          · intro event
            simp only [State.initial, Config.initial, EventOrder.Cut.empty, Finset.notMem_empty,
              low, Nat.not_lt_zero]
        exact ⟨atLow, atLow.within phase.nonempty.le⟩
  exact fresh_receiptRecord _ _ _ _ rawFrontier (State.ReceiptsComplete.initial inputs)

end PhaseRuntimeState

/-- Every genuine dispatcher operation preserves accepted receipt order. -/
theorem phaseApplication_receiptRecord (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (ordered : graph.RevealRelaxedOrdered) :
    (phaseApplication runtime leaks).Invariant PhaseRuntimeState.ReceiptRecord where
  submit state who material valid := by
    refine ⟨(phaseApplication_exclusionRecord runtime leaks).submit state who material
      valid.exclusion, ?_⟩
    intro phase member commitment
    have same := (submitStep_publicView (material.call.register state.current.native who) who
      material.call.packet).trans (material.call.register_facts who state.current.native).2
    exact (valid.ordered phase member commitment).congr (congrArg PublicView.accepted same)
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · rename_i allowed
      obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
      have notExcluded : state.current.excludedCall message.payload.packet.call = false := by
        cases value : state.current.excludedCall message.payload.packet.call with
        | false => rfl
        | true =>
            simp only [value, Bool.not_true, Bool.and_false, Bool.false_eq_true] at allowed
      exact PhaseRuntimeState.settle_receiptRecord _ _ _ _ _
        (valid.inclusionResult runtime state _ native authorized notExcluded handled ordered)
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rename_i allowed
      rw [PMF.support_map] at reached
      obtain ⟨native, supported, rfl⟩ := reached
      exact PhaseRuntimeState.settle_receiptRecord _ _ _ _ _
        (valid.environmentResult runtime state command native allowed supported)
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- Actual initialized histories supply the owned receipt condition required by
typed source readback, including after arbitrarily many permitted retries. -/
theorem phaseReceiptRecord_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (ordered : graph.RevealRelaxedOrdered) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.ReceiptRecord :=
  (phaseApplication_receiptRecord runtime leaks ordered).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_receiptRecord plan draw) trace

end Vegas.EventGraphRuntime
