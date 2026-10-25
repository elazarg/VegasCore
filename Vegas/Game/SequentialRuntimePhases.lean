/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompiledRuntimePhases
import Vegas.Pending.PhaseReadiness
import Mathlib.Data.List.ChainOfFn

/-! # Singleton source-ranked phases on the actual sequential graph

Every compiled event receives its own descriptor. Sequential dependencies,
rather than maximal same-kind blocks, confine readiness to the installed phase.
The ordinary phase application, settlement, clock and observations are unchanged.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)

/-- The descriptor of one actual source-ranked compiled event. -/
def sequentialRuntimePhaseAt (index : Fin (eventCount program)) :
    RuntimePhase ((toEventGraph program).withMode .sequential) where
  kind := (outputLayout_phaseKind program index).choose
  low := index.val
  high := index.val + 1
  nonempty := Nat.lt_succ_self _
  bounded := Nat.succ_le_of_lt index.isLt
  fields event lower upper := by
    have same : event = index := Fin.ext (by omega)
    subst event
    exact (outputLayout_phaseKind program index).choose_spec
  sample_singleton _ := rfl

/-- An actual binding output has the commitment descriptor kind. -/
theorem sequentialRuntimePhaseAt_kind_of_binding (index : Fin (eventCount program))
    {owner : Player} {payload : L.Ty}
    (binding : outputLayout program index = .binding owner payload) :
    (sequentialRuntimePhaseAt program index).kind = .commitment := by
  have classified := (outputLayout_phaseKind program index).choose_spec
  change (sequentialRuntimePhaseAt program index).kind.Matches (outputLayout program index)
    at classified
  rw [binding] at classified
  cases kind : (sequentialRuntimePhaseAt program index).kind <;>
    simp_all [RuntimePhaseKind.Matches]

/-- Each source instruction is one phase of the sequential compiled graph. -/
def sequentialRuntimePhasePlan :
    RuntimePhasePlan ((toEventGraph program).withMode .sequential) where
  phases := List.ofFn (sequentialRuntimePhaseAt program)
  adjacent := List.isChain_ofFn.mpr fun _ _ => rfl
  first := by
    intro phase member
    rw [List.head?_eq_getElem?, List.getElem?_ofFn] at member
    split at member
    · have same := Option.mem_some_iff.mp member
      subst phase
      rfl
    · cases member
  last := by
    intro phase member
    rw [List.getLast?_eq_getElem?, List.length_ofFn, List.getElem?_ofFn] at member
    split at member
    · have same := Option.mem_some_iff.mp member
      subst phase
      change eventCount program - 1 + 1 = eventCount program
      omega
    · cases member
  empty := by
    intro absent
    have counts := congrArg List.length absent
    change eventCount program = 0
    simpa only [List.length_ofFn, List.length_nil] using counts

@[simp]
theorem sequentialRuntimePhaseAt_events (index : Fin (eventCount program)) :
    (sequentialRuntimePhaseAt program index).events =
      {(index : ((toEventGraph program).withMode .sequential).EventId)} := by
  ext event
  rw [RuntimePhase.mem_events, Finset.mem_singleton]
  change (index.val ≤ event.val ∧ event.val < index.val + 1) ↔ event = index
  constructor
  · intro bounds
    exact Fin.ext (by omega)
  · rintro rfl
    exact ⟨le_rfl, Nat.lt_succ_self _⟩

/-- Phase owners are read from the actual compiled event, for all event kinds. -/
theorem sequentialRuntimePhaseAt_owners (index : Fin (eventCount program)) :
    (sequentialRuntimePhaseAt program index).owners =
      (((toEventGraph program).withMode .sequential).actor? index).toFinset := by
  rw [RuntimePhase.owners, sequentialRuntimePhaseAt_events, Finset.singleton_biUnion]

@[simp]
theorem mem_sequentialRuntimePhasePlan
    (phase : RuntimePhase ((toEventGraph program).withMode .sequential)) :
    phase ∈ (sequentialRuntimePhasePlan program).phases ↔
      ∃ index, phase = sequentialRuntimePhaseAt program index := by
  simp only [sequentialRuntimePhasePlan, List.mem_ofFn, eq_comm]

/-- Membership has a unique source-ranked descriptor, without a supplied partition. -/
theorem event_mem_sequentialRuntimePhasePlan
    (phase : RuntimePhase ((toEventGraph program).withMode .sequential))
    (event : Fin (eventCount program)) :
    (phase ∈ (sequentialRuntimePhasePlan program).phases ∧ event ∈ phase.events) ↔
      phase = sequentialRuntimePhaseAt program event := by
  constructor
  · rintro ⟨member, inside⟩
    obtain ⟨index, rfl⟩ := (mem_sequentialRuntimePhasePlan program phase).mp member
    rw [sequentialRuntimePhaseAt_events, Finset.mem_singleton] at inside
    exact congrArg (sequentialRuntimePhaseAt program) inside.symm
  · rintro rfl
    exact ⟨(mem_sequentialRuntimePhasePlan program _).mpr ⟨event, rfl⟩, by simp⟩

/-- Every commitment, reveal and chance phase is singleton in this plan. -/
theorem sequentialRuntimePhasePlan_singleton :
    ∀ phase ∈ (sequentialRuntimePhasePlan program).phases, phase.high = phase.low + 1 := by
  intro phase member
  obtain ⟨index, rfl⟩ := (mem_sequentialRuntimePhasePlan program phase).mp member
  rfl

end Vegas

namespace Vegas.EventGraphRuntime.RuntimePhase

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Total source order confines readiness to any unfinished installed interval.
No maximal-kind boundary condition is needed on a sequential graph. -/
theorem ready_mem_sequential (phase : RuntimePhase graph.sequentialize)
    (state : RecoveryState graph.sequentialize)
    (within : state.native.config.cut.Within phase.low phase.high)
    (unfinished : ¬ phase.Finished state)
    (event : graph.EventId) (ready : state.native.config.cut.Ready event) :
    event ∈ phase.events := by
  have lower : phase.low ≤ event.val := by
    by_contra below
    exact ready.1 (within.1 event (by omega))
  have missing : ∃ other ∈ phase.events, other ∉ state.native.config.cut.completed := by
    by_contra absent
    apply unfinished
    intro other inside
    by_contra incomplete
    exact absent ⟨other, inside, incomplete⟩
  obtain ⟨other, inside, incomplete⟩ := missing
  have least := graph.sequentialize_ready_le_unfinished state.native.config.cut ready incomplete
  exact (phase.mem_events event).mpr
    ⟨lower, lt_of_le_of_lt least ((phase.mem_events other).mp inside).2⟩

end Vegas.EventGraphRuntime.RuntimePhase

namespace Vegas.EventGraphRuntime.PhaseRuntimeState

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The sequential phase engine drains every excluded-owner readiness, even
when adjacent descriptors have the same kind. -/
theorem settle_global_quiescent_sequential
    (phases : List (RuntimePhase graph.sequentialize)) (generation : Nat)
    (entry current : RecoveryState graph.sequentialize)
    (retired : List (RetiredCommitAttempt graph.sequentialize))
    (valid : Frontier (⟨phases, generation, entry, current, retired⟩ :
      PhaseRuntimeState graph.sequentialize)) :
    ∀ event, ¬ (settle phases generation entry current retired).current.AutomaticReady event := by
  have result := settle_frontier phases generation entry current retired valid
  intro event eligible
  cases installed : (settle phases generation entry current retired).phases with
  | nil =>
      have terminal := result.terminal installed
      exact eligible.1.1 ((Finset.eq_univ_iff_forall.mp terminal) event)
  | cons phase remaining =>
      have positioned := result.positioned
      rw [installed] at positioned
      have head : phase ∈ (settle phases generation entry current retired).phases.head? := by
        simp only [installed, List.head?_cons, Option.mem_some_iff]
      have unfinished :=
        settle_unfinished phases generation entry current retired valid phase head
      have inside := phase.ready_mem_sequential _ positioned.2 unfinished event eligible.1
      exact settle_quiescent phases generation entry current retired phase head event inside
        eligible

end Vegas.EventGraphRuntime.PhaseRuntimeState

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Arbitrary responses and scheduler commands preserve sequential frontier
geometry and suppress excluded-owner readiness in the same phase application. -/
theorem phaseApplication_quiescent_sequential (runtime : EventGraphRuntime graph.sequentialize)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph.sequentialize)) :
    (phaseApplication runtime leaks).Invariant (fun state =>
      state.Frontier ∧ ∀ event, ¬ state.current.AutomaticReady event) where
  submit state who submission valid :=
    ⟨state.submit_frontier who submission valid.1,
      state.current.submit_quiescent who submission valid.2⟩
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · rename_i allowed
      obtain ⟨native, rawAccepted, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have authorized := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp allowed).1).2
      obtain ⟨phase, member, event, named, inside⟩ :=
        PhaseRuntimeState.allows_event state _ authorized
      obtain ⟨actual, actualNamed, ready, action, supported⟩ :=
        handle_config_mem_step runtime state.current.native native _ rawAccepted
      have same : actual = event := Option.some.inj (actualNamed.symm.trans named)
      subst actual
      have raw := valid.1.after_effect
        (state.current.inclusionResult message.payload.packet.call native)
        (Or.inr ⟨phase, member, event, inside, ready, action, supported⟩)
      exact ⟨PhaseRuntimeState.settle_frontier _ _ _ _ _ raw,
        PhaseRuntimeState.settle_global_quiescent_sequential _ _ _ _ _ raw⟩
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rename_i allowed
      rw [PMF.support_map] at reached
      obtain ⟨native, rawReached, rfl⟩ := reached
      have raw := valid.1.after_effect (state.current.environmentResult command native)
        (state.command_effect runtime command native allowed rawReached)
      exact ⟨PhaseRuntimeState.settle_frontier _ _ _ _ _ raw,
        PhaseRuntimeState.settle_global_quiescent_sequential _ _ _ _ _ raw⟩
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- The actual sequential initialization has the same frontier and quiescence
interface without requiring maximal adjacent source blocks. -/
theorem phaseApplication_initial_quiescent_sequential
    (plan : RuntimePhasePlan graph.sequentialize) (inputs : graph.sequentialize.Inputs) :
    (PhaseRuntimeState.initial plan inputs).Frontier ∧
      ∀ event, ¬ (PhaseRuntimeState.initial plan inputs).current.AutomaticReady event :=
  ⟨PhaseRuntimeState.initial_frontier plan inputs,
    PhaseRuntimeState.settle_global_quiescent_sequential _ _ _ _ _
      (PhaseRuntimeState.initial_checkpoint_frontier plan inputs)⟩

end Vegas.EventGraphRuntime
