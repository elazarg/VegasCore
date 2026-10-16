/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSavedExclusionReadback
import Vegas.Pending.PhaseArchiveGeneration
import Vegas.Game.CompiledRevealPhase
import Vegas.Source.CommitRecoveryInstructions

/-! # Public numeric source chronology from the literal native attempt records -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace RuntimePhasePlan

/-- The saved source rank at an instruction position in the actual static
phase partition. A public instruction saves its own current position. -/
def sourceSavedRank (plan : RuntimePhasePlan graph) (rank : Nat) : Nat :=
  match plan.phases.find? (fun phase => decide (phase.low ≤ rank ∧ rank < phase.high)) with
  | none => rank
  | some phase => if phase.kind = .commitment then phase.low else rank

/-- One completed static interval contributes its post-instruction addresses.
Only public failure footprints and numeric phase metadata are consulted. -/
def sourceAddressInterval (plan : RuntimePhasePlan graph)
    (failuresBefore : Nat → Finset Player) (inherited : Finset Player)
    (generation low high : Nat) : List (Option Nat × (Finset Player × Nat × Nat)) :=
  (List.range (high - low)).map fun offset =>
    let rank := low + offset + 1
    (some rank, inherited ∪ failuresBefore rank, generation, plan.sourceSavedRank rank)

/-- Scan the original completed archives in order. The final slot's address
is the actual close address; retry and exhausted close both consume that same
record, even when exhaustion leaves the generation unchanged. -/
def sourceArchiveAddresses (plan : RuntimePhasePlan graph)
    (finalFailuresBefore : Nat → Finset Player) (finalGeneration finalRank : Nat) :
    List (CommitAttemptId × (Nat → Finset Player) × Finset Player) →
      Nat → Finset Player → List (Option Nat × (Finset Player × Nat × Nat))
  | [], cursor, inherited =>
      plan.sourceAddressInterval finalFailuresBefore inherited finalGeneration cursor finalRank
  | record :: later, cursor, inherited =>
      let phase := plan.phases.find? fun phase => decide (phase.low = record.1.phase)
      let high := (phase.map RuntimePhase.high).getD record.1.phase
      let ending := inherited ∪ record.2.2
      let retry := phase.any fun phase =>
        decide (phase.kind = .commitment ∧ (phase.owners \ ending).Nonempty)
      let next := if retry then record.1.phase else high
      let nextGeneration := record.1.generation + if retry then 1 else 0
      plan.sourceAddressInterval record.2.1 inherited record.1.generation cursor record.1.phase ++
        (plan.sourceAddressInterval record.2.1 inherited record.1.generation
          record.1.phase high).dropLast ++
        [(some next, ending, nextGeneration, next)] ++
        plan.sourceArchiveAddresses finalFailuresBefore finalGeneration finalRank later next ending

end RuntimePhasePlan

variable [Fintype Player]

namespace State

/-- Public failures before each static rank, together with all ending failures.
The hidden candidate meanings and private store cells are absent. -/
def sourceFailureFootprint (state : State graph) :
    (Nat → Finset Player) × Finset Player :=
  (state.failureOwnersBefore, state.failureOwners)

theorem sourceFailureFootprint_congr {first second : State graph}
    (same : first.publicView = second.publicView) :
    first.sourceFailureFootprint = second.sourceFailureFootprint := by
  apply Prod.ext
  · funext rank
    exact failureOwnersBefore_congr same rank
  · classical
    change first.failureOwners = second.failureOwners
    ext owner
    simp only [failureOwners, Finset.mem_filter, Finset.mem_univ, true_and]
    exact exists_congr fun event => and_congr_right fun _ =>
      PublicFailure.of_publicView_eq same event

open scoped Classical in
/-- Extending a source-ranked public scan by one original event adds exactly
that event's failed owner. Repeated failures retain the same exclusion set. -/
theorem failureOwnersBefore_successor (state : State graph) (event : graph.EventId) :
    state.failureOwnersBefore (event.val + 1) =
      state.failureOwnersBefore event.val ∪ Finset.univ.filter (fun owner =>
        graph.actor? event = some owner ∧ state.PublicFailure event) := by
  classical
  ext owner
  simp only [failureOwnersBefore, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨prior, lower, acting, failed⟩
    by_cases earlier : prior.val < event.val
    · exact Or.inl ⟨prior, earlier, acting, failed⟩
    · have same : prior = event := Fin.ext (by omega)
      subst prior
      exact Or.inr ⟨acting, failed⟩
  · rintro (⟨prior, earlier, acting, failed⟩ | ⟨acting, failed⟩)
    · exact ⟨prior, by omega, acting, failed⟩
    · exact ⟨event, by omega, acting, failed⟩

open scoped Classical in
/-- The next excluded set is determined by the old set and the current public
failure. The inherited part may also contain failures from retired attempts. -/
theorem union_failureOwnersBefore_successor (state : State graph) (event : graph.EventId)
    (inherited : Finset Player) :
    inherited ∪ state.failureOwnersBefore (event.val + 1) =
      (graph.actor? event).elim (inherited ∪ state.failureOwnersBefore event.val)
        (fun owner => if state.PublicFailure event then
          insert owner (inherited ∪ state.failureOwnersBefore event.val)
        else inherited ∪ state.failureOwnersBefore event.val) := by
  classical
  rw [state.failureOwnersBefore_successor event]
  cases acting : graph.actor? event with
  | none =>
      ext who
      simp only [Option.elim_none, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, reduceCtorEq, false_and, or_false]
  | some owner =>
      by_cases failed : state.PublicFailure event
      · ext who
        simp only [Option.elim_some, failed, ↓reduceIte, Finset.mem_union,
          Finset.mem_filter, Finset.mem_univ, true_and, Option.some.injEq,
          and_true, Finset.mem_insert, eq_comm]
        tauto
      · ext who
        simp only [Option.elim_some, failed, ↓reduceIte, Finset.mem_union,
          Finset.mem_filter, Finset.mem_univ, and_false, or_false]

end State

namespace PhaseRuntimeState

/-- The original public attempt identifiers paired with their completed
failure footprints. No retired private declaration word is reconstructed. -/
def sourceControlRecords (records : List (RetiredCommitAttempt graph)) :
    List (CommitAttemptId × (Nat → Finset Player) × Finset Player) :=
  records.map fun record => (record.attempt, record.state.sourceFailureFootprint)

theorem sourceControlRecords_congr (first second : List (RetiredCommitAttempt graph))
    (same : first.map (fun record => (record.attempt, record.state.publicView)) =
      second.map (fun record => (record.attempt, record.state.publicView))) :
    sourceControlRecords first = sourceControlRecords second := by
  induction first generalizing second with
  | nil =>
      cases second with
      | nil => rfl
      | cons record later => cases same
  | cons record later ih =>
      cases second with
      | nil => cases same
      | cons other rest =>
          have parts := List.cons.inj same
          change (record.attempt, record.state.sourceFailureFootprint) :: _ =
            (other.attempt, other.state.sourceFailureFootprint) :: _
          have attempts : record.attempt = other.attempt := congrArg Prod.fst parts.1
          have publicViews : record.state.publicView = other.state.publicView :=
            congrArg Prod.snd parts.1
          exact congrArg₂ List.cons
            (Prod.ext attempts (State.sourceFailureFootprint_congr publicViews)) (ih rest parts.2)

/-- The chronological source addresses through the genuine saved boundary,
followed by the current no-new-miss commitment prefix. Setup contributes one
initial address; native WAIT callbacks contribute none. -/
def sourcePublicAddressWord (plan : RuntimePhasePlan graph) (state : PhaseRuntimeState graph)
    (eventRank : Nat) : List (Option Nat × (Finset Player × Nat × Nat)) :=
  let footprint := state.current.native.sourceFailureFootprint
  let records := sourceControlRecords state.retired
  let inherited := (records.map fun record => record.2.2).foldr (fun left right => left ∪ right) ∅
  let low := state.attempt.phase
  let saved := inherited ∪ footprint.1 low
  [(some 0, (∅, 0, 0))] ++
    plan.sourceArchiveAddresses footprint.1 state.attempt.generation low records 0 ∅ ++
    (List.range (eventRank - low)).map fun offset =>
      (some (low + offset + 1), saved, state.attempt.generation, low)

/-- The whole proposed numeric scan is a function of actual public native
information. All retired private words and candidate meanings may differ. -/
theorem sourcePublicAddressWord_congr (plan : RuntimePhasePlan graph)
    {first second : PhaseRuntimeState graph} (same : first.publicView = second.publicView)
    (eventRank : Nat) :
    first.sourcePublicAddressWord plan eventRank =
      second.sourcePublicAddressWord plan eventRank := by
  have native : first.current.native.publicView = second.current.native.publicView :=
    congrArg PhasePublicView.native same
  have archives : first.retired.map (fun record => (record.attempt, record.state.publicView)) =
      second.retired.map (fun record => (record.attempt, record.state.publicView)) :=
    congrArg PhasePublicView.retired same
  have attempt : first.attempt = second.attempt := congrArg PhasePublicView.attempt same
  simp only [sourcePublicAddressWord, State.sourceFailureFootprint_congr native,
    sourceControlRecords_congr _ _ archives, attempt]

end PhaseRuntimeState
end Vegas.EventGraphRuntime

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The retained native annotation is attached to the next original source
rank; no source retry or extra close lies inside a public instruction path. -/
theorem NativePublicSourceStep.position
    {graph : Vegas.EventGraph Player L} {Γ : SourceCtx Player L} {O : Finset VarId}
    {native : EventGraphRuntime.State graph} {offset : Nat}
    {program : SourceProgram Player L Γ O}
    {first last : ProtocolState program × Finset Player}
    (step : NativePublicSourceStep native offset program first last) :
    instructionCount program - ProtocolState.remaining program last.1 =
      instructionCount program - ProtocolState.remaining program first.1 + 1 := by
  obtain ⟨⟨running, _notCommit, joint, supported⟩, _update⟩ := step
  have consumed := ProtocolState.recoveryStep_remaining program first.1 first.2 joint last
    running supported
  have bound := ProtocolState.remaining_le_instructionCount program first.1
  omega

/-- Actual per-slot control metadata propagates the native public exclusion
scan, including chance-only steps and owners already excluded earlier. -/
theorem NativePublicSourceStep.excluded_scan [Fintype Player]
    {graph : Vegas.EventGraph Player L} {Γ : SourceCtx Player L} {O : Finset VarId}
    {native : EventGraphRuntime.State graph} {offset : Nat}
    {program : SourceProgram Player L Γ O}
    {first last : ProtocolState program × Finset Player}
    (step : NativePublicSourceStep native offset program first last)
    (event : graph.EventId)
    (ranked : event.val = offset + (instructionCount program -
      ProtocolState.remaining program first.1))
    (inherited : Finset Player)
    (before : first.2 = inherited ∪ native.failureOwnersBefore event.val) :
    last.2 = inherited ∪ native.failureOwnersBefore (event.val + 1) := by
  have update := step.2 event ranked
  rw [before] at update
  exact update.trans (native.union_failureOwnersBefore_successor event inherited).symm

/-- The complete public-instruction chunk is the deterministic native scan.
Every element is an actual post-instruction address in the retained path. -/
theorem native_public_path_addresses [Fintype Player]
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (native : EventGraphRuntime.State ((toEventGraph setup.program).withMode mode))
    (inherited : Finset Player) (generation : Nat)
    (first : ProtocolState setup.program × Finset Player)
    (states : List (ProtocolState setup.program × Finset Player))
    (chain : (first :: states).IsChain (NativePublicSourceStep native 0 setup.program))
    (before : first.2 = inherited ∪ native.failureOwnersBefore
      (instructionCount setup.program - ProtocolState.remaining setup.program first.1)) :
    states.map (fun point =>
      (CommitRecoveryState.atPoint point.1 point.2 generation).publicAddress) =
    (List.range states.length).map (fun index =>
      let rank := instructionCount setup.program -
        ProtocolState.remaining setup.program first.1 + index + 1
      (some rank, inherited ∪ native.failureOwnersBefore rank, generation, rank)) := by
  have addresses : ∀ index (bound : index < states.length),
      (CommitRecoveryState.atPoint (states[index]'bound).1
        (states[index]'bound).2 generation).publicAddress =
      let rank := instructionCount setup.program -
        ProtocolState.remaining setup.program first.1 + index + 1
      (some rank, inherited ∪ native.failureOwnersBefore rank, generation, rank) := by
    induction states generalizing first with
    | nil => intro index bound; simp only [List.length_nil] at bound; omega
    | cons middle states ih =>
        have moved := List.isChain_cons_cons.mp chain
        have nextRank := moved.1.position
        have bounded := ProtocolState.remaining_le_instructionCount setup.program first.1
        have positive : 0 < ProtocolState.remaining setup.program first.1 := by
          by_contra absent
          have stopped := (ProtocolState.remaining_zero_iff_terminal setup.program first.1).mp
            (by omega)
          exact moved.1.1.1 stopped
        let event : ((toEventGraph setup.program).withMode mode).EventId :=
          ⟨instructionCount setup.program - ProtocolState.remaining setup.program first.1, by
            change _ < eventCount setup.program
            rw [eventCount_eq_instructionCount]
            omega⟩
        have excluded := moved.1.excluded_scan event (by dsimp only [event]; omega)
          inherited before
        have nextExcluded : middle.2 = inherited ∪ native.failureOwnersBefore
            (instructionCount setup.program - ProtocolState.remaining setup.program middle.1) := by
          rw [nextRank]
          exact excluded
        intro index bound
        cases index with
        | zero =>
            change (some (instructionCount setup.program -
                ProtocolState.remaining setup.program middle.1), middle.2, generation,
              instructionCount setup.program - ProtocolState.remaining setup.program middle.1) = _
            rw [nextRank, nextExcluded, nextRank]
        | succ index =>
            have later := ih middle moved.2 nextExcluded index (by
              simp only [List.length_cons] at bound
              omega)
            simpa only [List.getElem_cons_succ, Nat.succ_eq_add_one, nextRank,
              Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later
  apply List.ext_getElem (by simp only [List.length_map, List.length_range])
  intro index bound _
  simpa only [List.getElem_map, List.getElem_range] using
    addresses index (by simpa only [List.length_map] using bound)

end Vegas
