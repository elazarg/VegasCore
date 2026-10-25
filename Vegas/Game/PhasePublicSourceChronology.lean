/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseArchiveGeneration
import Vegas.Pending.PhaseArchivedBindingInterval
import Vegas.Game.CompiledRevealPhase
import Vegas.Pending.PhaseNamespace

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

omit [DecidableEq Player] in
/-- Public instructions save their new cursor, including the boundary at
which the next maximal commitment interval begins. -/
theorem sourceSavedRank_of_public_interval (plan : RuntimePhasePlan graph)
    (phase : RuntimePhase graph) (member : phase ∈ plan.phases)
    (noncommit : phase.kind ≠ .commitment) (rank : Nat)
    (lower : phase.low < rank) (upper : rank ≤ phase.high) :
    plan.sourceSavedRank rank = rank := by
  classical
  unfold sourceSavedRank
  cases found : plan.phases.find? (fun current =>
      decide (current.low ≤ rank ∧ rank < current.high)) with
  | none => rfl
  | some current =>
      have currentMember := List.mem_of_find?_eq_some found
      have contains : current.low ≤ rank ∧ rank < current.high :=
        of_decide_eq_true (List.find?_some
          (p := fun other : RuntimePhase graph =>
            decide (other.low ≤ rank ∧ rank < other.high)) found)
      change (if current.kind = .commitment then current.low else rank) = rank
      by_cases committing : current.kind = .commitment
      · rw [ite_eq_left committing]
        by_contra different
        have currentLower : current.low < rank := by omega
        let previous : graph.EventId := ⟨rank - 1, by
          have bounded := phase.bounded
          omega⟩
        have same := containing_unique plan.phases plan.adjacent previous phase current
          member currentMember
          ((phase.mem_events previous).mpr ⟨by dsimp only [previous]; omega,
            by dsimp only [previous]; omega⟩)
          ((current.mem_events previous).mpr ⟨by dsimp only [previous]; omega,
            by dsimp only [previous]; omega⟩)
        exact noncommit (same.symm ▸ committing)
      · rw [ite_eq_right committing]

omit [DecidableEq Player] in
/-- An original static entry rank selects its unique descriptor. -/
theorem find_low_eq_of_mem (plan : RuntimePhasePlan graph) (phase : RuntimePhase graph)
    (member : phase ∈ plan.phases) :
    plan.phases.find? (fun current => decide (current.low = phase.low)) = some phase := by
  classical
  cases found : plan.phases.find? (fun current => decide (current.low = phase.low)) with
  | none =>
      have absent := (List.find?_eq_none.mp found) phase member
      exact (absent (decide_eq_true rfl)).elim
  | some current =>
      have currentMember := List.mem_of_find?_eq_some found
      have sameLow : current.low = phase.low :=
        of_decide_eq_true (List.find?_some
          (p := fun other : RuntimePhase graph => decide (other.low = phase.low)) found)
      have same := plan.phase_eq_of_low_eq current phase currentMember member sameLow
      exact congrArg some same

/-- One completed static interval contributes its post-instruction addresses.
Only public failure footprints and numeric phase metadata are consulted. -/
def sourceAddressInterval (plan : RuntimePhasePlan graph)
    (failuresBefore : Nat → Finset Player) (inherited : Finset Player)
    (generation low high : Nat) : List (Option Nat × (Finset Player × Nat × Nat)) :=
  (List.range (high - low)).map fun offset =>
    let rank := low + offset + 1
    (some rank, inherited ∪ failuresBefore rank, generation, plan.sourceSavedRank rank)

/-- Consecutive source intervals concatenate at the literal shared rank. -/
theorem sourceAddressInterval_append (plan : RuntimePhasePlan graph)
    (failuresBefore : Nat → Finset Player) (inherited : Finset Player)
    (generation low middle high : Nat) (lower : low ≤ middle) (upper : middle ≤ high) :
    plan.sourceAddressInterval failuresBefore inherited generation low high =
      plan.sourceAddressInterval failuresBefore inherited generation low middle ++
        plan.sourceAddressInterval failuresBefore inherited generation middle high := by
  have distance : high - low = (middle - low) + (high - middle) := by omega
  simp only [sourceAddressInterval, distance, List.range_add, List.map_append, List.map_map,
    Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro index _
  have rank : low + (middle - low + index) + 1 = middle + index + 1 := by omega
  simp only [rank]

/-- An extension retaining old public failures retains every address strictly
inside the same saved interval, including its endpoint. -/
theorem sourceAddressInterval_congr (plan : RuntimePhasePlan graph)
    (first second : Nat → Finset Player) (inherited : Finset Player)
    (generation low high : Nat)
    (same : ∀ rank, low < rank → rank ≤ high → first rank = second rank) :
    plan.sourceAddressInterval first inherited generation low high =
      plan.sourceAddressInterval second inherited generation low high := by
  apply List.map_congr_left
  intro index bound
  have below := List.mem_range.mp bound
  have positive : low < low + index + 1 := by omega
  have bounded : low + index + 1 ≤ high := by omega
  simp only [same _ positive bounded]

omit [DecidableEq Player] in
/-- Inside a commitment interval the saved source rank is its original entry. -/
theorem sourceSavedRank_of_commitment_interval (plan : RuntimePhasePlan graph)
    (phase : RuntimePhase graph) (member : phase ∈ plan.phases)
    (committing : phase.kind = .commitment) (rank : Nat)
    (lower : phase.low ≤ rank) (upper : rank < phase.high) :
    plan.sourceSavedRank rank = phase.low := by
  classical
  unfold sourceSavedRank
  cases found : plan.phases.find? (fun current =>
      decide (current.low ≤ rank ∧ rank < current.high)) with
  | none =>
      have absent := (List.find?_eq_none.mp found) phase member
      exact (absent (decide_eq_true ⟨lower, upper⟩)).elim
  | some current =>
      have currentMember := List.mem_of_find?_eq_some found
      have contains : current.low ≤ rank ∧ rank < current.high :=
        of_decide_eq_true (List.find?_some
          (p := fun other : RuntimePhase graph =>
            decide (other.low ≤ rank ∧ rank < other.high)) found)
      let event : graph.EventId := ⟨rank, upper.trans_le phase.bounded⟩
      have same := containing_unique plan.phases plan.adjacent event current phase
        currentMember member ((current.mem_events event).mpr contains)
        ((phase.mem_events event).mpr ⟨lower, upper⟩)
      simp only [same, committing, ↓reduceIte]

omit [DecidableEq Player] in
/-- A completed phase boundary saves that boundary, including when the next
phase is a commitment block. -/
theorem sourceSavedRank_of_phase_high (plan : RuntimePhasePlan graph)
    (phase : RuntimePhase graph) (member : phase ∈ plan.phases) :
    plan.sourceSavedRank phase.high = phase.high := by
  classical
  unfold sourceSavedRank
  cases found : plan.phases.find? (fun current =>
      decide (current.low ≤ phase.high ∧ phase.high < current.high)) with
  | none => rfl
  | some current =>
      have currentMember := List.mem_of_find?_eq_some found
      have contains : current.low ≤ phase.high ∧ phase.high < current.high :=
        of_decide_eq_true (List.find?_some
          (p := fun other : RuntimePhase graph =>
            decide (other.low ≤ phase.high ∧ phase.high < other.high)) found)
      change (if current.kind = .commitment then current.low else phase.high) = phase.high
      by_cases committing : current.kind = .commitment
      · rw [ite_eq_left committing]
        by_contra different
        let previous : graph.EventId := ⟨phase.high - 1, by
          have bounded := phase.bounded
          have positive := phase.nonempty
          omega⟩
        have same := containing_unique plan.phases plan.adjacent previous phase current
          member currentMember
          ((phase.mem_events previous).mpr ⟨by
            have positive := phase.nonempty
            dsimp only [previous]
            omega, by
            have positive := phase.nonempty
            dsimp only [previous]
            omega⟩)
          ((current.mem_events previous).mpr ⟨by dsimp only [previous]; omega,
            by dsimp only [previous]; omega⟩)
        rw [← same] at contains
        omega
      · rw [ite_eq_right committing]

/-- The interior of a commitment interval keeps the original saved cursor;
its last slot is reserved for the real close instead. -/
theorem sourceAddressInterval_commit_dropLast (plan : RuntimePhasePlan graph)
    (failures : Nat → Finset Player) (inherited : Finset Player) (generation : Nat)
    (phase : RuntimePhase graph) (member : phase ∈ plan.phases)
    (kind : phase.kind = .commitment) :
    (plan.sourceAddressInterval failures inherited generation phase.low phase.high).dropLast =
      (List.range (phase.high - phase.low - 1)).map (fun index =>
        (some (phase.low + index + 1), inherited ∪ failures (phase.low + index + 1),
          generation, phase.low)) := by
  unfold sourceAddressInterval
  apply List.ext_getElem
  · simp only [List.length_dropLast, List.length_map, List.length_range]
  · intro index bound _
    simp only [List.length_dropLast, List.length_map, List.length_range] at bound
    have lower : phase.low ≤ phase.low + index + 1 := by omega
    have upper : phase.low + index + 1 < phase.high := by omega
    simp only [List.getElem_dropLast, List.getElem_map, List.getElem_range,
      plan.sourceSavedRank_of_commitment_interval phase member kind _ lower upper]

/-- Split an actual completed interval at its real last post-step address. -/
theorem sourceAddressInterval_last (plan : RuntimePhasePlan graph)
    (failures : Nat → Finset Player) (inherited : Finset Player) (generation : Nat)
    (phase : RuntimePhase graph) (member : phase ∈ plan.phases) :
    plan.sourceAddressInterval failures inherited generation phase.low phase.high =
      (plan.sourceAddressInterval failures inherited generation phase.low phase.high).dropLast ++
        [(some phase.high, inherited ∪ failures phase.high, generation, phase.high)] := by
  have count : phase.high - phase.low = (phase.high - phase.low - 1) + 1 := by
    have positive := phase.nonempty
    omega
  have rank : phase.low + (phase.high - phase.low - 1) + 1 = phase.high := by
    have positive := phase.nonempty
    omega
  have split : plan.sourceAddressInterval failures inherited generation phase.low phase.high =
      (List.range (phase.high - phase.low - 1)).map (fun offset =>
        let current := phase.low + offset + 1
        (some current, inherited ∪ failures current, generation, plan.sourceSavedRank current)) ++
        [(some phase.high, inherited ∪ failures phase.high, generation, phase.high)] := by
    unfold sourceAddressInterval
    conv_lhs => rw [count, List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil, rank,
      plan.sourceSavedRank_of_phase_high phase member]
  rw [split, List.dropLast_concat]

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

/-- The cursor after consuming exactly the retained completed archives.
Successful later phases do not add a record and may advance beyond this rank. -/
def sourceArchiveCursor (plan : RuntimePhasePlan graph) :
    List (CommitAttemptId × (Nat → Finset Player) × Finset Player) → Nat → Finset Player → Nat
  | [], cursor, _inherited => cursor
  | record :: later, _cursor, inherited =>
      let phase := plan.phases.find? fun phase => decide (phase.low = record.1.phase)
      let high := (phase.map RuntimePhase.high).getD record.1.phase
      let ending := inherited ∪ record.2.2
      let retry := phase.any fun phase =>
        decide (phase.kind = .commitment ∧ (phase.owners \ ending).Nonempty)
      let next := if retry then record.1.phase else high
      plan.sourceArchiveCursor later next ending

/-- Advancing a successful phase appends only its new instruction interval;
the old consumed-archive prefix and every real close are retained literally. -/
theorem sourceArchiveAddresses_extend (plan : RuntimePhasePlan graph)
    (failures : Nat → Finset Player) (generation low high : Nat)
    (records : List (CommitAttemptId × (Nat → Finset Player) × Finset Player))
    (cursor : Nat) (inherited : Finset Player)
    (bounded : plan.sourceArchiveCursor records cursor inherited ≤ low) (upper : low ≤ high) :
    plan.sourceArchiveAddresses failures generation high records cursor inherited =
      plan.sourceArchiveAddresses failures generation low records cursor inherited ++
        plan.sourceAddressInterval failures
          (inherited ∪ (records.map fun record => record.2.2).foldr
            (fun left right => left ∪ right) ∅) generation low high := by
  induction records generalizing cursor inherited with
  | nil =>
      simpa only [sourceArchiveCursor, sourceArchiveAddresses, List.map_nil, List.foldr_nil,
        Finset.union_empty] using
          plan.sourceAddressInterval_append failures inherited generation cursor low high
            bounded upper
  | cons record rest ih =>
      simp only [sourceArchiveCursor] at bounded
      simp only [sourceArchiveAddresses, List.map_cons, List.foldr_cons]
      rw [ih _ _ bounded]
      simp only [List.append_assoc, Finset.union_assoc]

/-- The inherited ending set of a chronological archive list. This reads
only the retained public failure-owner sets. -/
def sourceRecordFailures
    (records : List (CommitAttemptId × (Nat → Finset Player) × Finset Player)) : Finset Player :=
  (records.map fun record => record.2.2).foldr (fun left right => left ∪ right) ∅

/-- Appending one real completed attempt to the public scan consumes its
interior slots and its single close exactly once. -/
theorem sourceArchiveAddresses_append (plan : RuntimePhasePlan graph)
    (finalFailures : Nat → Finset Player) (finalGeneration finalRank : Nat)
    (records : List (CommitAttemptId × (Nat → Finset Player) × Finset Player))
    (record : CommitAttemptId × (Nat → Finset Player) × Finset Player)
    (cursor : Nat) (inherited : Finset Player) :
    plan.sourceArchiveAddresses finalFailures finalGeneration finalRank (records ++ [record])
        cursor inherited =
      let current := inherited ∪ sourceRecordFailures records
      let phase := plan.phases.find? fun phase => decide (phase.low = record.1.phase)
      let high := (phase.map RuntimePhase.high).getD record.1.phase
      let ending := current ∪ record.2.2
      let retry := phase.any fun phase =>
        decide (phase.kind = .commitment ∧ (phase.owners \ ending).Nonempty)
      let next := if retry then record.1.phase else high
      let nextGeneration := record.1.generation + if retry then 1 else 0
      plan.sourceArchiveAddresses record.2.1 record.1.generation record.1.phase records
          cursor inherited ++
        (plan.sourceAddressInterval record.2.1 current record.1.generation
          record.1.phase high).dropLast ++
        [(some next, ending, nextGeneration, next)] ++
        plan.sourceAddressInterval finalFailures ending finalGeneration next finalRank := by
  induction records generalizing cursor inherited with
  | nil =>
      simp only [List.nil_append, sourceRecordFailures, List.map_nil, List.foldr_nil,
        Finset.union_empty, sourceArchiveAddresses]
  | cons first rest ih =>
      simp only [List.cons_append, sourceArchiveAddresses, sourceRecordFailures,
        List.map_cons, List.foldr_cons]
      rw [ih]
      simp only [sourceRecordFailures, List.append_assoc, Finset.union_assoc]

/-- A newly consumed archive leaves its actual retry or exhausted cursor,
regardless of the old successful intervals between archived attempts. -/
theorem sourceArchiveCursor_append (plan : RuntimePhasePlan graph)
    (records : List (CommitAttemptId × (Nat → Finset Player) × Finset Player))
    (record : CommitAttemptId × (Nat → Finset Player) × Finset Player)
    (cursor : Nat) (inherited : Finset Player) :
    plan.sourceArchiveCursor (records ++ [record]) cursor inherited =
      let phase := plan.phases.find? fun phase => decide (phase.low = record.1.phase)
      let high := (phase.map RuntimePhase.high).getD record.1.phase
      let ending := (inherited ∪ sourceRecordFailures records) ∪ record.2.2
      let retry := phase.any fun phase =>
        decide (phase.kind = .commitment ∧ (phase.owners \ ending).Nonempty)
      if retry then record.1.phase else high := by
  induction records generalizing cursor inherited with
  | nil =>
      simp only [List.nil_append, sourceRecordFailures, List.map_nil, List.foldr_nil,
        Finset.union_empty, sourceArchiveCursor]
  | cons first rest ih =>
      simp only [List.cons_append, sourceArchiveCursor]
      rw [ih]
      simp only [sourceRecordFailures, List.map_cons, List.foldr_cons, Finset.union_assoc]

/-- The final native footprint is used only at ranks already reached by the
saved boundary. Retired masks are read from their own immutable records. -/
theorem sourceArchiveAddresses_congr (plan : RuntimePhasePlan graph)
    (first second : Nat → Finset Player) (generation rank : Nat)
    (records : List (CommitAttemptId × (Nat → Finset Player) × Finset Player))
    (cursor : Nat) (inherited : Finset Player)
    (same : ∀ position ≤ rank, first position = second position) :
    plan.sourceArchiveAddresses first generation rank records cursor inherited =
      plan.sourceArchiveAddresses second generation rank records cursor inherited := by
  induction records generalizing cursor inherited with
  | nil =>
      exact plan.sourceAddressInterval_congr first second inherited generation cursor rank
        (fun position _ bounded => same position bounded)
  | cons record later ih =>
      simp only [sourceArchiveAddresses]
      rw [ih]


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

theorem sourceRecordFailures_sourceControlRecords (records : List (RetiredCommitAttempt graph)) :
    RuntimePhasePlan.sourceRecordFailures (sourceControlRecords records) =
      archivedFailureOwners records := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      change record.state.failureOwners ∪ RuntimePhasePlan.sourceRecordFailures
          (sourceControlRecords rest) = record.state.failureOwners ∪ archivedFailureOwners rest
      exact congrArg (record.state.failureOwners ∪ ·) ih

/-- Consuming the actual completed image leaves exactly its real close
cursor. The failure set is derived from the original archive invariant. -/
theorem sourceArchiveCursor_after_completed
    (plan : RuntimePhasePlan graph) (state : PhaseRuntimeState graph)
    (phase : RuntimePhase graph) (member : phase ∈ plan.phases)
    (kind : phase.kind = .commitment) (archives : state.ArchivedExclusions) :
    plan.sourceArchiveCursor
        (sourceControlRecords (state.retired ++
          [⟨⟨phase.low, state.generation⟩, (phase.drain state.current).native⟩])) 0 ∅ =
      if (phase.owners \ (phase.drain state.current).excluded).Nonempty
        then phase.low else phase.high := by
  classical
  have ending := (archives.active.phase_drain phase).failureOwners_union
  rw [sourceControlRecords, List.map_append]
  change plan.sourceArchiveCursor
    (sourceControlRecords state.retired ++
      [(⟨phase.low, state.generation⟩, (phase.drain state.current).native.sourceFailureFootprint)])
    0 ∅ = _
  rw [plan.sourceArchiveCursor_append]
  change (let selected := plan.phases.find? (fun current => decide (current.low = phase.low))
    let ending := (∅ ∪ RuntimePhasePlan.sourceRecordFailures
      (sourceControlRecords state.retired)) ∪ (phase.drain state.current).native.failureOwners
    let retry := selected.any fun current =>
      decide (current.kind = .commitment ∧ (current.owners \ ending).Nonempty)
    if retry then phase.low else (selected.map RuntimePhase.high).getD phase.low) = _
  rw [plan.find_low_eq_of_mem phase member, Finset.empty_union,
    sourceRecordFailures_sourceControlRecords, ← ending]
  by_cases survives : (phase.owners \ (phase.drain state.current).excluded).Nonempty
  · simp only [Option.any_some, kind, true_and, survives, decide_true,
      ↓reduceIte]
  · simp only [Option.any_some, kind, true_and, survives, decide_false, Bool.false_eq_true,
      ↓reduceIte, Option.map_some, Option.getD_some]

/-- Every archived prefix of an actual history ends before the next archived
entry; the whole archive ends before the current saved entry. -/
theorem sourceArchivePrefix_history (runtime : EventGraphRuntime graph)
    (leaks : Interaction.MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (initial plan)) horizon scheduler).Trace (some control)) :
    let state := control.execution.application
    plan.sourceArchiveCursor (sourceControlRecords state.retired) 0 ∅ ≤ state.attempt.phase ∧
      ∀ j : Fin state.retired.length,
        plan.sourceArchiveCursor (sourceControlRecords (state.retired.take j.val)) 0 ∅ ≤
          state.retired[j].attempt.phase := by
  classical
  let bounded : PhaseRuntimeState graph → Prop := fun state =>
    plan.sourceArchiveCursor (sourceControlRecords state.retired) 0 ∅ ≤ state.attempt.phase ∧
      ∀ j : Fin state.retired.length,
        plan.sourceArchiveCursor (sourceControlRecords (state.retired.take j.val)) 0 ∅ ≤
          state.retired[j].attempt.phase
  have settleBound (phases : List (RuntimePhase graph)) (generation : Nat)
      (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
      (suffix : phases <:+ plan.phases)
      (failures : (⟨phases, generation, entry, current, retired⟩ :
        PhaseRuntimeState graph).ArchivedExclusions)
      (prior : bounded ⟨phases, generation, entry, current, retired⟩) :
      bounded (settle phases generation entry current retired) := by
    have ordered := plan.adjacent.suffix suffix
    cases phases with
    | nil => exact prior
    | cons phase remaining =>
      have member : phase ∈ plan.phases := suffix.subset List.mem_cons_self
      have tailBound : phase.high ≤ phaseLow remaining := by
        cases remaining with
        | nil => exact phase.bounded
        | cons next rest => exact le_of_eq (List.isChain_cons_cons.mp ordered).1
      have tailOrdered := ordered.tail
      let record : RetiredCommitAttempt graph :=
        ⟨⟨phase.low, generation⟩, (phase.drain current).native⟩
      have archiveBound : ∀ j : Fin (retired ++ [record]).length,
          plan.sourceArchiveCursor (sourceControlRecords
            ((retired ++ [record]).take j.val)) 0 ∅ ≤
              (retired ++ [record])[j].attempt.phase := by
        intro j
        by_cases old : j.val < retired.length
        · simpa only [Fin.getElem_fin, List.take_append_of_le_length (Nat.le_of_lt old),
            List.getElem_append_left old] using prior.2 ⟨j.val, old⟩
        · have last : j.val = retired.length := by
            have bound := j.isLt
            simp only [List.length_append, List.length_singleton] at bound
            omega
          simpa only [Fin.getElem_fin, record, last, List.take_left,
            List.getElem_append_right (le_refl _), Nat.sub_self,
            List.getElem_cons_zero, PhaseRuntimeState.attempt, List.head?_cons,
            Option.map_some, Option.getD_some] using prior.1
      simp only [settle]
      split
      · split
        · rename_i missed
          have consumed := sourceArchiveCursor_after_completed plan
            (⟨phase :: remaining, generation, entry, current, retired⟩ : PhaseRuntimeState graph)
            phase member missed.1 failures
          split
          · rename_i survivors
            refine ⟨?_, archiveBound⟩
            change plan.sourceArchiveCursor (sourceControlRecords
              (retired ++ [⟨⟨phase.low, generation⟩,
                (phase.drain current).native⟩])) 0 ∅ ≤ phase.low
            rw [consumed, ite_eq_left survivors]
          · rename_i exhausted
            let rebuilt := phase.drain (restore entry (phase.drain current))
            let records := retired ++ [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩]
            have fresh := settle_generation_archive_of_same_excluded remaining generation
              rebuilt rebuilt records rfl
            have later :=
              (settle_namespace remaining generation rebuilt rebuilt records tailOrdered).2
            change bounded (settle remaining generation rebuilt rebuilt records)
            dsimp only [bounded]
            refine ⟨?_, ?_⟩
            · rw [fresh.2]
              have consumedBound :
                  plan.sourceArchiveCursor (sourceControlRecords records) 0 ∅ ≤ phase.high := by
                rw [consumed, ite_eq_right exhausted]
              exact consumedBound.trans (tailBound.trans later)
            · intro j
              have inside : j.val < records.length := Eq.mp
                (congrArg (fun bound : Nat => j.val < bound) (congrArg List.length fresh.2)) j.isLt
              simpa only [Fin.getElem_fin, fresh.2] using archiveBound ⟨j.val, inside⟩
        · have fresh := settle_generation_archive_of_same_excluded remaining generation
            (phase.drain current) (phase.drain current) retired rfl
          have later := (settle_namespace remaining generation (phase.drain current)
            (phase.drain current) retired tailOrdered).2
          change bounded (settle remaining generation (phase.drain current)
            (phase.drain current) retired)
          dsimp only [bounded]
          refine ⟨?_, ?_⟩
          · rw [fresh.2]
            exact prior.1.trans (phase.nonempty.le.trans (tailBound.trans later))
          · intro j
            have inside : j.val < retired.length := Eq.mp
              (congrArg (fun bound : Nat => j.val < bound) (congrArg List.length fresh.2)) j.isLt
            simpa only [Fin.getElem_fin, fresh.2] using prior.2 ⟨j.val, inside⟩
      · exact prior
  have invariant : (phaseApplication runtime leaks).Invariant
      (fun state => state.ArchivedExclusions ∧ state.phases <:+ plan.phases ∧ bounded state) := {
    submit := by
      intro state who material valid
      exact ⟨(phaseApplication_archivedExclusions runtime leaks).submit _ _ _ valid.1,
        valid.2.1, valid.2.2⟩
    handle := by
      intro state message next valid accepted
      refine ⟨(phaseApplication_archivedExclusions runtime leaks).handle _ _ _ valid.1 accepted,
        (phaseApplication_planSuffix runtime leaks plan).handle _ _ _ valid.2.1 accepted, ?_⟩
      change state.handle runtime message = some next at accepted
      unfold PhaseRuntimeState.handle at accepted
      split at accepted
      · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
        apply settleBound state.phases state.generation state.entry
          (state.current.inclusionResult message.payload.packet.call native) state.retired
          valid.2.1 _ valid.2.2
        exact ⟨⟨valid.1.coverage.saved,
            valid.1.coverage.active.inclusionResult runtime _ native handled,
            valid.1.coverage.inherited.trans (state.current.inclusionResult_excluded_subset _ _)⟩,
          valid.1.saved, valid.1.active.inclusionResult runtime _ native handled⟩
      · cases accepted
    environment := by
      intro state command next valid reached
      refine ⟨(phaseApplication_archivedExclusions runtime leaks).environment _ _ _ valid.1 reached,
        (phaseApplication_planSuffix runtime leaks plan).environment _ _ _ valid.2.1 reached, ?_⟩
      change next ∈ (state.environment runtime command).support at reached
      unfold PhaseRuntimeState.environment at reached
      split at reached
      · obtain ⟨native, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
        apply settleBound state.phases state.generation state.entry
          (state.current.environmentResult command native) state.retired valid.2.1 _ valid.2.2
        exact ⟨⟨valid.1.coverage.saved,
            valid.1.coverage.active.environmentResult runtime command native supported,
            valid.1.coverage.inherited.trans (state.current.environmentResult_excluded_subset _ _)⟩,
          valid.1.saved, valid.1.active.environmentResult runtime command native supported⟩
      · rw [PMF.mem_support_pure_iff] at reached
        subst next
        exact valid.2.2 }
  have result := invariant.history _ horizon scheduler (fun state supported => ?_) trace
  · exact result.2.2
  · obtain ⟨input, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    refine ⟨initial_archivedExclusions plan input, settle_suffix .., ?_⟩
    apply settleBound plan.phases 0 ⟨State.initial input, ∅⟩ ⟨State.initial input, ∅⟩ []
      (List.suffix_refl _) _
      ⟨Nat.zero_le _, fun j => Fin.elim0 j⟩
    have record : ExclusionEvidence 0 ∅
        (⟨State.initial input, ∅⟩ : RecoveryState graph) :=
      (RecoveryState.FailureCoverage.initial input).exclusionEvidence
    exact ⟨⟨RecoveryState.FailureCoverage.initial input,
      RecoveryState.FailureCoverage.initial input, Finset.Subset.refl _⟩, record, record⟩

/-- Appending the genuine completed image retains its old native prefix,
all interior slots and exactly one original retry or exhausted close. -/
theorem sourceArchiveAddresses_after_completed
    (plan : RuntimePhasePlan graph) (state : PhaseRuntimeState graph)
    (phase : RuntimePhase graph) (member : phase ∈ plan.phases)
    (kind : phase.kind = .commitment) (archives : state.ArchivedExclusions)
    (finalFailures : Nat → Finset Player) (finalGeneration finalRank : Nat) :
    let image := phase.drain state.current
    let closeRank := if (phase.owners \ image.excluded).Nonempty then phase.low else phase.high
    let closeGeneration := state.generation +
      if (phase.owners \ image.excluded).Nonempty then 1 else 0
    plan.sourceArchiveAddresses finalFailures finalGeneration finalRank
        (sourceControlRecords (state.retired ++ [⟨⟨phase.low, state.generation⟩, image.native⟩]))
        0 ∅ =
      plan.sourceArchiveAddresses image.native.failureOwnersBefore state.generation phase.low
          (sourceControlRecords state.retired) 0 ∅ ++
        (plan.sourceAddressInterval image.native.failureOwnersBefore
          (archivedFailureOwners state.retired) state.generation phase.low phase.high).dropLast ++
        [(some closeRank, image.excluded, closeGeneration, closeRank)] ++
        plan.sourceAddressInterval finalFailures image.excluded finalGeneration closeRank
          finalRank := by
  classical
  dsimp only
  have ending := (archives.active.phase_drain phase).failureOwners_union
  rw [sourceControlRecords, List.map_append]
  change plan.sourceArchiveAddresses finalFailures finalGeneration finalRank
    (sourceControlRecords state.retired ++
      [(⟨phase.low, state.generation⟩, (phase.drain state.current).native.sourceFailureFootprint)])
    0 ∅ = _
  rw [plan.sourceArchiveAddresses_append]
  dsimp only [State.sourceFailureFootprint]
  rw [plan.find_low_eq_of_mem phase member, Finset.empty_union,
    sourceRecordFailures_sourceControlRecords, ← ending]
  by_cases survives : (phase.owners \ (phase.drain state.current).excluded).Nonempty
  · simp only [Option.map_some, Option.getD_some, Option.any_some, kind, true_and,
      survives, decide_true, ↓reduceIte]
  · simp only [Option.map_some, Option.getD_some, Option.any_some, kind, true_and,
      survives, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]

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

/-- The saved-boundary scan ignores later native changes above its cutoff.
All retired masks remain at their original completed images. -/
theorem sourcePublicAddressWord_eq_of_prefix {first second : PhaseRuntimeState graph}
    (plan : RuntimePhasePlan graph)
    (attempt : first.attempt = second.attempt)
    (archives : first.retired = second.retired)
    (same : ∀ rank ≤ first.attempt.phase,
      first.current.native.failureOwnersBefore rank =
        second.current.native.failureOwnersBefore rank)
    (eventRank : Nat) :
    first.sourcePublicAddressWord plan eventRank =
      second.sourcePublicAddressWord plan eventRank := by
  have scanned := plan.sourceArchiveAddresses_congr
    first.current.native.failureOwnersBefore second.current.native.failureOwnersBefore
    first.attempt.generation first.attempt.phase (sourceControlRecords first.retired) 0 ∅ same
  have boundary := same first.attempt.phase le_rfl
  simp only [sourcePublicAddressWord, State.sourceFailureFootprint]
  rw [← archives, ← attempt, boundary, scanned]

/-- The saved boundary has no unfinished current-prefix suffix. -/
theorem sourcePublicAddressWord_saved (plan : RuntimePhasePlan graph)
    (state : PhaseRuntimeState graph) :
    state.sourcePublicAddressWord plan state.attempt.phase =
      [(some 0, (∅, 0, 0))] ++ plan.sourceArchiveAddresses
        state.current.native.failureOwnersBefore state.generation state.attempt.phase
        (sourceControlRecords state.retired) 0 ∅ := by
  simp only [sourcePublicAddressWord, State.sourceFailureFootprint, Nat.sub_self,
    List.range_zero, List.map_nil, List.append_nil]
  rfl


/-- An active adjacent row outside every retired namespace obtains its handle
from the immutable native image providing that exact public gap. -/
theorem sourcePublicAddressWord_gap_provider (runtime : EventGraphRuntime graph)
    (leaks : Interaction.MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (initial plan)) horizon scheduler).Trace (some control))
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (index : Nat) (before after : Option Nat × (Finset Player × Nat × Nat))
    (first : (control.execution.application.sourcePublicAddressWord plan
      control.execution.application.attempt.phase)[index]? = some before)
    (second : (control.execution.application.sourcePublicAddressWord plan
      control.execution.application.attempt.phase)[index + 1]? = some after)
    (rank : before.1 = some event.val) (active : owner ∉ after.2.1)
    (unarchived : ∀ record ∈ control.execution.application.retired,
      before.2.2 ≠ (record.attempt.generation, record.attempt.phase)) :
    ∃ provider : State graph,
      (provider = control.execution.application.current.native ∧
          event.val < control.execution.application.attempt.phase ∨
        ∃ j : Fin control.execution.application.retired.length,
          provider = control.execution.application.retired[j].state ∧
          event.val < control.execution.application.retired[j].attempt.phase) ∧
      owner ∉ provider.failureOwnersBefore (event.val + 1) ∧
      event ∈ provider.config.cut.completed ∧
      ∃ handle, provider.accepted (.inr event) = some handle := by
  classical
  let state := control.execution.application
  let Address := Option Nat × (Finset Player × Nat × Nat)
  let R : Address → Address → Prop := fun left right => ∀ r,
    left.1 = some r → owner ∉ right.2.1 →
      (r < state.attempt.phase ∧ owner ∉ state.current.native.failureOwnersBefore (r + 1)) ∨
      (∃ record ∈ state.retired,
        r < record.attempt.phase ∧ owner ∉ record.state.failureOwnersBefore (r + 1)) ∨
      ∃ record ∈ state.retired,
        left.2.2 = (record.attempt.generation, record.attempt.phase)
  have intervalChain (failures : Nat → Finset Player) (inherited : Finset Player)
      (generation low high : Nat) (start : Address) (startRank : start.1 = some low)
      (provided : ∀ r, low ≤ r → r < high → ∀ left right : Address,
        left.1 = some r → right.2.1 = inherited ∪ failures (r + 1) → R left right) :
      List.IsChain R (start :: plan.sourceAddressInterval failures inherited
        generation low high) := by
    apply List.isChain_iff_getElem.mpr
    intro i bound
    simp only [RuntimePhasePlan.sourceAddressInterval, List.length_cons,
      List.length_map, List.length_range] at bound
    cases i with
    | zero =>
        simpa only [RuntimePhasePlan.sourceAddressInterval, List.getElem_cons_zero,
          List.getElem_cons_succ, List.getElem_map, List.getElem_range, Nat.add_zero]
          using provided low le_rfl (by omega) start
            (some (low + 1), inherited ∪ failures (low + 1),
              generation, plan.sourceSavedRank (low + 1)) startRank rfl
    | succ i =>
        simpa only [RuntimePhasePlan.sourceAddressInterval, List.getElem_cons_succ,
          List.getElem_map, List.getElem_range, Nat.succ_eq_add_one, Nat.add_assoc]
          using provided (low + i + 1) (by omega) (by omega)
            (some (low + i + 1), inherited ∪ failures (low + i + 1),
              generation, plan.sourceSavedRank (low + i + 1))
            (some (low + i + 1 + 1), inherited ∪ failures (low + i + 1 + 1),
              generation, plan.sourceSavedRank (low + i + 1 + 1)) rfl rfl
  have intervalLast (failures : Nat → Finset Player) (inherited : Finset Player)
      (generation low high : Nat) (start : Address) (lower : low ≤ high)
      (startNamespace : start.2.2 = (generation, low))
      (boundary : plan.sourceSavedRank high = high) :
      ∀ last ∈ (start :: plan.sourceAddressInterval failures inherited
        generation low high).getLast?, last.2.2 = (generation, high) := by
    by_cases equal : high = low
    · subst high
      intro last member
      simp only [RuntimePhasePlan.sourceAddressInterval, Nat.sub_self, List.range_zero,
        List.map_nil, List.getLast?_singleton, Option.mem_some_iff] at member
      cases member
      exact startNamespace
    · have positive : high - low ≠ 0 := by omega
      have endpoint : low + (high - low - 1) + 1 = high := by omega
      intro last member
      have nonempty : plan.sourceAddressInterval failures inherited generation low high ≠ [] := by
        intro empty
        have lengths := congrArg List.length empty
        simp only [RuntimePhasePlan.sourceAddressInterval, List.length_map,
          List.length_range, List.length_nil] at lengths
        exact positive lengths
      rw [List.getLast?_cons_of_ne_nil nonempty, RuntimePhasePlan.sourceAddressInterval,
        List.getLast?_map, List.getLast?_range, ite_eq_right positive, Option.map_some] at member
      have equal := Option.mem_some_iff.mp member
      subst last
      simp only [endpoint, boundary]
  have scans : ∀ (records : List (RetiredCommitAttempt graph)) (cursor : Nat)
      (inherited : Finset Player) (generation : Nat) (start : Address),
      records ⊆ state.retired →
      ArchiveGenerationFrom plan inherited generation records →
      plan.sourceArchiveCursor (sourceControlRecords records) cursor inherited ≤
        state.attempt.phase →
      (∀ j : Fin records.length,
        plan.sourceArchiveCursor (sourceControlRecords (records.take j.val)) cursor inherited ≤
          records[j].attempt.phase) →
      start.1 = some cursor → start.2.2 = (generation, cursor) →
      List.IsChain R (start :: plan.sourceArchiveAddresses state.current.native.failureOwnersBefore
        state.generation state.attempt.phase (sourceControlRecords records) cursor inherited) := by
    intro records
    induction records with
    | nil =>
        intro cursor inherited generation start _ _ bounded _ startRank _
        apply intervalChain _ _ _ _ _ _ startRank
        intro r _ upper left right positioned mask query equal active
        have same := Option.some.inj (positioned.symm.trans equal)
        subst query
        exact Or.inl ⟨upper, fun failed => active (mask.symm ▸ Finset.mem_union_right _ failed)⟩
    | cons record records ih =>
        intro cursor inherited generation start subset generations bounded bounds startRank startNs
        have member : record ∈ state.retired := subset List.mem_cons_self
        have actual := phaseRetiredCompletion_history runtime leaks plan inputs horizon
          scheduler trace
        obtain ⟨phase, installed, low, kind, _, _, _⟩ := actual.archives record member
        have found := plan.find_low_eq_of_mem phase installed
        let ending := inherited ∪ record.state.failureOwners
        let retries := (phase.owners \ ending).Nonempty
        have retryEq : RetiredRetry plan ending record ↔ retries := by
          constructor
          · rintro ⟨other, otherMember, sameLow, _, surviving⟩
            have equal := plan.phase_eq_of_low_eq other phase otherMember installed
              (sameLow.trans low)
            simpa only [equal, retries] using surviving
          · exact fun surviving => ⟨phase, installed, low.symm, kind, surviving⟩
        have generationEq : record.attempt.generation = generation := generations.1
        let next := if retries then phase.low else phase.high
        let nextGeneration := record.attempt.generation + if retries then 1 else 0
        let closing : Address := (some next, ending, nextGeneration, next)
        have lower : cursor ≤ phase.low := by
          have firstBound := bounds ⟨0, by simp⟩
          simpa only [Fin.getElem_fin, List.take_zero, sourceControlRecords, List.map_nil,
            RuntimePhasePlan.sourceArchiveCursor, List.getElem_cons_zero, low] using firstBound
        have nextBound : plan.sourceArchiveCursor (sourceControlRecords records) next ending ≤
            state.attempt.phase := by
          simpa only [sourceControlRecords, List.map_cons, RuntimePhasePlan.sourceArchiveCursor,
            State.sourceFailureFootprint, found, Option.map_some, Option.getD_some,
            Option.any_some, kind, true_and, decide_eq_true_eq, low, ending, next,
            retries] using bounded
        have nextBounds : ∀ j : Fin records.length,
            plan.sourceArchiveCursor (sourceControlRecords (records.take j.val)) next ending ≤
              records[j].attempt.phase := by
          intro j
          have previous := bounds ⟨j.val + 1, by simp only [List.length_cons]; omega⟩
          simpa only [Fin.getElem_fin, List.take_succ_cons, sourceControlRecords, List.map_cons,
            RuntimePhasePlan.sourceArchiveCursor, State.sourceFailureFootprint, found,
            Option.map_some, Option.getD_some, Option.any_some, kind, true_and,
            decide_eq_true_eq, low, ending, next, retries,
            List.getElem_cons_succ] using previous
        have nextGenerations : ArchiveGenerationFrom plan ending nextGeneration records := by
          have tail := generations.2
          simpa only [← generationEq, retryEq, ending, nextGeneration] using tail
        have tail := ih next ending nextGeneration closing
          (fun item inside => subset (List.mem_cons_of_mem record inside))
          nextGenerations nextBound nextBounds rfl rfl
        let gap := plan.sourceAddressInterval record.state.failureOwnersBefore inherited
          record.attempt.generation cursor phase.low
        let middle := (plan.sourceAddressInterval record.state.failureOwnersBefore inherited
          record.attempt.generation phase.low phase.high).dropLast
        have gapChain : List.IsChain R (start :: gap) := by
          apply intervalChain _ _ _ _ _ _ startRank
          intro r _ upper left right positioned mask query equal active
          have same := Option.some.inj (positioned.symm.trans equal)
          subst query
          exact Or.inr (Or.inl ⟨record, member, low.symm ▸ upper,
            fun failed => active (mask.symm ▸ Finset.mem_union_right _ failed)⟩)
        have gapLast : ∀ last ∈ (start :: gap).getLast?,
            last.2.2 = (record.attempt.generation, record.attempt.phase) := by
          have boundary := plan.sourceSavedRank_of_commitment_interval phase installed kind
            phase.low le_rfl phase.nonempty
          simpa only [low] using intervalLast record.state.failureOwnersBefore inherited
            record.attempt.generation cursor phase.low start lower
            (by simpa only [generationEq] using startNs) boundary
        have middleNamespaces : ∀ address ∈ middle,
            address.2.2 = (record.attempt.generation, record.attempt.phase) := by
          intro address inside
          rw [show middle = _ from plan.sourceAddressInterval_commit_dropLast
            record.state.failureOwnersBefore inherited record.attempt.generation
              phase installed kind] at inside
          obtain ⟨i, _, rfl⟩ := List.mem_map.mp inside
          exact congrArg (record.attempt.generation, ·) low.symm
        have blockChain : ∀ address : Address,
            address.2.2 = (record.attempt.generation, record.attempt.phase) →
            List.IsChain R (address :: middle ++ [closing]) := by
          have build : ∀ (entries : List Address),
              (∀ address ∈ entries,
                address.2.2 = (record.attempt.generation, record.attempt.phase)) →
              ∀ address : Address,
                address.2.2 = (record.attempt.generation, record.attempt.phase) →
                List.IsChain R (address :: entries ++ [closing]) := by
            intro entries
            induction entries with
            | nil =>
                intro _ address matching
                exact List.isChain_pair.mpr (fun _ _ _ =>
                  Or.inr (Or.inr ⟨record, member, matching⟩))
            | cons item rest ih =>
                intro all address matching
                apply List.isChain_cons_cons.mpr
                exact ⟨fun _ _ _ => Or.inr (Or.inr ⟨record, member, matching⟩),
                  ih (fun other inside => all other (List.mem_cons_of_mem item inside))
                    item (all item List.mem_cons_self)⟩
          exact build middle middleNamespaces
        let entry : Address := (some phase.low, inherited,
          record.attempt.generation, record.attempt.phase)
        have closed : List.IsChain R ((start :: gap) ++ (middle ++ [closing])) :=
          gapChain.append (blockChain entry rfl).tail (fun left present right head =>
            (blockChain left (gapLast left present)).rel_head? head)
        have combined := (show List.IsChain R (((start :: gap) ++ middle) ++ [closing]) by
          simpa only [List.append_assoc] using closed).append_overlap tail (by simp)
        simpa only [sourceControlRecords, List.map_cons, RuntimePhasePlan.sourceArchiveAddresses,
          State.sourceFailureFootprint, found, Option.map_some, Option.getD_some, Option.any_some,
          kind, true_and, decide_eq_true_eq, low, gap, middle, closing, ending, next,
          nextGeneration, retries,
          List.cons_append, List.singleton_append, List.append_assoc] using combined
  have bounds := sourceArchivePrefix_history runtime leaks plan inputs horizon scheduler trace
  have generations := phaseArchiveGeneration_history runtime leaks plan inputs horizon scheduler
    trace
  have chain := scans state.retired 0 ∅ 0 (some 0, ∅, 0, 0)
    (List.Subset.refl _) generations.1 bounds.1 bounds.2 rfl rfl
  have allChain : List.IsChain R (state.sourcePublicAddressWord plan state.attempt.phase) := by
    simpa only [sourcePublicAddressWord_saved, List.singleton_append] using chain
  obtain ⟨firstBound, firstValue⟩ := List.getElem?_eq_some_iff.mp first
  obtain ⟨indexBound, secondValue⟩ := List.getElem?_eq_some_iff.mp second
  have edge := allChain.getElem index indexBound
  rw [firstValue, secondValue] at edge
  have provided := edge event.val rank active
  have completedCurrent : ∀ r : graph.EventId, r.val < state.attempt.phase →
      r ∈ state.current.native.config.cut.completed := by
    have frontier := (phaseApplication_frontier runtime leaks).history _ horizon scheduler
      (fun current supported => by
        obtain ⟨input, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
        exact initial_frontier plan input) trace
    intro r below
    cases phases : state.phases with
    | nil => exact (frontier.terminal phases).symm ▸ Finset.mem_univ r
    | cons phase rest =>
        have positioned := frontier.positioned
        rw [phases] at positioned
        have lower : r.val < phase.low := by
          simpa only [PhaseRuntimeState.attempt, phases, List.head?_cons,
            Option.map_some, Option.getD_some] using below
        exact positioned.2.1 r lower
  have accepted (provider : State graph)
      (unflagged : owner ∉ provider.failureOwnersBefore (event.val + 1))
      (completed : event ∈ provider.config.cut.completed) :
      ∃ handle, provider.accepted (.inr event) = some handle := by
    cases present : provider.accepted (.inr event) with
    | some handle => exact ⟨handle, rfl⟩
    | none =>
        have failed := (provider.publicFailure_iff_accepted_none event owner payload
          binding completed).mpr present
        exact (unflagged (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ⟨event, Nat.lt_succ_self _, graph.actor?_of_outputLayout_binding binding, failed⟩⟩)).elim
  rcases provided with final | archived | forbidden
  · exact ⟨state.current.native, Or.inl ⟨rfl, final.1⟩, final.2,
      completedCurrent event final.1, accepted _ final.2 (completedCurrent event final.1)⟩
  · obtain ⟨record, member, below, unflagged⟩ := archived
    obtain ⟨phase, low, _, finished⟩ :=
      phaseRetiredBindingInterval_history runtime leaks plan inputs horizon scheduler trace
        record member
    have completed := (finished.2 event).mpr (below.trans_le (low.symm ▸ phase.nonempty.le))
    obtain ⟨j, bounded, equal⟩ := List.mem_iff_getElem.mp member
    refine ⟨record.state, Or.inr ⟨⟨j, bounded⟩, ?_, ?_⟩, unflagged,
      completed, accepted _ unflagged completed⟩
    · exact congrArg RetiredCommitAttempt.state equal.symm
    · change event.val < state.retired[j].attempt.phase
      rw [equal]
      exact below
  · obtain ⟨record, member, same⟩ := forbidden
    exact (unarchived record member same).elim

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

/-- The source rank difference is exactly the number of retained public
instructions, independently of their disclosure bits and sampled values. -/
theorem NativePublicSourceStep.path_length
    {graph : Vegas.EventGraph Player L} {Γ : SourceCtx Player L} {O : Finset VarId}
    {native : EventGraphRuntime.State graph} {offset : Nat}
    {program : SourceProgram Player L Γ O}
    (first last : ProtocolState program × Finset Player)
    (states : List (ProtocolState program × Finset Player))
    (chain : (first :: states).IsChain (NativePublicSourceStep native offset program))
    (ending : (first :: states).getLast (List.cons_ne_nil _ _) = last) :
    instructionCount program - ProtocolState.remaining program last.1 =
      instructionCount program - ProtocolState.remaining program first.1 + states.length := by
  induction states generalizing first with
  | nil =>
      have same : first = last := ending
      subst last
      rfl
  | cons middle states ih =>
      have moved := List.isChain_cons_cons.mp chain
      have rest := ih middle moved.2 (by simpa only [List.getLast_cons_cons] using ending)
      have nextRank := moved.1.position
      simp only [List.length_cons]
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
  have update := step.2.1 event ranked
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
