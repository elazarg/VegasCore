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
