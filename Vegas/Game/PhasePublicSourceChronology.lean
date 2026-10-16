/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSavedExclusionReadback
import Vegas.Pending.PhaseArchiveGeneration

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
