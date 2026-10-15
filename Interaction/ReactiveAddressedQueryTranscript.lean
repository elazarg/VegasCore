/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAddressedPosterior

/-! # Actual coordinate query transcripts characterize every candidate seed -/

noncomputable section

namespace Interaction.ReactiveApplication.AddressedScheduler

open GameTheory.Math.Probability

variable {Principal Address LocalSeed RestSeed Query : Type} [DecidableEq Address]
  {app : ReactiveApplication Principal}

/-- Extract precisely the selected coordinate's actual erased queries and
replies. The selector depends on the residual seed and public history only. -/
def coordinateTranscriptFrom (controller : AddressedScheduler app Address LocalSeed RestSeed Query)
    (rest : RestSeed) (address : Address) (earlier : List app.EnvironmentEntry) :
    List app.EnvironmentEntry → List (Query × app.Command)
  | [] => []
  | entry :: later =>
      let tail := coordinateTranscriptFrom controller rest address (earlier ++ [entry]) later
      match controller.request rest earlier entry.beforeView with
      | none => tail
      | some (selected, query) =>
          if selected = address then (query, entry.command) :: tail else tail

/-- This equivalence is simultaneous for ALL candidate local seeds. It is not
restricted to an original seed already known to follow the observed run. -/
theorem coordinateConsistentFrom_iff_transcript
    (controller : AddressedScheduler app Address LocalSeed RestSeed Query)
    (rest : RestSeed) (address : Address) (seed : LocalSeed)
    (earlier past : List app.EnvironmentEntry) :
    controller.coordinateConsistentFrom rest address seed earlier past ↔
      ∀ entry ∈ controller.coordinateTranscriptFrom rest address earlier past,
        controller.reply address seed entry.1 = entry.2 := by
  induction past generalizing earlier with
  | nil => simp [coordinateConsistentFrom, coordinateTranscriptFrom]
  | cons entry later ih =>
      cases requested : controller.request rest earlier entry.beforeView with
      | none => simp [coordinateConsistentFrom, coordinateTranscriptFrom, requested, ih]
      | some pair =>
          obtain ⟨selected, query⟩ := pair
          by_cases same : selected = address
          · subst selected
            simp [coordinateConsistentFrom, coordinateTranscriptFrom, requested, ih]
          · simp [coordinateConsistentFrom, coordinateTranscriptFrom, requested, same, ih]

/-- Query-order commutation reduces to an ordinary permutation of the actual
coordinate transcript, using existing conjunction semantics. -/
theorem coordinateConsistentFrom_iff_of_transcript_perm
    (controller : AddressedScheduler app Address LocalSeed RestSeed Query)
    (firstRest secondRest : RestSeed) (address : Address) (seed : LocalSeed)
    (firstEarlier firstPast secondEarlier secondPast : List app.EnvironmentEntry)
    (same : (controller.coordinateTranscriptFrom firstRest address firstEarlier firstPast).Perm
      (controller.coordinateTranscriptFrom secondRest address secondEarlier secondPast)) :
    controller.coordinateConsistentFrom firstRest address seed firstEarlier firstPast ↔
      controller.coordinateConsistentFrom secondRest address seed secondEarlier secondPast := by
  rw [coordinateConsistentFrom_iff_transcript, coordinateConsistentFrom_iff_transcript]
  constructor
  · intro valid entry member
    exact valid entry (same.mem_iff.mpr member)
  · intro valid entry member
    exact valid entry (same.mem_iff.mp member)

/-- The actual planner's existing command rectangle can be read as per-event
query constraints, retaining the unrestricted history-adaptive residual. -/
theorem command_rectangle_transcript
    (controller : AddressedScheduler app Address LocalSeed RestSeed Query)
    (rest : RestSeed) (values : Address → LocalSeed)
    (earlier past : List app.EnvironmentEntry) :
    app.commandConsistentFrom controller.choose (rest, values) earlier past ↔
      controller.remainderConsistentFrom rest earlier past ∧
        ∀ address, ∀ entry ∈ controller.coordinateTranscriptFrom rest address earlier past,
          controller.reply address (values address) entry.1 = entry.2 := by
  simp only [controller.command_rectangle, coordinateConsistentFrom_iff_transcript]

end Interaction.ReactiveApplication.AddressedScheduler
