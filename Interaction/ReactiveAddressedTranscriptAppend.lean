/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAddressedQueryTranscript

/-! # Appending an actual scheduler query to its coordinate transcript -/

noncomputable section

namespace Interaction.ReactiveApplication.AddressedScheduler

variable {Principal Address LocalSeed RestSeed Query : Type} [DecidableEq Address]
  {app : ReactiveApplication Principal}

/-- Reconstructing a transcript after an additional command retains its complete
previous query prefix and reads the new request at the complete actual recall. -/
theorem coordinateTranscriptFrom_append
    (controller : AddressedScheduler app Address LocalSeed RestSeed Query)
    (rest : RestSeed) (address : Address) (earlier first later : List app.EnvironmentEntry) :
    controller.coordinateTranscriptFrom rest address earlier (first ++ later) =
      controller.coordinateTranscriptFrom rest address earlier first ++
        controller.coordinateTranscriptFrom rest address (earlier ++ first) later := by
  induction first generalizing earlier with
  | nil => simp only [List.nil_append, coordinateTranscriptFrom, List.append_nil]
  | cons entry first ih =>
      simp only [List.cons_append, coordinateTranscriptFrom]
      rw [ih]
      have append : earlier ++ entry :: first = (earlier ++ [entry]) ++ first := by
        simp only [List.append_assoc, List.singleton_append]
      rw [append]
      cases controller.request rest earlier entry.beforeView with
      | none => rfl
      | some selected =>
          rcases selected with ⟨selected, query⟩
          dsimp only
          split <;> rfl

end Interaction.ReactiveApplication.AddressedScheduler
