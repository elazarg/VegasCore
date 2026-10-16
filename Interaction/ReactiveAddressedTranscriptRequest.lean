/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAddressedQueryTranscript

/-! # Reconstructed coordinate transcripts depend only on scheduler requests -/

namespace Interaction.ReactiveApplication.AddressedScheduler

variable {Principal Address FirstSeed SecondSeed RestSeed Query : Type}
  [DecidableEq Address] {app : ReactiveApplication Principal}

/-- Changing the private reply carrier preserves the reconstructed query and
command transcript when requests are identical; no seed laws are identified. -/
theorem coordinateTranscriptFrom_eq_of_request_eq
    (first : AddressedScheduler app Address FirstSeed RestSeed Query)
    (second : AddressedScheduler app Address SecondSeed RestSeed Query)
    (same : first.request = second.request) (rest : RestSeed) (address : Address)
    (earlier past : List app.EnvironmentEntry) :
    first.coordinateTranscriptFrom rest address earlier past =
      second.coordinateTranscriptFrom rest address earlier past := by
  induction past generalizing earlier with
  | nil => rfl
  | cons entry later ih =>
      simp only [coordinateTranscriptFrom]
      rw [same, ih]

end Interaction.ReactiveApplication.AddressedScheduler
