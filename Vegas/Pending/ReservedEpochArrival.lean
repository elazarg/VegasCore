/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochTape

/-! # First shared processing epochs are monotone in the send boundary -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch.Tape

variable {Player : Type} {length : Nat}

open Classical in
def nextProcessingEpoch (tape : Tape Player length) (start : Nat) : Option Nat :=
  if available : ∃ cycle, start ≤ cycle ∧ tape.processes cycle = true then
    some (Nat.find available)
  else none

theorem nextProcessingEpoch_spec (tape : Tape Player length) (start cycle : Nat)
    (selected : tape.nextProcessingEpoch start = some cycle) :
    start ≤ cycle ∧ tape.processes cycle = true ∧
      ∀ later, start ≤ later → tape.processes later = true → cycle ≤ later := by
  classical
  unfold nextProcessingEpoch at selected
  split at selected
  · rename_i available
    cases Option.some.inj selected
    exact ⟨(Nat.find_spec available).1, (Nat.find_spec available).2,
      fun _ lower epoch => Nat.find_min' available ⟨lower, epoch⟩⟩
  · cases selected

theorem nextProcessingEpoch_mono (tape : Tape Player length) (first later left right : Nat)
    (ordered : first ≤ later) (early : tape.nextProcessingEpoch first = some left)
    (late : tape.nextProcessingEpoch later = some right) : left ≤ right := by
  have leftSpec := tape.nextProcessingEpoch_spec first left early
  have rightSpec := tape.nextProcessingEpoch_spec later right late
  exact leftSpec.2.2 right (ordered.trans rightSpec.1) rightSpec.2.1

theorem nextProcessingEpoch_bounded (tape : Tape Player length)
    (cycles activationGap processingGap start : Nat)
    (gaps : tape.BoundedGaps cycles activationGap processingGap) (running : start < cycles) :
    ∃ cycle, tape.nextProcessingEpoch start = some cycle ∧ start ≤ cycle ∧
      cycle < start + processingGap ∧ tape.processes cycle = true := by
  classical
  obtain ⟨later, lower, upper, epoch⟩ := gaps.processing start running
  have available : ∃ cycle, start ≤ cycle ∧ tape.processes cycle = true := ⟨later, lower, epoch⟩
  have selected : tape.nextProcessingEpoch start = some (Nat.find available) := by
    simp only [nextProcessingEpoch, available, ↓reduceDIte]
  have spec := tape.nextProcessingEpoch_spec start (Nat.find available) selected
  exact ⟨Nat.find available, selected, spec.1,
    (spec.2.2 later lower epoch).trans_lt upper, spec.2.1⟩

end Vegas.EventGraphRuntime.ReservedEpoch.Tape
