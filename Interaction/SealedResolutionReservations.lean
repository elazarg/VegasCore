/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionPeriodicService

/-! # Periodic reserved inclusion schedules

The final service phase of each positive-length period is reserved in full.
Outside those phases an arbitrary adaptive wire policy is retained unchanged.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]

/-- Reserve environment calls belonging to the final round of each period. -/
def periodicFinalReservation (serviceSlots period turn : Nat) : Bool :=
  decide ((turn / (serviceSlots + 1) + 1) % period = 0)

/-- Every service call in a block-final round is reserved. -/
theorem periodicFinalReservation_range_count (serviceSlots period block : Nat)
    (hperiod : 0 < period) :
    (List.range' (((block + 1) * period - 1) * (serviceSlots + 1)) serviceSlots).countP
      (periodicFinalReservation serviceSlots period) = serviceSlots := by
  calc
    _ = (List.range' (((block + 1) * period - 1) * (serviceSlots + 1))
        serviceSlots).length := List.countP_eq_length.mpr (by
      intro turn hturn
      obtain ⟨hlower, hupper⟩ := List.mem_range'_1.mp hturn
      obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hlower
      have hoffset : offset < serviceSlots := by omega
      have hslotPositive : 0 < serviceSlots + 1 := by omega
      have hoffsetSmall : offset < serviceSlots + 1 := by omega
      have hperiodProduct : 0 < (block + 1) * period :=
        Nat.mul_pos (by omega) hperiod
      have hquotient :
          ((((block + 1) * period - 1) * (serviceSlots + 1) + offset) /
            (serviceSlots + 1)) = (block + 1) * period - 1 := by
        rw [Nat.mul_comm ((block + 1) * period - 1) (serviceSlots + 1)]
        rw [Nat.mul_add_div hslotPositive, Nat.div_eq_of_lt hoffsetSmall, Nat.add_zero]
      simp only [periodicFinalReservation, hquotient, decide_eq_true_eq]
      have hsub : (block + 1) * period - 1 + 1 = (block + 1) * period := by omega
      rw [hsub]
      simp)
    _ = serviceSlots := by simp

omit [DecidableEq Principal] in
/-- Periodic reservation has enough final-round capacity whenever one round
can cover all roster submissions. -/
theorem periodicFinalReservation_capacity (principals : List Principal)
    (serviceSlots period block : Nat) (hperiod : 0 < period)
    (hcapacity : period * principals.length ≤ serviceSlots) :
    period * principals.length ≤
      (List.range' (((block + 1) * period - 1) * (serviceSlots + 1)) serviceSlots).countP
        (periodicFinalReservation serviceSlots period) := by
  rw [periodicFinalReservation_range_count serviceSlots period block hperiod]
  exact hcapacity

/-- The periodic mask admits a servicing environment for every adaptive wire
policy; unreserved calls continue to use that policy with its real history and
view. -/
theorem exists_periodicFinalReservation_service
    (app : MessageApplication Principal) (serviceSlots period : Nat)
    (wire : app.WirePolicy) :
    ∃ reservedWire : app.WirePolicy,
      app.InclusionService
        (fun turn => periodicFinalReservation serviceSlots period turn = true)
        (app.wireEnvironment reservedWire) :=
  ⟨app.reserveInclusion (periodicFinalReservation serviceSlots period) wire,
    app.reserveInclusion_service _ wire⟩

end Interaction.SealedResolution
