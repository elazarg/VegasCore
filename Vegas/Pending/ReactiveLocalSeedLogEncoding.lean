/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedPositiveLog
import Vegas.Pending.ReactiveLocalSeedExhaustion

/-! # Recovering unsent-event query logs from their positive queries

For an unsent event a raw query records two counters: previous exhausted
clocks and previous activations. Positive queries and the final exhaustion
count determine the complete activation/exhaustion word.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

local notation "app" => runtime.reactiveApplication leaks

/-- Encode an unsent activation/exhaustion word at its actual two local counters. -/
def encodeUnsentLogFrom (elapsed activationIndex : Nat) :
    List Bool → List (LocalSeedEntry graph (app).Command)
  | [] => []
  | true :: rest => ⟨⟨⟨elapsed, []⟩, activationIndex⟩, .activation⟩ ::
      encodeUnsentLogFrom elapsed (activationIndex + 1) rest
  | false :: rest => ⟨⟨⟨elapsed, []⟩, activationIndex⟩, .exhausted⟩ ::
      encodeUnsentLogFrom (elapsed + 1) activationIndex rest

local notation "encodeLog" => encodeUnsentLogFrom (runtime := runtime) (leaks := leaks)

private theorem encode_positive_elapsed (word : List Bool) (elapsed activationIndex : Nat)
    (query : CurrentSeedQuery graph)
    (member : query ∈ positiveQueries (encodeLog elapsed activationIndex word)) :
    elapsed ≤ query.input.elapsed := by
  induction word generalizing elapsed activationIndex with
  | nil => simp [encodeUnsentLogFrom, positiveQueries] at member
  | cons answer rest ih =>
      cases answer with
      | false =>
          have later := ih (elapsed + 1) activationIndex member
          omega
      | true =>
          simp only [encodeUnsentLogFrom, positiveQueries, List.filterMap_cons, List.mem_cons]
            at member
          rcases member with same | later
          · cases same
            exact Nat.le_refl _
          · exact ih elapsed (activationIndex + 1) later

/-- Positive clocks and the final exhausted-clock count determine the
complete raw word; repeated activations at one clock remain distinguishable. -/
theorem encodeUnsentLogFrom_signature_injective (first second : List Bool)
    (elapsed activationIndex : Nat)
    (positiveEq : (positiveQueries (encodeLog elapsed activationIndex first)).map
        (fun query => query.input.elapsed) =
      (positiveQueries (encodeLog elapsed activationIndex second)).map
        (fun query => query.input.elapsed))
    (exhaustedEq : (exhaustedClocks (encodeLog elapsed activationIndex first)).length =
      (exhaustedClocks (encodeLog elapsed activationIndex second)).length) : first = second := by
  induction first generalizing second elapsed activationIndex with
  | nil =>
      cases second with
      | nil => rfl
      | cons answer rest =>
          cases answer with
          | false =>
              simp only [encodeUnsentLogFrom, exhaustedClocks, List.filterMap_nil,
                List.filterMap_cons, List.length_cons, List.length_nil] at exhaustedEq
              omega
          | true => simp [encodeUnsentLogFrom, positiveQueries] at positiveEq
  | cons answer rest ih =>
      cases second with
      | nil =>
          cases answer with
          | false =>
              simp only [encodeUnsentLogFrom, exhaustedClocks, List.filterMap_nil,
                List.filterMap_cons, List.length_cons, List.length_nil] at exhaustedEq
              omega
          | true => simp [encodeUnsentLogFrom, positiveQueries] at positiveEq
      | cons other tail =>
          cases answer <;> cases other
          · have positives : (positiveQueries (encodeLog (elapsed + 1) activationIndex rest)).map
                  (fun query => query.input.elapsed) =
                (positiveQueries (encodeLog (elapsed + 1) activationIndex tail)).map
                  (fun query => query.input.elapsed) := positiveEq
            have exhausts : (exhaustedClocks
                (encodeLog (elapsed + 1) activationIndex rest)).length =
                (exhaustedClocks (encodeLog (elapsed + 1) activationIndex tail)).length := by
              simpa only [encodeUnsentLogFrom, exhaustedClocks, List.filterMap_cons,
                List.length_cons, Nat.succ.injEq] using exhaustedEq
            exact congrArg (false :: ·) (ih tail _ _ positives exhausts)
          · have memberClock : elapsed ∈
                (positiveQueries (encodeLog (elapsed + 1) activationIndex rest)).map
                  (fun query => query.input.elapsed) := by
              change (positiveQueries (encodeLog (elapsed + 1) activationIndex rest)).map
                  (fun query => query.input.elapsed) = elapsed ::
                (positiveQueries (encodeLog elapsed (activationIndex + 1) tail)).map
                  (fun query => query.input.elapsed) at positiveEq
              rw [positiveEq]
              exact List.mem_cons_self
            obtain ⟨query, member, clock⟩ := List.mem_map.mp memberClock
            have later := encode_positive_elapsed rest (elapsed + 1) activationIndex _ member
            rw [clock] at later
            omega
          · have memberClock : elapsed ∈
                (positiveQueries (encodeLog (elapsed + 1) activationIndex tail)).map
                  (fun query => query.input.elapsed) := by
              change elapsed :: (positiveQueries (encodeLog elapsed (activationIndex + 1) rest)).map
                  (fun query => query.input.elapsed) =
                (positiveQueries (encodeLog (elapsed + 1) activationIndex tail)).map
                  (fun query => query.input.elapsed) at positiveEq
              rw [← positiveEq]
              exact List.mem_cons_self
            obtain ⟨query, member, clock⟩ := List.mem_map.mp memberClock
            have later := encode_positive_elapsed tail (elapsed + 1) activationIndex _ member
            rw [clock] at later
            omega
          · have positives : (positiveQueries (encodeLog elapsed (activationIndex + 1) rest)).map
                  (fun query => query.input.elapsed) =
                (positiveQueries (encodeLog elapsed (activationIndex + 1) tail)).map
                  (fun query => query.input.elapsed) := by
              exact (List.cons.inj positiveEq).2
            have exhausts :
                (exhaustedClocks (encodeLog elapsed (activationIndex + 1) rest)).length =
                (exhaustedClocks (encodeLog elapsed (activationIndex + 1) tail)).length :=
              exhaustedEq
            exact congrArg (true :: ·) (ih tail _ _ positives exhausts)

end Vegas.EventGraphRuntime.LocalSeedController
