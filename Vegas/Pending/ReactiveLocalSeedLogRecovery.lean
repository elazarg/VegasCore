/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedCountedLog
import Vegas.Pending.ReactiveLocalSeedLogEncoding

/-! # Uniqueness of counted unsent-event raw logs

A genuine counted log with no emitted event packet and no resolution is
recovered exactly from its positive queries and exhausted-clock count.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

local notation "app" => runtime.reactiveApplication leaks
local notation "encodeLog" => encodeUnsentLogFrom (runtime := runtime) (leaks := leaks)

theorem encodeUnsentLogFrom_append (left right : List Bool) (elapsed activationIndex : Nat) :
    encodeLog elapsed activationIndex (left ++ right) =
      encodeLog elapsed activationIndex left ++
        encodeLog (elapsed + (exhaustedClocks (encodeLog elapsed activationIndex left)).length)
          (activationIndex + (positiveQueries (encodeLog elapsed activationIndex left)).length)
          right := by
  induction left generalizing elapsed activationIndex with
  | nil => simp [encodeUnsentLogFrom, positiveQueries, exhaustedClocks]
  | cons answer rest ih =>
      cases answer <;>
        simp [encodeUnsentLogFrom, positiveQueries, exhaustedClocks, ih,
          Nat.add_assoc, Nat.add_comm]

private theorem entry_eq_of_unsent (entry : LocalSeedEntry graph (app).Command)
    (empty : entry.query.input.emitted = []) :
    entry = ⟨⟨⟨entry.query.input.elapsed, []⟩, entry.query.activationIndex⟩, entry.reply⟩ := by
  cases entry with
  | mk query reply =>
      cases query with
      | mk input index =>
          cases input with
          | mk elapsed emitted =>
              simp only at empty
              subst emitted
              rfl

/-- Every counted unsent unresolved log is the concrete encoding of its
activation/exhaustion word. No information about a private seed is assumed. -/
theorem CountedQueryLog.encode_unsent {log : List (LocalSeedEntry graph (app).Command)}
    (counted : CountedQueryLog log)
    (unsent : ∀ entry ∈ log, entry.query.input.emitted = [])
    (unresolved : ∀ entry ∈ log, entry.reply = .activation ∨ entry.reply = .exhausted) :
    ∃ word : List Bool, log = encodeLog 0 0 word := by
  revert unsent unresolved
  induction counted with
  | empty => intro _ _; exact ⟨[], rfl⟩
  | @append past recorded entry clock index ih =>
      intro unsent unresolved
      have oldUnsent : ∀ earlier ∈ past, earlier.query.input.emitted = [] :=
        fun earlier member => unsent earlier (List.mem_append_left _ member)
      have oldUnresolved : ∀ earlier ∈ past,
          earlier.reply = .activation ∨ earlier.reply = .exhausted :=
        fun earlier member => unresolved earlier (List.mem_append_left _ member)
      obtain ⟨word, wordEq⟩ := ih oldUnsent oldUnresolved
      have last : entry ∈ past ++ [entry] := List.mem_append_right _ (by simp)
      have empty := unsent entry last
      rcases unresolved entry last with activation | exhausted
      · have form : entry =
            ⟨⟨⟨(exhaustedClocks past).length, []⟩, (positiveQueries past).length⟩,
              .activation⟩ := by
          rw [entry_eq_of_unsent entry empty, clock, index, activation]
        refine ⟨word ++ [true], ?_⟩
        rw [encodeUnsentLogFrom_append, ← wordEq]
        simp only [Nat.zero_add, encodeUnsentLogFrom]
        rw [← form]
      · have form : entry =
            ⟨⟨⟨(exhaustedClocks past).length, []⟩, (positiveQueries past).length⟩,
              .exhausted⟩ := by
          rw [entry_eq_of_unsent entry empty, clock, index, exhausted]
        refine ⟨word ++ [false], ?_⟩
        rw [encodeUnsentLogFrom_append, ← wordEq]
        simp only [Nat.zero_add, encodeUnsentLogFrom]
        rw [← form]

/-- Two actual counted unsent unresolved logs with identical observable
positive queries and closed-clock count are exactly the same raw query log. -/
theorem CountedQueryLog.eq_of_unsent_signature
    {first second : List (LocalSeedEntry graph (app).Command)}
    (left : CountedQueryLog first) (right : CountedQueryLog second)
    (leftUnsent : ∀ entry ∈ first, entry.query.input.emitted = [])
    (rightUnsent : ∀ entry ∈ second, entry.query.input.emitted = [])
    (leftUnresolved : ∀ entry ∈ first, entry.reply = .activation ∨ entry.reply = .exhausted)
    (rightUnresolved : ∀ entry ∈ second, entry.reply = .activation ∨ entry.reply = .exhausted)
    (positiveEq : positiveQueries first = positiveQueries second)
    (closedEq : (exhaustedClocks first).length = (exhaustedClocks second).length) :
    first = second := by
  obtain ⟨firstWord, rfl⟩ := left.encode_unsent leftUnsent leftUnresolved
  obtain ⟨secondWord, rfl⟩ := right.encode_unsent rightUnsent rightUnresolved
  have same := encodeUnsentLogFrom_signature_injective firstWord secondWord 0 0 positiveEq closedEq
  rw [same]

end Vegas.EventGraphRuntime.LocalSeedController
