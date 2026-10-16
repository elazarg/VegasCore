/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAddressedTranscriptAppend

/-! # Original history occurrences of addressed query transcript entries -/

noncomputable section

namespace Interaction.ReactiveApplication.AddressedScheduler

variable {Principal Address LocalSeed RestSeed Query : Type} [DecidableEq Address]
  {app : ReactiveApplication Principal}

/-- Every queried pair has a genuine original history occurrence, with its
complete earlier recall retained in the request. -/
theorem coordinateTranscriptFrom_mem_iff
    (controller : AddressedScheduler app Address LocalSeed RestSeed Query)
    (rest : RestSeed) (address : Address) (earlier past : List app.EnvironmentEntry)
    (item : Query × app.Command) :
    item ∈ controller.coordinateTranscriptFrom rest address earlier past ↔
      ∃ before entry after, past = before ++ entry :: after ∧
        controller.request rest (earlier ++ before) entry.beforeView = some (address, item.1) ∧
        entry.command = item.2 := by
  induction past generalizing earlier with
  | nil => simp [coordinateTranscriptFrom]
  | cons first later ih =>
      constructor
      · intro member
        have recover (tail : item ∈ controller.coordinateTranscriptFrom rest address
            (earlier ++ [first]) later) :
            ∃ before entry after, first :: later = before ++ entry :: after ∧
              controller.request rest (earlier ++ before) entry.beforeView =
                some (address, item.1) ∧ entry.command = item.2 := by
          obtain ⟨before, entry, after, recorded, requested, command⟩ :=
            (ih (earlier ++ [first])).mp tail
          refine ⟨first :: before, entry, after, by rw [recorded]; rfl, ?_, command⟩
          simpa only [List.append_assoc, List.singleton_append] using requested
        simp only [coordinateTranscriptFrom] at member
        cases requested : controller.request rest earlier first.beforeView with
        | none => rw [requested] at member; exact recover member
        | some pair =>
            rcases pair with ⟨selected, query⟩
            rw [requested] at member
            dsimp only at member
            by_cases same : selected = address
            · rw [ite_eq_left same] at member
              rcases List.mem_cons.mp member with head | tail
              · refine ⟨[], first, later, rfl, ?_, ?_⟩
                · simpa only [List.append_nil, ← same, head] using requested
                · exact congrArg Prod.snd head.symm
              · exact recover tail
            · rw [ite_eq_right same] at member
              exact recover member
      · rintro ⟨before, entry, after, recorded, requested, command⟩
        rw [recorded, coordinateTranscriptFrom_append]
        apply List.mem_append_right
        simp only [coordinateTranscriptFrom, requested, ite_true]
        apply List.mem_cons.mpr
        exact Or.inl (Prod.ext rfl command.symm)

end Interaction.ReactiveApplication.AddressedScheduler
