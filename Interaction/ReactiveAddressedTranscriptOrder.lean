/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAddressedTranscriptEntries

/-! # Chronological pairwise properties of original addressed transcripts -/

noncomputable section

namespace Interaction.ReactiveApplication.AddressedScheduler

variable {Principal Address LocalSeed RestSeed Query : Type} [DecidableEq Address]
  {app : ReactiveApplication Principal}

/-- A relation proved at every ordered pair of genuine queried occurrences
holds pairwise on the extracted transcript, including repeated equal entries. -/
theorem coordinateTranscriptFrom_pairwise
    (controller : AddressedScheduler app Address LocalSeed RestSeed Query)
    (rest : RestSeed) (address : Address) (earlier past : List app.EnvironmentEntry)
    (relation : (Query × app.Command) → (Query × app.Command) → Prop)
    (chronological : ∀ before first between second after firstQuery secondQuery,
      past = (before ++ [first] ++ between) ++ second :: after →
      controller.request rest (earlier ++ before) first.beforeView = some (address, firstQuery) →
      controller.request rest (earlier ++ before ++ [first] ++ between) second.beforeView =
        some (address, secondQuery) → relation (firstQuery, first.command)
          (secondQuery, second.command)) :
    (controller.coordinateTranscriptFrom rest address earlier past).Pairwise relation := by
  induction past generalizing earlier with
  | nil => exact .nil
  | cons head tail ih =>
      have tailOrdered : (controller.coordinateTranscriptFrom rest address
          (earlier ++ [head]) tail).Pairwise relation := by
        apply ih
        intro before first between second after firstQuery secondQuery recorded firstAt secondAt
        apply chronological (head :: before) first between second after firstQuery secondQuery
        · rw [recorded]
          simp only [List.cons_append, List.append_assoc]
        · simpa only [List.append_assoc, List.singleton_append] using firstAt
        · simpa only [List.append_assoc, List.singleton_append] using secondAt
      simp only [coordinateTranscriptFrom]
      cases requested : controller.request rest earlier head.beforeView with
      | none => exact tailOrdered
      | some pair =>
          rcases pair with ⟨selected, query⟩
          by_cases same : selected = address
          · subst selected
            simp only [ite_true]
            apply List.pairwise_cons.mpr
            refine ⟨?_, tailOrdered⟩
            intro item member
            obtain ⟨before, entry, after, recorded, queried, command⟩ :=
              (controller.coordinateTranscriptFrom_mem_iff rest address (earlier ++ [head])
                tail item).mp member
            have related := chronological [] head before entry after query item.1
              (by simpa only [List.nil_append, List.singleton_append, List.cons_append] using
                congrArg (head :: ·) recorded)
              (by simpa only [List.append_nil] using requested)
              (by simpa only [List.append_nil, List.append_assoc] using queried)
            simpa only [command] using related
          · simpa only [ite_eq_right same] using tailOrdered

end Interaction.ReactiveApplication.AddressedScheduler
