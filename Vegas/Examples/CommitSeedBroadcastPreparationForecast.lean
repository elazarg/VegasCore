/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastGoodReceiptForecast
import Vegas.Examples.CommitSeedBroadcastTailRecall
import Vegas.Examples.CommitSeedBroadcastHelperPublicPackets
import Vegas.Examples.CommitSeedBroadcastRegularBelief

/-! # Foreign original records before a good clock-two preparation choice -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

open Classical in
/-- The original seed and retained pre-response records determine the foreign
receipt forecast used by the two preparation experiments. -/
def originalReceiptForecast (seed : Seeds) (execution : app.Execution) (owner : Player) : Prop :=
  if seed.2 owner then
    (execution.recall owner).length = 1 ∨ ∃ entry ∈ execution.recall owner,
      entry.action.transmission ≠ none
  else initialPublicPackets execution ≠ ∅

open Classical in
/-- The potential strict improvement at a good seed with no foreign original
miss. Its connection to actual future receipts is established by native forecasts. -/
def preparationAdvantageMark (seed : Seeds) (state : app.ProtocolState) (owner : Player) : ℝ :=
  match state with
  | none => 0
  | some current => if seed.2 owner = true ∧
      ∀ other, other ≠ owner → originalReceiptForecast seed current.execution other then
        3 / 2 else 0

def preparationAdvantageValue (state : app.ProtocolState) (owner : Player) : ℝ :=
  expect (originalSeedPosterior state) (fun seed => preparationAdvantageMark seed state owner)

/-- At a good first-late callback, a bad owner has not yet received its own
first-late callback. Its full recall is the actual initial response alone. -/
theorem bad_owner_initial_record_at_good_clock_two
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (focal : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some focal, execution⟩))
    (request : execution.application.SeedRequest focal (originalCoordinate focal))
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = [])
    (good : seed.2 focal = true) (owner : Player) (bad : seed.2 owner = false) :
    ∃ first : app.PlayerEntry, execution.recall owner = [first] ∧
      PhaseRuntimeState.requests first.beforeView.application.2 owner
        (originalCoordinate owner) ∧ first.beforeView.application.2.native.clock = 0 := by
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have upper : execution.environmentRecall.length ≤ 8 := by
    rcases original_first_late_input_placement seed ⟨remaining, some focal, execution⟩ raw focal rfl
        request.1.symm clock with early | late
    · exact early.2.1
    · rw [good] at late
      cases late.2.2
  obtain ⟨first, _view, initialRequest, zero, word⟩ := original_first_late_foreign_records seed
    remaining execution focal (countedInRaw.trace initial horizon (family seed) trace)
      request.1.symm clock empty owner
  rcases word with singleton | ⟨second, word, _secondView, secondRequest, secondClock⟩
  · exact ⟨first, singleton, initialRequest, zero⟩
  · obtain ⟨before, prior, kept, active, _past, viewed, _offered⟩ :=
      countedMenu.recorded_response_at initial horizon (family seed)
        ⟨remaining, some focal, execution⟩ trace owner [first] second [] word
    have beforeOriginal : before.execution.application.attempt = originalAttempt := by
      change (before.execution.observe app owner).application.2.attempt = originalAttempt
      rw [← viewed]
      exact secondRequest.1.symm
    have beforeClock : before.execution.application.current.native.clock = 2 := by
      change (before.execution.observe app owner).application.2.native.clock = 2
      rw [← viewed]
      exact secondClock
    have lower := (original_first_late_bad_iff seed before
      (countedMenu.toRawTrace initial horizon (family seed) prior) owner active beforeOriginal
        beforeClock).mp bad
    have ordered := (environment_prefix countedMenu seed before
      ⟨remaining, some focal, execution⟩ prior trace kept).length_le
    change before.execution.environmentRecall.length ≤ execution.environmentRecall.length
      at ordered
    omega

/-- A regular actual prefix has every foreign original receipt forecast and
therefore contributes the entire fixed-loss improvement to the original mark. -/
theorem regular_clock_two_preparation_mark
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (focal : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some focal, execution⟩))
    (request : execution.application.SeedRequest focal (originalCoordinate focal))
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = [])
    (regular : regularFirstLateControl seed (some ⟨remaining, some focal, execution⟩)) :
    preparationAdvantageMark seed (some ⟨remaining, some focal, execution⟩) focal = 3 / 2 := by
  classical
  change (if seed.2 focal = true ∧ ∀ other, other ≠ focal →
    originalReceiptForecast seed execution other then (3 / 2 : ℝ) else 0) = 3 / 2
  apply ite_eq_left
  refine ⟨regular.1 focal, ?_⟩
  intro other _different
  unfold originalReceiptForecast
  rw [regular.1 other]
  change (execution.recall other).length = 1 ∨ ∃ entry ∈ execution.recall other,
    entry.action.transmission ≠ none
  rcases regular.2 other with short | transmitted
  · exact Or.inl short
  · obtain ⟨first, _view, _request, _zero, records⟩ := original_first_late_foreign_records seed
      remaining execution focal (countedInRaw.trace initial horizon (family seed) trace)
        request.1.symm clock empty other
    rcases records with short | ⟨second, word, _secondView, _secondRequest, _secondClock⟩
    · exact Or.inl (by rw [short]; rfl)
    · right
      refine ⟨second, by rw [word]; simp, ?_⟩
      intro silent
      have actionEq : second.action = (⟨none⟩ : app.Action) := by
        have eta : second.action = ⟨second.action.transmission⟩ := by cases second.action; rfl
        exact eta.trans (congrArg ReactiveApplication.Action.mk silent)
      apply transmitted
      rw [word]
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.map_some, actionEq]

end Vegas.Examples.CommitSeedBroadcast
