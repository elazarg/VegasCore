/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeService
import Vegas.Pending.ReactiveLateBlind
import Interaction.ReactivePriorityErasure

/-! # Erasure independence of the initialized late-opening service

Every finite nonnegative lottery weight gives an erasure-independent scheduler
on arbitrary environment inputs. Protected turns select the last unpublished
envelope of an authenticated author; the late turn uses the public pending
identifier lottery. Public completion gates and the padded stage index remain
unchanged by erasure. No service-contract or reachability premise is needed.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeServiceErasure

open Interaction GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService

private theorem latest_identifier_law (who : Player) (view : app.EnvironmentView)
    (predicate : Message Player app.Payload → Bool)
    (same : ∀ message, predicate message = true ↔
      message.sender = who ∧ view.Unpublished app message.id) :
    latestAuthor who view =
      ((view.network.pending.reverse.find? predicate).map Message.id).elim
        (ReactiveApplication.Command.wait : app.Command) ReactiveApplication.Command.include := by
  unfold latestAuthor
  have representation (selected : Option (Message Player app.Payload)) :
      (match selected with
      | none => (ReactiveApplication.Command.wait : app.Command)
      | some message => ReactiveApplication.Command.include message.id) =
        (selected.map Message.id).elim ReactiveApplication.Command.wait
          ReactiveApplication.Command.include := by
    cases selected <;> rfl
  refine (representation _).trans ?_
  apply congrArg (fun selected : Option (Message Player app.Payload) =>
    (selected.map Message.id).elim (ReactiveApplication.Command.wait : app.Command)
      ReactiveApplication.Command.include)
  apply congrArg (fun flag : Message Player app.Payload → Bool =>
    view.network.pending.reverse.find? flag)
  funext message
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using (same message).symm

/-- Deleting an unselected identifier preserves protected author selection. -/
theorem latestAuthor_restore_of_not_selected (who : Player) (view : app.EnvironmentView)
    (removed : MessageId Player) (notSelected : latestAuthor who view ≠ .include removed) :
    ReactiveApplication.Command.restore app removed
      (latestAuthor who (view.erase app removed)) = latestAuthor who view := by
  let before := fun message : Message Player app.Payload =>
    decide (message.sender = who ∧ view.Unpublished app message.id)
  let after := fun message : Message Player app.Payload =>
    decide (message.sender = who ∧ (view.erase app removed).Unpublished app message.id)
  have predicate : ∀ message : Message Player app.Payload, message.id ≠ removed →
      after ⟨MessageId.erase removed message.id, message.payload⟩ = before message := by
    intro message kept
    simp only [before, after, Message.sender, MessageId.erase_author,
      ReactiveApplication.EnvironmentView.unpublished_erase app view removed message.id kept]
  have original := latest_identifier_law who view before (by
    intro message
    simp only [before, decide_eq_true_eq])
  have erased := latest_identifier_law who (view.erase app removed) after (by
    intro message
    simp only [after, decide_eq_true_eq])
  have unselected : (view.network.pending.reverse.find? before).map Message.id ≠ some removed := by
    intro selected
    apply notSelected
    rw [original, selected]
    rfl
  have identifiers := Message.find_eraseList_restore removed before after predicate
    view.network.pending.reverse unselected
  rw [Message.eraseList_reverse] at identifiers
  have command := congrArg (fun id : Option (MessageId Player) =>
    id.elim (ReactiveApplication.Command.wait : app.Command)
      ReactiveApplication.Command.include) identifiers
  rw [original, erased]
  change ReactiveApplication.Command.restore app removed
    ((((Message.eraseList removed view.network.pending).reverse.find? after).map Message.id).elim
      ReactiveApplication.Command.wait ReactiveApplication.Command.include) =
    ((view.network.pending.reverse.find? before).map Message.id).elim
      ReactiveApplication.Command.wait ReactiveApplication.Command.include
  cases first : view.network.pending.reverse.find? before <;>
    cases second : (Message.eraseList removed view.network.pending).reverse.find? after
  all_goals first
  | rfl
  | simpa only [first, second, Option.map_none, Option.map_some, Option.elim_none,
      Option.elim_some, ReactiveApplication.Command.restore] using command

/-- At every input, protected author selection either includes the deleted
identifier or makes precisely the selection of the erased world. -/
theorem latestAuthor_include_or_erased (who : Player) (view : app.EnvironmentView)
    (removed : MessageId Player) :
    ∃ (probability : ℝ) (nonnegative : 0 ≤ probability) (atMost : probability ≤ 1),
      PMF.pure (latestAuthor who view) =
        mix probability nonnegative atMost (PMF.pure (.include removed))
          ((PMF.pure (latestAuthor who (view.erase app removed))).map
            (ReactiveApplication.Command.restore app removed)) := by
  classical
  by_cases selected : latestAuthor who view = .include removed
  · refine ⟨1, zero_le_one, le_rfl, ?_⟩
    rw [mix_one, selected]
  · refine ⟨0, le_rfl, zero_le_one, ?_⟩
    rw [mix_zero, PMF.pure_map,
      latestAuthor_restore_of_not_selected who view removed selected]

private theorem fixed_command_erasure (command : app.Command) (removed : MessageId Player)
    (restored : ReactiveApplication.Command.restore app removed command = command) :
    ∃ (probability : ℝ) (nonnegative : 0 ≤ probability) (atMost : probability ≤ 1),
      PMF.pure command = mix probability nonnegative atMost (PMF.pure (.include removed))
        ((PMF.pure command).map (ReactiveApplication.Command.restore app removed)) := by
  refine ⟨0, le_rfl, zero_le_one, ?_⟩
  rw [mix_zero, PMF.pure_map, restored]

/-- Every padded stage has the include-or-erased law, for every pending
identifier and every finite nonnegative lottery weight. -/
theorem stageChoice_include_or_erased (weight : ℝ) (nonnegative : 0 ≤ weight)
    (position : Nat) (view : app.EnvironmentView) (message : Message Player app.Payload)
    (pending : message ∈ view.network.pending) :
    ∃ (probability : ℝ) (nonnegativeProbability : 0 ≤ probability) (atMost : probability ≤ 1),
      stageChoice weight nonnegative position view =
        mix probability nonnegativeProbability atMost (PMF.pure (.include message.id))
          ((stageChoice weight nonnegative position (view.erase app message.id)).map
            (ReactiveApplication.Command.restore app message.id)) := by
  by_cases inside : position < 26
  · interval_cases position
    all_goals first
    | simpa only [stageChoice] using latestAuthor_include_or_erased alice view message.id
    | simpa only [stageChoice] using latestAuthor_include_or_erased bob view message.id
    | simpa only [stageChoice, ReactiveApplication.eraseEnvironmentRecall, List.map_nil] using
        app.pendingLotteryScheduler_include_or_erased weight nonnegative [] view message pending
    | simpa only [stageChoice] using fixed_command_erasure _ message.id rfl
    | (by_cases completed : bobBindEvent ∈ view.application.observation.completionOrder
       · simpa only [stageChoice, ReactiveApplication.EnvironmentView.erase, completed,
           ↓reduceIte] using latestAuthor_include_or_erased bob view message.id
       · simpa only [stageChoice, ReactiveApplication.EnvironmentView.erase, completed,
           ↓reduceIte] using fixed_command_erasure .wait message.id rfl)
    | (by_cases completed : bobBindEvent ∈ view.application.observation.completionOrder
       · simpa only [stageChoice, ReactiveApplication.EnvironmentView.erase, completed,
           ↓reduceIte] using fixed_command_erasure (.activate bob) message.id rfl
       · simpa only [stageChoice, ReactiveApplication.EnvironmentView.erase, completed,
           ↓reduceIte] using fixed_command_erasure .wait message.id rfl)
  · have idle : stageChoice weight nonnegative position view = PMF.pure .wait := by
      unfold stageChoice
      split <;> first | omega | rfl
    have erasedIdle : stageChoice weight nonnegative position (view.erase app message.id) =
        PMF.pure .wait := by
      unfold stageChoice
      split <;> first | omega | rfl
    rw [idle, erasedIdle]
    exact fixed_command_erasure .wait message.id rfl

/-- The actual service scheduler satisfies late-packet erasure independence
for every finite nonnegative weight, without assuming its service contract. -/
theorem scheduler_blind (weight : ℝ) (nonnegative : 0 ≤ weight) :
    LateOpeningRuntimeService.runtime.BlindToLatePackets leaks LateOpeningRuntimeService.bound
      (LateOpeningRuntimeService.scheduler weight nonnegative) := by
  intro past view message pending _late
  have lengthErase : (app.eraseEnvironmentRecall message.id past).length = past.length := by
    exact List.length_map ..
  simpa only [LateOpeningRuntimeService.scheduler, lengthErase] using
    stageChoice_include_or_erased weight nonnegative past.length view message pending

end Vegas.Examples.LateOpeningRuntimeServiceErasure
