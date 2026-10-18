/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperPreparationObservation

/-! # The actual single-helper initial frame modulo its private preparation -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- Advancing the actual prepared prefix keeps its external comparison. The
entire candidate catalogue is retained; no initial state is reinitialized. -/
theorem helper_preparation_advance (hidden : Player) (clock : Nat)
    (left right : app.Execution)
    (first second : CommitmentCandidates Player (CandidateSlot graph) (Raw simpleExpr))
    (leftFrame : left.application = preparedApplication clock first)
    (rightFrame : right.application = preparedApplication clock second)
    (same : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right) :
    phaseExternalObservation runtime leaks hidden (advance left) =
      phaseExternalObservation runtime leaks hidden (advance right) := by
  have network : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun data => data.2.1) same
  have service : left.environmentRecall = right.environmentRecall :=
    congrArg (fun data => data.2.2.1) same
  have environment : left.observeEnvironment app = right.observeEnvironment app :=
    congrArg (fun data => data.2.2.2.1) same
  have inputs (who : Player) (different : who ≠ hidden) :
      (left.recall who, left.observe app who) = (right.recall who, right.observe app who) := by
    have viewed := congrFun (congrArg (fun data => data.2.2.2.2) same) who
    change (if who = hidden then none else some (left.recall who, left.observe app who)) =
      (if who = hidden then none else some (right.recall who, right.observe app who)) at viewed
    exact Option.some.inj (by simpa only [different, ite_false] using viewed)
  apply phaseExternalObservation_congr runtime leaks (advance left) (advance right) hidden
  · exact network
  · exact receipts
  · change left.environmentRecall ++ [⟨left.observeEnvironment app, .application .advanceClock⟩] =
      right.environmentRecall ++ [⟨right.observeEnvironment app, .application .advanceClock⟩]
    rw [service, environment]
  · rw [advance_prepared left clock first leftFrame,
      advance_prepared right clock second rightFrame]
    rfl
  · intro who different
    have candidates := congrArg (fun input => input.2.application.1.candidates)
      (inputs who different)
    change left.application.current.native.candidates.table who =
      right.application.current.native.candidates.table who at candidates
    rw [leftFrame, rightFrame] at candidates
    change first.table who = second.table who at candidates
    change ((advance left).application.playerView who) =
      ((advance right).application.playerView who)
    rw [advance_prepared left clock first leftFrame,
      advance_prepared right clock second rightFrame]
    change ((preparedApplication (clock + 1) first).current.native.playerView who,
      (preparedApplication (clock + 1) first).publicView) =
        ((preparedApplication (clock + 1) second).current.native.playerView who,
          (preparedApplication (clock + 1) second).publicView)
    refine Prod.ext ?_ ?_
    · change (⟨who, _, _, first.table who⟩ : EventGraphRuntime.PlayerView graph) =
        ⟨who, _, _, second.table who⟩
      rw [candidates]
      rfl
    · rfl
  · intro who different
    exact congrArg Prod.fst (inputs who different)

private theorem helper_preparation_quiet_response (hidden actor : Player)
    (left right : app.Execution)
    (same : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right) :
    phaseExternalObservation runtime leaks hidden (quietResponse left actor) =
      phaseExternalObservation runtime leaks hidden (quietResponse right actor) := by
  have sampled := helper_preparation_activation hidden actor left right same
  by_cases own : actor = hidden
  · subst actor
    exact helper_preparation_silent hidden _ _ sampled
  · exact helper_preparation_response hidden actor own _ _ sampled ⟨none⟩

/-- The literal five-command frame with exactly this owner's initial packet.
This uses the same initial responses and two actual native clock advances. -/
def initialHelperFrame (hidden : Player) (material : WitnessedSubmission graph) : app.Execution :=
  initialClockTwo
    (if alice = hidden then ⟨some material⟩ else ⟨none⟩)
    (if bob = hidden then ⟨some material⟩ else ⟨none⟩)
    (if carol = hidden then ⟨some material⟩ else ⟨none⟩)

/-- Equality of the one public helper packet already fixes the complete
unsent-owner frame after the original five commands. Arbitrary unusable
preparations and evidence aliases remain in the hidden helper state. -/
theorem initial_helper_frame_external (hidden : Player)
    (first second : WitnessedSubmission graph)
    (packet : app.packet (app.submit (initialCallback hidden).application hidden first) hidden
        ((initialCallback hidden).network.known hidden) first =
      app.packet (app.submit (initialCallback hidden).application hidden second) hidden
        ((initialCallback hidden).network.known hidden) second) :
    phaseExternalObservation runtime leaks hidden (initialHelperFrame hidden first) =
      phaseExternalObservation runtime leaks hidden (initialHelperFrame hidden second) := by
  let left := afterInitialResponses
    (if alice = hidden then ⟨some first⟩ else ⟨none⟩)
    (if bob = hidden then ⟨some first⟩ else ⟨none⟩)
    (if carol = hidden then ⟨some first⟩ else ⟨none⟩)
  let right := afterInitialResponses
    (if alice = hidden then ⟨some second⟩ else ⟨none⟩)
    (if bob = hidden then ⟨some second⟩ else ⟨none⟩)
    (if carol = hidden then ⟨some second⟩ else ⟨none⟩)
  have source : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right := by
    have submitted := helper_preparation_alias_submission hidden
      (initialCallback hidden) (initialCallback hidden) rfl first second packet
    fin_cases hidden
    · change phaseExternalObservation runtime leaks alice
        (quietResponse (quietResponse
          ((initialCallback alice).respond app alice ⟨some first⟩) bob) carol) =
        phaseExternalObservation runtime leaks alice
          (quietResponse (quietResponse
            ((initialCallback alice).respond app alice ⟨some second⟩) bob) carol)
      exact helper_preparation_quiet_response alice carol _ _
        (helper_preparation_quiet_response alice bob _ _ submitted)
    · change phaseExternalObservation runtime leaks bob
        (quietResponse ((initialCallback bob).respond app bob ⟨some first⟩) carol) =
        phaseExternalObservation runtime leaks bob
          (quietResponse ((initialCallback bob).respond app bob ⟨some second⟩) carol)
      exact helper_preparation_quiet_response bob carol _ _ submitted
    · exact submitted
  obtain ⟨leftCandidates, leftFrame⟩ := afterInitialResponses_prepared
    (if alice = hidden then ⟨some first⟩ else ⟨none⟩)
    (if bob = hidden then ⟨some first⟩ else ⟨none⟩)
    (if carol = hidden then ⟨some first⟩ else ⟨none⟩)
  obtain ⟨rightCandidates, rightFrame⟩ := afterInitialResponses_prepared
    (if alice = hidden then ⟨some second⟩ else ⟨none⟩)
    (if bob = hidden then ⟨some second⟩ else ⟨none⟩)
    (if carol = hidden then ⟨some second⟩ else ⟨none⟩)
  change phaseExternalObservation runtime leaks hidden (advance (advance left)) =
    phaseExternalObservation runtime leaks hidden (advance (advance right))
  exact helper_preparation_advance hidden 1 _ _ leftCandidates rightCandidates
    (advance_prepared left 0 leftCandidates leftFrame)
    (advance_prepared right 0 rightCandidates rightFrame)
    (helper_preparation_advance hidden 0 left right leftCandidates rightCandidates
      leftFrame rightFrame source)

end Vegas.Examples.CommitSeedBroadcast
