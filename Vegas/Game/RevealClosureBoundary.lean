/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealRunTargetPhase

/-! # Phase boundaries seen through the closure

At a phase boundary every event from the boundary's rank on that has completed
did so automatically for an owner defaulted earlier, and no event is
automatically ready. So the configuration is read from the deviator's view of
its closure: two boundaries whose closures look alike to the deviator look
alike themselves.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- **Reflection at a phase boundary.** Two phase boundaries at one rank whose
closures look alike to the deviator look alike to the deviator. -/
theorem phaseBoundary_reflect (reference : (serviceGraph setup mode).BehavioralProfile)
    (who : Player)
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy} {horizon rank : Nat}
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (leftBoundary : PhaseBoundary scheduler players horizon rank left)
    (rightBoundary : PhaseBoundary scheduler players horizon rank right)
    (views : keyView who (runKey (closure reference who left.application.config)) =
      keyView who (runKey (closure reference who right.application.config))) :
    keyView who (runKey left.application.config) =
      keyView who (runKey right.application.config) := by
  classical
  let G := serviceGraph setup mode
  rw [keyView_runKey, keyView_runKey] at views
  have same := Option.some.inj views
  have leftPath := closure_path reference who left.application.config
  have rightPath := closure_path reference who right.application.config
  -- defaults transfer through the deviator's view of the closures
  have defaultsTransfer {first second : (serviceApplication setup mode deadline leaks).Execution}
      (firstBoundary : PhaseBoundary scheduler players horizon rank first)
      (secondBoundary : PhaseBoundary scheduler players horizon rank second)
      (sameViews : G.normalizeObservation who (G.playerObserve who
          (closure reference who first.application.config)) =
        G.normalizeObservation who (G.playerObserve who
          (closure reference who second.application.config)))
      {owner : Player} (inactive : owner ∈ first.application.config.defaulted) :
      owner ∈ second.application.config.defaulted := by
    rw [mem_defaulted_iff_completionOf] at inactive ⊢
    obtain ⟨defaulting, found⟩ := inactive
    obtain ⟨record, recorded⟩ : ∃ record,
        completionOf first.application.config defaulting = some record := by
      cases recordedEq : completionOf first.application.config defaulting with
      | none => rw [recordedEq] at found; cases found
      | some record => exact ⟨record, rfl⟩
    have done : defaulting ∈ first.application.config.cut.completed :=
      (completionOf_isSome_iff _ defaulting).mp (by rw [recorded]; rfl)
    have early : defaulting.val < rank := by
      by_contra late
      push Not at late
      rw [(firstBoundary.later defaulting late done).1] at found
      cases found
    have secondDone := secondBoundary.earlier defaulting early
    obtain ⟨secondRecord, secondRecorded⟩ := Option.isSome_iff_exists.mp
      ((completionOf_isSome_iff _ defaulting).mpr secondDone)
    have firstClosure := Config.Step.path_completionOf_of_some
      (closure_path reference who first.application.config) defaulting record recorded
    have secondClosure := Config.Step.path_completionOf_of_some
      (closure_path reference who second.application.config) defaulting secondRecord
      secondRecorded
    have defaults := normalize_defaultEvent_congr who sameViews defaulting
      (by rw [firstClosure]; rfl)
    rw [firstClosure, secondClosure] at defaults
    refine ⟨defaulting, ?_⟩
    rw [secondRecorded, ← defaults, ← recorded]
    exact found
  have sets : left.application.config.cut.completed = right.application.config.cut.completed := by
    have oneWay {first second : (serviceApplication setup mode deadline leaks).Execution}
        (firstBoundary : PhaseBoundary scheduler players horizon rank first)
        (secondBoundary : PhaseBoundary scheduler players horizon rank second)
        (sameViews : G.normalizeObservation who (G.playerObserve who
            (closure reference who first.application.config)) =
          G.normalizeObservation who (G.playerObserve who
            (closure reference who second.application.config))) :
        ∀ event : G.EventId, event ∈ first.application.config.cut.completed →
          event ∈ second.application.config.cut.completed := by
      intro event
      induction hval : event.val using Nat.strong_induction_on generalizing event with
      | _ value ih =>
      intro done
      by_cases early : event.val < rank
      · exact secondBoundary.earlier event early
      push Not at early
      obtain ⟨_, _, owner, owned, inactive⟩ := firstBoundary.later event early done
      by_contra pending
      have ready : second.application.config.cut.Ready event := ⟨pending, fun prior member =>
        ih prior.val (hval ▸ G.order.predecessor_lt member) prior rfl
          (first.application.config.cut.predecessor_closed done member)⟩
      apply secondBoundary.quiescent event
      unfold EventGraphRuntime.State.AutomaticReady
      rw [owned]
      exact ⟨ready, defaultsTransfer firstBoundary secondBoundary sameViews inactive⟩
    ext event
    exact ⟨oneWay leftBoundary rightBoundary same event,
      oneWay rightBoundary leftBoundary same.symm event⟩
  rw [keyView_runKey, keyView_runKey, normalizeObservation_playerObserve_restrict who _
    (Config.restrictionOf_of_completed rfl leftPath)
    (Config.restrictionOf_of_completed sets.symm rightPath) same]

end Vegas
