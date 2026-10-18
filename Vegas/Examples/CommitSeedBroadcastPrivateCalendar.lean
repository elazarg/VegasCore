/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastTailExhaustion
import Vegas.Examples.CommitSeedBroadcastAddressedSeed

/-! # Complete coordinate-relative calendars of the installed native family -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem original_request_coordinate (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (original : coordinate.attempt = originalAttempt)
    (request : current.execution.application.SeedRequest owner coordinate) :
    coordinate = originalCoordinate owner := by
  have phases := original_phases (family seeds) current trace (request.1.symm.trans original)
  obtain ⟨phase, installed, inside⟩ := request.2.1
  rw [phases] at installed
  have samePhase : phase = commitmentPhase := (Option.some.inj installed).symm
  subst phase
  have interval := (RuntimePhase.mem_events commitmentPhase coordinate.event).mp inside
  change 0 ≤ coordinate.event.val ∧ coordinate.event.val < 3 at interval
  have actor := request.2.2.2.1
  rcases coordinate with ⟨attempt, event⟩
  change attempt = originalAttempt at original
  subst attempt
  change Fin 6 at event
  fin_cases event
  · have sameOwner : owner = alice := Option.some.inj (actor.symm.trans (binding_actor alice))
    subst owner
    rfl
  · have sameOwner : owner = bob := Option.some.inj (actor.symm.trans (binding_actor bob))
    subst owner
    rfl
  · have sameOwner : owner = carol := Option.some.inj (actor.symm.trans (binding_actor carol))
    subst owner
    rfl
  · change 0 ≤ 3 ∧ 3 < 3 at interval
    omega
  · change 0 ≤ 4 ∧ 4 < 3 at interval
    omega
  · change 0 ≤ 5 ∧ 5 < 3 at interval
    omega

def relativeCalendar (coordinate : PhaseSeedAddress graph) (_seed : Bool) : List Nat :=
  if coordinate.1.attempt = originalAttempt then [0, 2, 3] else [0]

/-- These are the exact existing calendar requirements on genuine counted
histories; the addressed representation is the same installed scheduler. -/
theorem family_privateActivationCalendar :
    PhaseService.PrivateActivationCalendar runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon addressedSeedLaw addressedFamily := by
  classical
  unfold PhaseService.PrivateActivationCalendar
  rw [← initial_eq_compiled]
  refine ⟨relativeCalendar, ?_, ?_⟩
  · intro seeds _supported remaining owner execution trace coordinate request _unsent
    let core := addressedSeedCore seeds
    change (countedMenu.protocol initial horizon (family core)).Trace
      (some ⟨remaining, some owner, execution⟩) at trace
    by_cases original : coordinate.1.attempt = originalAttempt
    · have same := original_request_coordinate core _
        (countedMenu.toRawTrace initial horizon (family core) trace) coordinate.1 owner original
          request
      rw [relativeCalendar, ite_eq_left original]
      rw [same] at request ⊢
      exact original_service_clocks_prefix countedMenu core _ trace owner rfl request
    · rw [relativeCalendar, ite_eq_right original]
      rw [tail_service_clocks countedMenu (PhaseCount.silence_onePacket runtime leaks bounds)
        core _ trace owner rfl coordinate.1 original request]
  · intro seeds _supported current trace coordinate owner genuine resolved empty
    let core := addressedSeedCore seeds
    change (countedMenu.protocol initial horizon (family core)).Trace (some current) at trace
    obtain ⟨before, beforeTrace, kept, request⟩ := genuine
    change (countedMenu.protocol initial horizon (family core)).Trace (some before) at beforeTrace
    by_cases original : coordinate.1.attempt = originalAttempt
    · have same := original_request_coordinate core before
        (countedMenu.toRawTrace initial horizon (family core) beforeTrace) coordinate.1 owner
          original request
      rw [relativeCalendar, ite_eq_left original]
      rw [same] at resolved empty ⊢
      exact original_binding_exhausted_clocks core current trace owner resolved empty
    · rw [relativeCalendar, ite_eq_right original]
      exact tail_episode_exhausted_clocks core before current beforeTrace trace kept coordinate.1
        owner original request resolved empty

end Vegas.Examples.CommitSeedBroadcast
