/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.ReactiveMenusStrategies

/-! # No common behavioral SPE in the reactive reserved service

The canonical history runner agrees with scheduler-round evaluation, including
all private recall. At the proper root, each utility has a deviation worth 2,
but the sum of the two incumbent expected utilities is at most 3.
-/

noncomputable section

namespace VegasTests.ReactiveMenus

open GameTheory.Protocol GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

abbrev reactiveRun (policy : app.Policy) (fuel : Nat) (history : arena.History) :=
  model.runSingleMoverBehavioralFrom (app.singleMover initialLaw horizon scheduler)
    (fun _ => app.encodePolicy policy) fuel history

def reactiveResult : arena.State → Option (PublicationResult Int)
  | none => none
  | some control => control.execution.application.config.outputs 1

def reactivePayoff (preferOne : Bool) (final : arena.History) (_who : Unit) : ℝ :=
  PendingMenus.publicUtility preferOne (reactiveResult final.state)

theorem root_run_law (policy : app.Policy) :
    (reactiveRun policy (2 * horizon + 1) (rootHistory first second)).map
      ExecutionProtocol.History.state =
        (app.runRounds scheduler (fun _ => policy) 111 contested).map app.finished := by
  rw [app.run_map_state]
  change (fun law => law.bind
    (app.controlStep initialLaw horizon scheduler (fun _ => policy)))^[2 * horizon + 1]
      (FinDist.pure (some (rootControl first second))) = _
  rw [app.iterate_eq_finish initialLaw horizon scheduler (fun _ => policy) _ _ (by decide)]
  change ((FinDist.pure contested).bind
    (app.runRounds scheduler (fun _ => policy) 111)).map app.finished = _
  rw [FinDist.pure_bind]

theorem root_value (policy : app.Policy) (preferOne : Bool) :
    (reactiveRun policy (2 * horizon + 1) (rootHistory first second)).expect
      (fun final => reactivePayoff preferOne final ()) =
        (app.runRounds scheduler (fun _ => policy) 111 contested).expect
          (fun final => PendingMenus.publicUtility preferOne
            (final.application.config.outputs 1)) := by
  have law := congrArg (fun law => law.expect
    (fun state => PendingMenus.publicUtility preferOne (reactiveResult state)))
      (root_run_law policy)
  simpa only [FinDist.expect_map, reactivePayoff, reactiveResult,
    ReactiveApplication.finished] using law

/-- Arbitrary randomized information-local policies cannot satisfy both
continuation benchmarks. The root is reachable from the actual initial state;
its closure includes every legal history, not only paths of a chosen profile. -/
theorem no_common_reactive_spe :
    ¬ ∃ profile : GameTheory.Profile model.behavioralSignature,
      model.IsBehavioralSubgamePerfect
        (app.singleMover initialLaw horizon scheduler)
        (app.bounded initialLaw horizon scheduler) profile (reactivePayoff true) ∧
      model.IsBehavioralSubgamePerfect
        (app.singleMover initialLaw horizon scheduler)
        (app.bounded initialLaw horizon scheduler) profile (reactivePayoff false) := by
  rintro ⟨profile, one, two⟩
  let policy := app.decodePolicy (profile ())
  have profileEq : profile = fun _ => app.encodePolicy policy := by
    funext who
    cases who
    exact (app.encode_decodePolicy (profile ())).symm
  have deviation (preferOne : Bool) :
      GameTheory.Profile.update profile () (app.encodePolicy (recoveryPolicy preferOne)) =
        fun _ => app.encodePolicy (recoveryPolicy preferOne) := by
    funext who
    cases who
    simp [GameTheory.Profile.update]
  rw [InformationModel.isBehavioralSubgamePerfect_iff] at one two
  have oneBound := one (rootHistory first second) root_isSubgameRoot ()
    (app.encodePolicy (recoveryPolicy true))
  have twoBound := two (rootHistory first second) root_isSubgameRoot ()
    (app.encodePolicy (recoveryPolicy false))
  rw [deviation, profileEq] at oneBound twoBound
  change (reactiveRun (recoveryPolicy true) (2 * horizon + 1) _).expect
      (fun final => reactivePayoff true final ()) ≤
    (reactiveRun policy (2 * horizon + 1) _).expect
      (fun final => reactivePayoff true final ()) at oneBound
  change (reactiveRun (recoveryPolicy false) (2 * horizon + 1) _).expect
      (fun final => reactivePayoff false final ()) ≤
    (reactiveRun policy (2 * horizon + 1) _).expect
      (fun final => reactivePayoff false final ()) at twoBound
  rw [root_value, root_value, show 111 = 12 + 99 from rfl,
    recovery_rounds_value] at oneBound twoBound
  linarith [rounds_value_sum_le (fun _ => policy) 108]

end VegasTests.ReactiveMenus
