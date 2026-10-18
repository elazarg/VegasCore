/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastNativeTimingWait
import Vegas.Examples.CommitSeedBroadcastPosteriorTrace
import Interaction.ReactiveSchedulerFinishSeed

/-! # Original-posterior continuation bounds after a remembered late omission -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Projecting the joint realization retains the exact original seed posterior
and every physical future outcome, including a currently pending response. -/
theorem native_finish_original_seed_law (players : Player → app.Policy)
    (current : app.Control) :
    app.finish initial horizon scheduler players (some current) =
      (implementation.posterior current.execution.environmentRecall).bind fun seed =>
        app.finish initial horizon (family seed) players (some current) := by
  have joint := congrArg (fun law : PMF (app.ProtocolState × Seeds) => law.map Prod.fst)
    (app.schedulerMixture_finish_joint nativeSeedLaw family initial horizon players (some current))
  simpa only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
    PMF.bind_const, PMF.bind_pure, scheduler, implementation]
    using joint.symm

/-- The actual full continuation retains both recorded omissions. Its terminal
bound allows every count-permitted opposing response and every preparation. -/
theorem counted_waits_fixed_finish_value_upper
    (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩)) (owner : Player)
    (first last : app.PlayerEntry)
    (firstMember : first ∈ execution.recall owner) (lastMember : last ∈ execution.recall owner)
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (lastRequest : PhaseRuntimeState.requests last.beforeView.application.2 owner
      (originalCoordinate owner))
    (firstSilent : first.action.transmission = none)
    (lastSilent : last.action.transmission = none)
    (firstClock : first.beforeView.application.2.native.clock = 0)
    (lastClock : last.beforeView.application.2.native.clock = 2)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view) :
    expect (app.finish initial horizon (family seed) players
      (some ⟨remaining, none, execution⟩)) (fun state => netPayoff state owner) ≤
        (5 / 2 : ℝ) * (if seed.2 owner = false then 1 else 0) - 3 / 2 := by
  have bounded (state : app.ProtocolState) : |netPayoff state owner| ≤ (9 / 2 : ℝ) := by
    have range := netPayoff_mem_Icc state owner
    exact abs_le.mpr ⟨range.1, by linarith [range.2]⟩
  apply expect_le_const _ _ (payoffIntegrable_of_bounded _ _ bounded)
  intro state reached
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind] at reached
  obtain ⟨after, continued, rfl⟩ := PMF.support_map .. ▸ reached
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 remaining execution after (by simpa only [Nat.zero_add] using trace) continued
  let retained : app.PolicyInvariant players (fun current =>
      first ∈ current.recall owner ∧ last ∈ current.recall owner) := {
    respond := fun before actor action valid _ =>
      ⟨app.respond_recall_mono before actor owner action valid.1,
        app.respond_recall_mono before actor owner action valid.2⟩
    environment := fun before next command valid moved => by
      rw [app.environmentStep_recall before next command moved]
      exact valid }
  have kept := retained.runRounds (family seed) remaining execution after
    ⟨firstMember, lastMember⟩ continued
  exact counted_waits_terminal_payoff_upper seed after finalTrace owner first last
    kept.1 kept.2 firstRequest lastRequest firstSilent lastSilent firstClock lastClock

/-- Averaging uses the original seed posterior of the actual native prefix.
The entire future physical law remains the selected scheduler's continuation. -/
theorem counted_waits_finish_value_upper
    (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, none, execution⟩)) (owner : Player)
    (first last : app.PlayerEntry)
    (firstMember : first ∈ execution.recall owner) (lastMember : last ∈ execution.recall owner)
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (lastRequest : PhaseRuntimeState.requests last.beforeView.application.2 owner
      (originalCoordinate owner))
    (firstSilent : first.action.transmission = none)
    (lastSilent : last.action.transmission = none)
    (firstClock : first.beforeView.application.2.native.clock = 0)
    (lastClock : last.beforeView.application.2.native.clock = 2)
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view) :
    expect (app.finish initial horizon scheduler players
      (some ⟨remaining, none, execution⟩)) (fun state => netPayoff state owner) ≤
        (5 / 2 : ℝ) * expect (implementation.posterior execution.environmentRecall)
          (fun seed => if seed.2 owner = false then (1 : ℝ) else 0) - 3 / 2 := by
  have bounded (state : app.ProtocolState) : |netPayoff state owner| ≤ (9 / 2 : ℝ) := by
    have range := netPayoff_mem_Icc state owner
    exact abs_le.mpr ⟨range.1, by linarith [range.2]⟩
  rw [native_finish_original_seed_law,
    expect_bind_tower_bounded _ _ _ bounded]
  have comparison := expect_mono (μ := implementation.posterior execution.environmentRecall)
    (f := fun seed => expect (app.finish initial horizon (family seed) players
      (some ⟨remaining, none, execution⟩)) (fun state => netPayoff state owner))
    (g := fun seed => (5 / 2 : ℝ) * (if seed.2 owner = false then 1 else 0) - 3 / 2)
    (fun seed supported => by
      obtain ⟨_original, ⟨fixed⟩⟩ := menu_original_posterior_trace countedMenu
        ⟨remaining, none, execution⟩ trace seed supported
      exact counted_waits_fixed_finish_value_upper seed remaining execution fixed owner first last
        firstMember lastMember firstRequest lastRequest firstSilent lastSilent firstClock lastClock
          players covered)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  rw [expect_sub (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _),
    expect_const_mul, expect_constant] at comparison
  exact comparison

end Vegas.Examples.CommitSeedBroadcast
