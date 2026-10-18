/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialCallbackSeed
import Vegas.Examples.CommitSeedBroadcastCountedFiber
import Vegas.Examples.CommitSeedBroadcastSeedTrace
import Interaction.ReactiveRoundTrace

/-! # The whole raw information fiber at a quiet initial decision -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem initial_quiet_prefix (seed : Seeds) (owner : Player) :
    app.runRounds (family seed) (fun _ => app.silentPolicy) owner.val initialExecution =
      PMF.pure (initialBefore owner) := by
  fin_cases owner <;>
    simp only [ReactiveApplication.runRounds, initial_alice_round, initial_bob_round,
      ReactiveApplication.silentPolicy, PMF.pure_map, PMF.pure_bind]
  all_goals rfl

/-- A quiet initial control is a genuine counted native history under every
original seed, including when the equilibrium assigns it zero probability. -/
theorem quiet_initial_fixed_trace (seed : Seeds) (owner : Player) :
    Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨horizon - owner.val - 1, some owner, initialCallback owner⟩)) := by
  have covered : ∀ who past view action,
      action ∈ ((fun _ => app.silentPolicy) who past view).support →
        action ∈ countedMenu.actions who past view := by
    intro who past view action supported
    rw [app.silentPolicy_cases past view action supported]
    exact PhaseCount.silence_onePacket runtime leaks bounds who past view
  obtain ⟨before⟩ := countedMenu.trace_roundsFrom initial horizon (family seed)
    (fun _ => app.silentPolicy) covered owner.val (by have := owner.isLt; norm_num; omega)
      (initialBefore owner) (by
        rw [ReactiveApplication.roundsFrom, initial, PMF.pure_bind]
        change initialBefore owner ∈ (app.runRounds (family seed)
          (fun _ => app.silentPolicy) owner.val initialExecution).support
        rw [initial_quiet_prefix, PMF.mem_support_pure_iff])
  have budget : horizon - owner.val = horizon - owner.val - 1 + 1 := by
    have := owner.isLt
    norm_num
    omega
  rw [budget] at before
  exact countedMenu.trace_environment initial horizon (family seed)
    (horizon - owner.val - 1) (initialBefore owner) (initialCallback owner) (.activate owner)
      before (by rw [family_initial_callback, PMF.mem_support_pure_iff])
      (by rw [completeActivation_law, PMF.mem_support_pure_iff]; rfl)

/-- The actual mixed scheduler retains each of these counted controls. -/
theorem quiet_initial_counted_trace (owner : Player) :
    Nonempty (countedProtocol.Trace
      (some ⟨horizon - owner.val - 1, some owner, initialCallback owner⟩)) := by
  obtain ⟨seed, supported⟩ := nativeSeedLaw.support_nonempty
  exact counted_fixed_decision_mixed seed supported _ _ owner
    (quiet_initial_fixed_trace seed owner).some

/-- Complete initial observations determine the entire native execution in
the quiet information fiber, rather than merely its public state. -/
theorem quiet_initial_raw_fiber_execution (owner : Player) (remaining : Nat)
    (execution : app.Execution)
    (trace : rawProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (recalled : execution.recall owner = (initialCallback owner).recall owner)
    (observed : execution.observe app owner = (initialCallback owner).observe app owner) :
    execution = initialCallback owner := by
  have inputs := app.complete_decision_inputs_congr rfl initial horizon scheduler scheduler
    ⟨horizon - owner.val - 1, some owner, initialCallback owner⟩
    ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon scheduler (quiet_initial_counted_trace owner).some)
    (rawMenu.toRawTrace initial horizon scheduler trace) owner rfl rfl recalled.symm observed.symm
  have quietInputs : (initialCallback owner).network.inputs = [] := by fin_cases owner <;> rfl
  have empty : execution.network.inputs = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro message member
    have present := (inputs message).mpr member
    rw [quietInputs] at present
    exact List.not_mem_nil present
  have original : execution.application.attempt = originalAttempt := by
    have sameAttempt := congrArg (fun view : app.PlayerView => view.application.2.attempt) observed
    have quiet : (initialCallback owner).application.attempt = originalAttempt := by
      fin_cases owner <;> exact initialState_attempt
    exact sameAttempt.trans quiet
  have clock : execution.application.current.native.clock = 0 := by
    have sameClock := congrArg
      (fun view : app.PlayerView => view.application.1.publicView.clock) observed
    have quiet : (initialCallback owner).application.current.native.clock = 0 := by
      fin_cases owner <;> exact initialState_clock
    exact sameClock.trans quiet
  obtain ⟨seed, supported⟩ :=
    (implementation.posterior execution.environmentRecall).support_nonempty
  obtain ⟨_originalSeed, ⟨fixed⟩⟩ := menu_original_posterior_trace rawMenu
    ⟨remaining, some owner, execution⟩ trace seed supported
  exact original_zero_empty_callback seed remaining execution owner fixed original clock empty

/-- At the literal quiet callback, the actual native trace fixes the entire
remaining horizon as well as the player's physical execution. -/
theorem quiet_initial_remaining (selected : app.Scheduler) (owner : Player) (remaining : Nat)
    (trace : (app.protocol initial horizon selected).Trace
      (some ⟨remaining, some owner, initialCallback owner⟩)) :
    remaining = horizon - owner.val - 1 := by
  have position := app.raw_trace_horizon initial horizon selected trace
  have length : (initialCallback owner).environmentRecall.length = owner.val + 1 := by
    fin_cases owner <;> rfl
  change (initialCallback owner).environmentRecall.length + remaining = horizon at position
  rw [length] at position
  omega

end Vegas.Examples.CommitSeedBroadcast
