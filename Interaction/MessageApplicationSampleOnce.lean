/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationLocality
import Interaction.MessageApplicationCounters

/-! # Retention of a sample-once submission through other-player polls -/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal uChoice

variable {Principal : Type uPrincipal} [DecidableEq Principal]

/-- If an owner's two polls submit a sampled payload and then wait, other
players' surrounding polls retain that exact fresh packet. Their private
commands, submissions, and replays are unrestricted. The law premise describes
the actual two polls; no acceptance or delivery assumption is made. -/
theorem runPolicies_submit_wait_packet (app : MessageApplication Principal)
    {Choice : Type uChoice} (owner : Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (before after : List (@Invocation Principal))
    (hbeforeEnvironment : Invocation.environment ∉ before)
    (hbeforeOwner : Invocation.player owner ∉ before)
    (hafterEnvironment : Invocation.environment ∉ after)
    (hafterOwner : Invocation.player owner ∉ after)
    (execution final : app.PolicyExecution)
    (hserials : execution.native.pool.SerialsBeforeNext)
    (kernel : FinDist Choice) (payload : Choice → app.Payload)
    (hlaw : app.runPolicies players environment
      (before ++ [.player owner, .player owner]) execution =
        (app.runPolicies players environment before execution).bind fun middle =>
          kernel.bind fun chosen =>
            (app.playerStep owner middle (.submit (payload chosen))).bind fun submitted =>
              app.playerStep owner submitted .wait)
    (hfinal : final ∈ (app.runPolicies players environment
      ((before ++ [.player owner, .player owner]) ++ after) execution).support) :
    ∃ chosen ∈ kernel.support,
      final.native.pool.nextSerial owner = execution.native.pool.nextSerial owner + 1 ∧
      final.native.pool.lookup (owner, execution.native.pool.nextSerial owner) =
        some ⟨(owner, execution.native.pool.nextSerial owner), payload chosen⟩ := by
  rw [runPolicies_append] at hfinal
  simp only [FinDist.support_bind, Set.mem_iUnion] at hfinal
  obtain ⟨waited, hwaited, hafter⟩ := hfinal
  rw [hlaw] at hwaited
  simp only [FinDist.support_bind, Set.mem_iUnion] at hwaited
  obtain ⟨middle, hmiddle, chosen, hchosen, submitted, hsubmitted, hwaited⟩ := hwaited
  have hbeforeFrame := app.runPolicies_other_frame owner (fun _ => ())
    (fun _ _ _ _ => rfl) players environment before hbeforeEnvironment hbeforeOwner
    execution middle hmiddle
  have hmiddleSerials := app.runPolicies_serialsBeforeNext players environment before
    execution middle hserials hmiddle
  have hafterFrame := app.runPolicies_other_frame owner (fun _ => ())
    (fun _ _ _ _ => rfl) players environment after hafterEnvironment hafterOwner
    waited final hafter
  have hpool : waited.native.pool = (middle.native.pool.submit owner (payload chosen)).2 := by
    simp only [playerStep, PlayerCommand.toAction, advance, step, FinDist.pure_bind,
      FinDist.mem_support_pure] at hsubmitted hwaited
    subst submitted
    subst waited
    rfl
  refine ⟨chosen, hchosen, ?_, ?_⟩
  · rw [hafterFrame.2.1, hpool]
    simp only [MessagePool.submit, if_pos, hbeforeFrame.2.1]
  · apply hafterFrame.2.2
    rw [hpool, ← hbeforeFrame.2.1]
    exact hmiddleSerials.lookup_submit owner _

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.runPolicies_submit_wait_packet'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_submit_wait_packet
