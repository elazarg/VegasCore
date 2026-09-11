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

/-- A concrete submit/wait branch surrounded by other-player polls retains the
submitted packet at the owner's fresh serial. -/
theorem runPolicies_submit_wait_branch_packet (app : MessageApplication Principal)
    (owner : Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (before after : List (@Invocation Principal))
    (hbeforeEnvironment : Invocation.environment ∉ before)
    (hbeforeOwner : Invocation.player owner ∉ before)
    (hafterEnvironment : Invocation.environment ∉ after)
    (hafterOwner : Invocation.player owner ∉ after)
    (execution final : app.PolicyExecution)
    (hserials : execution.native.pool.SerialsBeforeNext)
    (payload : app.Payload)
    (hbranch : final ∈
      ((app.runPolicies players environment before execution).bind fun middle =>
        (app.playerStep owner middle (.submit payload)).bind fun submitted =>
          (app.playerStep owner submitted .wait).bind fun waited =>
            app.runPolicies players environment after waited).support) :
    final.native.pool.nextSerial owner = execution.native.pool.nextSerial owner + 1 ∧
      final.native.pool.lookup (owner, execution.native.pool.nextSerial owner) =
        some ⟨(owner, execution.native.pool.nextSerial owner), payload⟩ := by
  simp only [FinDist.support_bind, Set.mem_iUnion] at hbranch
  obtain ⟨middle, hmiddle, submitted, hsubmitted, waited, hwaited, hafter⟩ := hbranch
  have hbeforeFrame := app.runPolicies_other_frame owner (fun _ => ())
    (fun _ _ _ _ => rfl) players environment before hbeforeEnvironment hbeforeOwner
    execution middle hmiddle
  have hmiddleSerials := app.runPolicies_serialsBeforeNext players environment before
    execution middle hserials hmiddle
  have hafterFrame := app.runPolicies_other_frame owner (fun _ => ())
    (fun _ _ _ _ => rfl) players environment after hafterEnvironment hafterOwner
    waited final hafter
  have hpool : waited.native.pool = (middle.native.pool.submit owner payload).2 := by
    simp only [playerStep, PlayerCommand.toAction, advance, step, FinDist.pure_bind,
      FinDist.mem_support_pure] at hsubmitted hwaited
    subst submitted
    subst waited
    rfl
  constructor
  · rw [hafterFrame.2.1, hpool]
    simp only [MessagePool.submit, if_pos, hbeforeFrame.2.1]
  · apply hafterFrame.2.2
    rw [hpool, ← hbeforeFrame.2.1]
    exact hmiddleSerials.lookup_submit owner _

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
  refine ⟨chosen, hchosen, app.runPolicies_submit_wait_branch_packet owner players environment
    before after hbeforeEnvironment hbeforeOwner hafterEnvironment hafterOwner execution final
    hserials (payload chosen) ?_⟩
  simp only [FinDist.support_bind, Set.mem_iUnion]
  exact ⟨middle, hmiddle, submitted, hsubmitted, waited, hwaited, hafter⟩

/-- An actual complete ordinary roster poll using an exact source law at one
submitter contains a concrete branch indexed by a supported source value. -/
theorem ordinary_submit_wait_support_value (app : MessageApplication Principal)
    {Choice : Type uChoice}
    (owner : Principal) (payload : Choice → app.Payload)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (roster beforeRoster afterRoster : List Principal)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (initial final : app.PolicyExecution) (kernel : FinDist Choice)
    (hownerLaw : ∀ middle,
      middle ∈ (app.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) initial).support →
      app.runPolicies players environment [.player owner, .player owner] middle =
        kernel.bind fun chosen =>
          (app.playerStep owner middle (.submit (payload chosen))).bind fun submitted =>
            app.playerStep owner submitted .wait)
    (hfinal : final ∈ (app.runPolicies players environment
      (roster.flatMap fun actor => [.player actor, .player actor]) initial).support) :
    ∃ chosen, chosen ∈ kernel.support ∧
      final ∈ ((app.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) initial).bind
          fun middle =>
            (app.playerStep owner middle (.submit (payload chosen))).bind fun submitted =>
              (app.playerStep owner submitted .wait).bind fun waited =>
                app.runPolicies players environment
                  (afterRoster.flatMap fun actor => [.player actor, .player actor])
                    waited).support := by
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let after := afterRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  have hschedule : roster.flatMap (fun actor => [Invocation.player actor, .player actor]) =
      (before ++ [.player owner, .player owner]) ++ after := by
    simp [hsplit, before, after, List.append_assoc]
  rw [hschedule, runPolicies_append] at hfinal
  simp only [FinDist.support_bind, Set.mem_iUnion] at hfinal
  obtain ⟨waited, hwaited, hafter⟩ := hfinal
  rw [runPolicies_append] at hwaited
  simp only [FinDist.support_bind, Set.mem_iUnion] at hwaited
  obtain ⟨middle, hmiddle, howner⟩ := hwaited
  rw [hownerLaw middle hmiddle] at howner
  simp only [FinDist.support_bind, Set.mem_iUnion] at howner
  obtain ⟨chosen, hchosen, submitted, hsubmitted, hwait⟩ := howner
  refine ⟨chosen, hchosen, ?_⟩
  simp only [FinDist.support_bind, Set.mem_iUnion]
  exact ⟨middle, hmiddle, submitted, hsubmitted, waited, hwait, hafter⟩

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.runPolicies_submit_wait_branch_packet'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_submit_wait_branch_packet

/-- info: 'Interaction.MessageApplication.runPolicies_submit_wait_packet'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.runPolicies_submit_wait_packet

/-- info: 'Interaction.MessageApplication.ordinary_submit_wait_support_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.ordinary_submit_wait_support_value
