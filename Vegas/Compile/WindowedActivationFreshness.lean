/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockIsolation

/-! # Fresh activation origins after resolution -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every currently active obligation was activated at the state's current
public clock. This deliberately makes no claim about retained activations
after later clock advances. -/
def State.FreshActivation (state : WindowedApplication.State P L) : Prop :=
  ∀ activation ∈ state.active, activation.since = state.base.memory.clock

omit [DecidableEq P] in
theorem State.freshActivation_initial (runtime : WindowedApplication P L)
    (base : ApplicationImage.State P L) :
    (runtime.initial base).FreshActivation := by
  intro activation hactivation
  simp only [WindowedApplication.initial, Option.mem_map] at hactivation
  obtain ⟨address, _, rfl⟩ := hactivation
  rfl

/-- Every successful handler changes the active key and therefore refreshes
the successor origin to the successor state's exact public clock. -/
theorem handle_freshActivation (runtime : WindowedApplication P L)
    (before after : WindowedApplication.State P L)
    (message : Message P (ApplicationImage.Payload P L))
    (hhandle : runtime.handle before message = some after) :
    after.FreshActivation := by
  obtain ⟨activation, base, hactivation, hcurrent, hbase, rfl⟩ :=
    runtime.handle_some before after message hhandle
  obtain ⟨address, hbefore, _, hafter⟩ :=
    runtime.handle_resolves_active before (runtime.advanceTo before base) message hhandle
  have haddress : address = activation.key := by
    rw [hcurrent] at hbefore
    exact (Option.some.inj hbefore).symm
  have hnewInactive : runtime.image.activeAddress? base.memory ≠ some address := by
    simpa only [WindowedApplication.advanceTo] using hafter
  have hchanged : before.active.map Activation.key ≠
      runtime.image.activeAddress? base.memory := by
    rw [hactivation, Option.map_some]
    intro heq
    apply hnewInactive
    simpa only [haddress] using heq.symm
  rw [WindowedApplication.advanceTo, Activation.refresh_changed _ _ _ hchanged]
  intro nextActivation hnext
  simp only [Option.mem_map] at hnext
  obtain ⟨key, _, rfl⟩ := hnext
  rfl

omit [DecidableEq P] in
theorem State.FreshActivation.of_publicState_eq
    {first second : WindowedApplication.State P L}
    (hfirst : first.FreshActivation)
    (heq : (second.base.memory, second.active) = (first.base.memory, first.active)) :
    second.FreshActivation := by
  have hmemory : second.base.memory = first.base.memory := congrArg Prod.fst heq
  have hactive : second.active = first.active := congrArg Prod.snd heq
  intro activation hmem
  rw [hactive] at hmem
  rw [hmemory]
  exact hfirst activation hmem

/-- An address-aligned inactive block suffix preserves a fresh activation,
because the existing isolation theorem preserves both public memory and the
activation record exactly. -/
theorem runPolicies_block_inactive_freshActivation
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    (schedule : List (@Invocation P)) (execution next : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + schedule.countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (hinactive : runtime.image.activeAddress? execution.native.application.base.memory ≠
      some instruction.address)
    (hfresh : execution.native.application.FreshActivation)
    (hnext : next ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) schedule execution).support) :
    next.native.application.FreshActivation := by
  apply hfresh.of_publicState_eq
  exact runtime.runPolicies_block_inactive roster players schedule execution next instruction
    hindex hinactive hnext

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.handle_freshActivation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_freshActivation

/-- info: 'Vegas.WindowedApplication.runPolicies_block_inactive_freshActivation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_block_inactive_freshActivation
