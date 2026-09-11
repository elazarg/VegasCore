/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedBlockIsolation

/-! # Normal-service selection after actual ordinary polling -/

noncomputable section

namespace Vegas.ApplicationPlan.WindowedCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The first environment slot after ordinary polls selects the submitter's
retained latest envelope. This establishes selection, not acceptance. -/
theorem blockEnvironment_after_ordinary_polls
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
    {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
    {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
    {windowOf : Nat → Nat} {roster : List P} {focal owner : P}
    {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
    {blockIndex : Nat} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ} {plan : ApplicationPlan accounted fresh state}
    {profile : SourceBehavioralProfile prog}
    {current : CoupledAt (compileCore prog fresh state).graph state}
    {execution polled :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement blockIndex plan profile current execution)
    (instruction : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = instruction :: rest)
    (hsubmitter : instruction.submitter = some owner)
    (hpolled : polled ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap fun actor => [Invocation.player actor, .player actor]) execution).support)
    (hserial : polled.native.pool.nextSerial owner =
      execution.native.pool.nextSerial owner + 1)
    (message : Message P (ApplicationImage.Payload P L))
    (hlookup : polled.native.pool.lookup (owner, execution.native.pool.nextSerial owner) =
      some message) :
    (root.windowed deadlineOf binding choice windowOf).blockEnvironment roster
      polled.environmentHistory
      (State.environmentView (root.windowed deadlineOf binding choice windowOf).application
        polled.native) =
      FinDist.pure (.include (owner, execution.native.pool.nextSerial owner)) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf
    focal replacement
  let polls := roster.flatMap fun actor => [Invocation.player actor, .player actor]
  let decorated := (instruction.withBindingTimeouts binding).withChoiceTimeouts choice
  have hpublic := runtime.runPolicies_players_publicState players (runtime.blockEnvironment roster)
    polls (by simp [polls]) execution polled hpolled
  have hmemory : polled.native.application.base.memory =
      execution.native.application.base.memory := congrArg Prod.fst hpublic
  have hactive : runtime.image.activeAddress? polled.native.application.base.memory =
      some decorated.address := by
    rw [hmemory]
    simpa [decorated] using checkpoint.activeAddress?_head instruction rest hhead
  have hindexOriginal := checkpoint.instruction_at instruction rest hhead
  have hindex : runtime.image.instructions[blockIndex]? = some decorated := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, decorated]
  have hcount : polls.countP Invocation.isEnvironment = 0 := by
    apply List.countP_eq_zero.mpr
    intro invocation hmem
    cases invocation with
    | player actor => simp [Invocation.isEnvironment]
    | environment => simp [polls] at hmem
  have hlength : polled.environmentHistory.length = blockIndex * (roster.length + 2) := by
    rw [runtime.application.runPolicies_environmentHistory_length players
      (runtime.blockEnvironment roster) polls execution polled hpolled, hcount, Nat.add_zero]
    exact checkpoint.environmentHistory_length
  have hnormal := runtime.blockEnvironment_normal roster polled.environmentHistory
    (State.environmentView runtime.application polled.native) decorated
    (by rw [hlength, Nat.mul_div_cancel] <;> omega) hactive
    (by rw [hlength]; exact Nat.mul_mod_left _ _)
  rw [hnormal]
  cases instruction with
  | sample code =>
      exfalso
      change (none : Option P) = some owner at hsubmitter
      cases hsubmitter
  | bind code =>
      change some code.owner = some owner at hsubmitter
      have ho := Option.some.inj hsubmitter
      subst owner
      simp only [decorated, ApplicationInstruction.withBindingTimeouts,
        ApplicationInstruction.withChoiceTimeouts, ApplicationImage.serviceCommand,
        MessageApplication.latestSubmissionCommand, WindowedApplication.eraseEnvironmentView,
        State.environmentView]
      change FinDist.pure (runtime.liftEnvironmentCommand
        (match polled.native.pool.nextSerial code.owner with
        | 0 => .wait | serial + 1 => if (polled.native.pool.lookup (code.owner, serial)).isSome
          then .include (code.owner, serial) else .wait)) = _
      simp only [hserial, hlookup, Option.isSome_some, ↓reduceIte]
      rfl
  | publicChoice code =>
      change some code.endpoint.owner = some owner at hsubmitter
      have ho := Option.some.inj hsubmitter
      subst owner
      simp only [decorated, ApplicationInstruction.withBindingTimeouts,
        ApplicationInstruction.withChoiceTimeouts, ApplicationImage.serviceCommand,
        MessageApplication.latestSubmissionCommand, WindowedApplication.eraseEnvironmentView,
        State.environmentView]
      change FinDist.pure (runtime.liftEnvironmentCommand
        (match polled.native.pool.nextSerial code.endpoint.owner with
        | 0 => .wait | serial + 1 =>
          if (polled.native.pool.lookup (code.endpoint.owner, serial)).isSome
          then .include (code.endpoint.owner, serial) else .wait)) = _
      simp only [hserial, hlookup, Option.isSome_some, ↓reduceIte]
      rfl
  | conditional code =>
      change some code.endpoint.owner = some owner at hsubmitter
      have ho := Option.some.inj hsubmitter
      subst owner
      simp only [decorated, ApplicationInstruction.withBindingTimeouts,
        ApplicationInstruction.withChoiceTimeouts, ApplicationImage.serviceCommand,
        MessageApplication.latestSubmissionCommand, WindowedApplication.eraseEnvironmentView,
        State.environmentView]
      change FinDist.pure (runtime.liftEnvironmentCommand
        (match polled.native.pool.nextSerial code.endpoint.owner with
        | 0 => .wait | serial + 1 =>
          if (polled.native.pool.lookup (code.endpoint.owner, serial)).isSome
          then .include (code.endpoint.owner, serial) else .wait)) = _
      simp only [hserial, hlookup, Option.isSome_some, ↓reduceIte]
      rfl

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.blockEnvironment_after_ordinary_polls'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.blockEnvironment_after_ordinary_polls
