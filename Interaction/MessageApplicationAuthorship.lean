/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyInvariant
import Interaction.MessagePoolCounters

/-! # Authenticated message authorship -/

noncomputable section
namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]
variable (app : MessageApplication Principal)

/-- Payloads submitted by one authenticated principal, in allocation order. -/
def submittedPayloads (history : List app.PlayerEntry) : List app.Payload :=
  history.filterMap fun entry =>
    match entry.command with
    | .submit payload => some payload
    | _ => none

/-- Native sender counters and retained envelopes agree with authenticated
player-command histories. -/
def Authorship (execution : app.PolicyExecution) : Prop :=
  (∀ who, execution.native.pool.nextSerial who =
    (app.submittedPayloads (execution.principalHistory who)).length) ∧
  execution.native.pool.Satisfies fun message =>
    (app.submittedPayloads (execution.principalHistory message.id.1))[message.id.2]? =
      some message.payload

omit [DecidableEq Principal] in
@[simp] theorem submittedPayloads_append_privateCommand
    (history : List app.PlayerEntry) (view : app.View) (command : app.PrivateCommand) :
    app.submittedPayloads (history ++ [⟨view, .privateCommand command⟩]) =
      app.submittedPayloads history := by
  simp [submittedPayloads]

omit [DecidableEq Principal] in
@[simp] theorem submittedPayloads_append_submit
    (history : List app.PlayerEntry) (view : app.View) (payload : app.Payload) :
    app.submittedPayloads (history ++ [⟨view, .submit payload⟩]) =
      app.submittedPayloads history ++ [payload] := by
  simp [submittedPayloads]

omit [DecidableEq Principal] in
@[simp] theorem submittedPayloads_append_replay
    (history : List app.PlayerEntry) (view : app.View) (id : MessageId Principal) :
    app.submittedPayloads (history ++ [⟨view, .replay id⟩]) =
      app.submittedPayloads history := by
  simp [submittedPayloads]

omit [DecidableEq Principal] in
@[simp] theorem submittedPayloads_append_wait
    (history : List app.PlayerEntry) (view : app.View) :
    app.submittedPayloads (history ++ [⟨view, .wait⟩]) =
      app.submittedPayloads history := by
  simp [submittedPayloads]

omit [DecidableEq Principal] in
@[simp] theorem PolicyExecution.initial_authorship (application : app.Application) :
    app.Authorship (PolicyExecution.initial app (State.initial app application)) := by
  constructor
  · intro who; rfl
  · exact MessagePool.Satisfies.empty

theorem playerStep_authorship
    (who : Principal) (execution next : app.PolicyExecution) (command : app.PlayerCommand)
    (authorship : app.Authorship execution)
    (supported : next ∈ (app.playerStep who execution command).support) :
    app.Authorship next := by
  have historySelf := app.playerStep_history_self who execution command next supported
  have historyOther := fun other (hne : other ≠ who) =>
    app.playerStep_other_history who other hne execution command next supported
  have nativeMem : next.native ∈
      ((app.playerStep who execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [app.playerStep_native] at nativeMem
  rcases authorship with ⟨counters, messages⟩
  cases command with
  | privateCommand privateCommand =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at nativeMem
      unfold Authorship
      rw [nativeMem]
      refine ⟨?_, messages.mono ?_⟩
      · intro sender
        by_cases hsender : sender = who
        · subst sender
          simpa [historySelf] using counters who
        · simpa [historyOther sender hsender] using counters sender
      · intro message safe
        by_cases hsender : message.id.1 = who
        · subst who
          simpa [historySelf] using safe
        · simpa [historyOther message.id.1 hsender] using safe
  | submit payload =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at nativeMem
      unfold Authorship
      rw [nativeMem]
      refine ⟨?_, ?_⟩
      · intro sender
        by_cases hsender : sender = who
        · subst sender
          simp [MessagePool.submit, historySelf, counters who]
        · simpa [MessagePool.submit, hsender, historyOther sender hsender] using counters sender
      · have old := messages.mono (weaker := fun message =>
          (app.submittedPayloads (next.principalHistory message.id.1))[message.id.2]? =
            some message.payload)
          (by
          intro message safe
          by_cases hsender : message.id.1 = who
          · subst who
            rw [historySelf, app.submittedPayloads_append_submit,
              List.getElem?_append_left]
            · exact safe
            · by_contra outside
              have missing := List.getElem?_eq_none (Nat.le_of_not_gt outside)
              rw [missing] at safe
              contradiction
          · simpa [historyOther message.id.1 hsender] using safe)
        apply old.submit who payload
        simp [historySelf, counters who]
  | replay id =>
      simp only [PlayerCommand.toAction, step, FinDist.mem_support_pure] at nativeMem
      unfold Authorship
      rw [nativeMem]
      refine ⟨?_, (messages.replay who id).mono ?_⟩
      · intro sender
        by_cases hsender : sender = who
        · subst sender
          simpa [historySelf] using counters who
        · simpa [historyOther sender hsender] using counters sender
      · intro message safe
        by_cases hsender : message.id.1 = who
        · subst who
          simpa [historySelf] using safe
        · simpa [historyOther message.id.1 hsender] using safe
  | wait =>
      simp only [PlayerCommand.toAction, FinDist.mem_support_pure] at nativeMem
      unfold Authorship
      rw [nativeMem]
      refine ⟨?_, messages.mono ?_⟩
      · intro sender
        by_cases hsender : sender = who
        · subst sender
          simpa [historySelf] using counters who
        · simpa [historyOther sender hsender] using counters sender
      · intro message safe
        by_cases hsender : message.id.1 = who
        · subst who
          simpa [historySelf] using safe
        · simpa [historyOther message.id.1 hsender] using safe

theorem environmentStep_nextSerial
    (execution next : app.PolicyExecution) (command : app.EnvironmentPolicyCommand)
    (supported : next ∈ (app.environmentPolicyStep execution command).support) :
    ∀ who, next.native.pool.nextSerial who = execution.native.pool.nextSerial who := by
  have nativeMem : next.native ∈
      ((app.environmentPolicyStep execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [app.environmentStep_native] at nativeMem
  intro who
  cases command with
  | deliver observer id =>
      simp only [EnvironmentPolicyCommand.toAction, step,
        FinDist.mem_support_pure] at nativeMem
      rw [nativeMem]
      simp
  | «include» id =>
      simp only [EnvironmentPolicyCommand.toAction, step,
        FinDist.mem_support_pure] at nativeMem
      rw [nativeMem, includePending_pool]
      exact MessagePool.include_preserves_nextSerial _ _ _
  | application applicationCommand =>
      simp only [EnvironmentPolicyCommand.toAction, step, FinDist.support_map,
        Set.mem_image] at nativeMem
      obtain ⟨applicationNext, _, nativeEq⟩ := nativeMem
      rw [← nativeEq]
  | wait =>
      simp only [EnvironmentPolicyCommand.toAction, FinDist.mem_support_pure] at nativeMem
      rw [nativeMem]

theorem environmentStep_authorship
    (execution next : app.PolicyExecution) (command : app.EnvironmentPolicyCommand)
    (authorship : app.Authorship execution)
    (supported : next ∈ (app.environmentPolicyStep execution command).support) :
    app.Authorship next := by
  have history := app.environmentStep_principalHistory execution command next supported
  have pool := app.environmentPolicyStep_pool_satisfies
    (fun message =>
      (app.submittedPayloads (execution.principalHistory message.id.1))[message.id.2]? =
        some message.payload) execution next command authorship.2 supported
  have counters := app.environmentStep_nextSerial execution next command supported
  constructor
  · intro who
    rw [counters who, congrFun history who]
    exact authorship.1 who
  · apply pool.mono
    intro message safe
    rwa [congrFun history message.id.1]

/-- Authorship is preserved by arbitrary player and environment policies. -/
theorem runPolicies_authorship
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (execution next : app.PolicyExecution)
    (authorship : app.Authorship execution)
    (supported : next ∈ (app.runPolicies players environment schedule execution).support) :
    app.Authorship next := by
  apply app.runPolicies_execution_invariant (Authorship app) players environment
  · intro current who command after currentAuthorship _commandMem stepMem
    exact app.playerStep_authorship who current after command currentAuthorship stepMem
  · intro current command after currentAuthorship _commandMem stepMem
    exact app.environmentStep_authorship current after command currentAuthorship stepMem
  · exact authorship
  · exact supported

/-- Every actual policy run from an empty native pool has authenticated
counter/history and retained-message provenance. -/
theorem runPolicies_initial_authorship
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (state : app.Application)
    (next : app.PolicyExecution)
    (supported : next ∈ (app.runPolicies players environment schedule
      (PolicyExecution.initial app (State.initial app state))).support) :
    app.Authorship next := by
  exact app.runPolicies_authorship players environment schedule _ next
    (PolicyExecution.initial_authorship app _) supported

/-- Authenticated history fixes the payload at each identifier, so every
pending copy of that identifier has the same content. -/
theorem Authorship.lookup_eq_of_mem_pending
    (execution : app.PolicyExecution) (authorship : app.Authorship execution)
    (target : Message Principal app.Payload) (pending : target ∈ execution.native.pool.pending) :
    execution.native.pool.lookup target.id = some target := by
  unfold MessagePool.lookup
  let safe : Message Principal app.Payload → Prop := fun message =>
    (app.submittedPayloads (execution.principalHistory message.id.1))[message.id.2]? =
      some message.payload
  have findLaw : ∀ messages : List (Message Principal app.Payload),
      (∀ message, message ∈ messages → safe message) → target ∈ messages →
        messages.find? (fun message => message.id = target.id) = some target := by
    intro messages allSafe targetMem
    induction messages with
    | nil => contradiction
    | cons head tail ih =>
        simp only [List.find?_cons]
        split
        · rename_i same
          simp only [decide_eq_true_eq] at same
          have headSafe := allSafe head (by simp)
          have targetSafe := allSafe target targetMem
          unfold safe at headSafe targetSafe
          rw [same] at headSafe
          have payloadEq : head.payload = target.payload :=
            Option.some.inj (headSafe.symm.trans targetSafe)
          cases head
          cases target
          simp_all
        · rename_i different
          simp only [decide_eq_false_iff_not] at different
          apply ih
          · intro message member
            exact allSafe message (by simp [member])
          · apply (List.mem_cons.mp targetMem).resolve_left
            intro targetEq
            exact different (congrArg Message.id targetEq).symm
  exact findLaw execution.native.pool.pending authorship.2.1 pending

end Interaction.MessageApplication
