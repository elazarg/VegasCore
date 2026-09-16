/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.DeviationServiceSafety
import Vegas.Pending.ContinuationWire

/-! # Continuations for one arbitrary native player

The focal player's native cache and authenticated command history are not
interpreted as graph choices.  An extracted graph policy supplies those
choices; its own-action argument is erased.  Every nonfocal history remains
the actual initialized execution history. -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- A graph policy ignores its owner's accumulated action list at every
decision node.  The observation remains an input: this is exactly the
factorization needed for an extracted unilateral policy, not an
information-free policy. -/
def PolicyIgnoresOwnHistory (who : Player) :
    {Γ Δ : VCtx Player L} → (graph : Graph Player L Γ Δ) →
      BehavioralPolicy who graph → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample _ _ _ next, policy => PolicyIgnoresOwnHistory who next policy
  | _, _, .bind _ _ _ next, policy =>
      (∀ owned observation left right,
        policy.1 owned (observation, left) = policy.1 owned (observation, right)) ∧
      PolicyIgnoresOwnHistory who next policy.2
  | _, _, .resolve _ _ _ _ _ _ next, policy =>
      (∀ owned observation left right,
        policy.1 owned (observation, left) = policy.1 owned (observation, right)) ∧
      PolicyIgnoresOwnHistory who next policy.2

/-- The focal component of a behavioral profile factors through its current
graph observation and does not inspect its own logical-action history. -/
def IgnoresOwnHistory (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (focal : Player) : Prop :=
  PolicyIgnoresOwnHistory focal whole (profile focal)

/-- History independence is retained when a typed graph prefix selects the
residual policy. -/
theorem Prefix.policyTail_ignoresOwnHistory {whole : Graph Player L Γ₀ Δ}
    {suffix : Graph Player L Γ Δ} {length : Nat}
    (walk : Prefix Δ whole suffix length) (profile : BehavioralProfile whole)
    (focal : Player) (independent : IgnoresOwnHistory whole profile focal) :
    PolicyIgnoresOwnHistory focal suffix ((walk.profileTail profile) focal) := by
  change PolicyIgnoresOwnHistory focal suffix
    (walk.policyTail focal (profile focal))
  induction walk with
  | refl => exact independent
  | sample walk ih => exact ih (fun who => profile who) independent
  | bind walk ih => exact ih (fun who => (profile who).2) independent.2
  | resolve walk ih => exact ih (fun who => (profile who).2) independent.2

def eraseFocalHistory {runtime : GraphRuntime Player L Δ} (focal : Player)
    (histories : Player → List (Entry runtime)) :
    Player → List (Entry runtime) := fun who => if who = focal then [] else histories who

def eraseFocalLogical (focal : Player) (logical : History Player L) : History Player L :=
  fun who => if who = focal then [] else logical who

/-- The proof-side execution used to invoke a nonfocal compiled policy.  Its
native state, environment transcript, and native trace are unchanged. -/
def eraseFocalExecution (runtime : GraphRuntime Player L Δ) (focal : Player)
    (execution : runtime.application.PolicyExecution) :
    runtime.application.PolicyExecution :=
  { execution with principalHistory := eraseFocalHistory focal execution.principalHistory }

@[simp] theorem eraseFocalExecution_native (runtime : GraphRuntime Player L Δ)
    (focal : Player) (execution : runtime.application.PolicyExecution) :
    (eraseFocalExecution runtime focal execution).native = execution.native := rfl

@[simp] theorem eraseFocalExecution_history_of_ne (runtime : GraphRuntime Player L Δ)
    (focal actor : Player) (different : actor ≠ focal)
    (execution : runtime.application.PolicyExecution) :
    (eraseFocalExecution runtime focal execution).principalHistory actor =
      execution.principalHistory actor := by
  simp [eraseFocalExecution, eraseFocalHistory, different]

/-- Erasing the focal transcript commutes with a different player's concrete
command step. -/
theorem playerStep_eraseFocalExecution_of_ne (runtime : GraphRuntime Player L Δ)
    (focal actor : Player) (different : actor ≠ focal)
    (execution : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand) :
    (runtime.application.playerStep actor execution command).map
        (eraseFocalExecution runtime focal) =
      runtime.application.playerStep actor
        (eraseFocalExecution runtime focal execution) command := by
  cases execution with
  | mk native principalHistory environmentHistory nativeTrace =>
    simp only [MessageApplication.playerStep, FinDist.map_bind]
    apply FinDist.bind_congr
    intro advanced _
    simp only [FinDist.map_pure]
    congr 1
    simp only [eraseFocalExecution]
    congr 1
    funext other
    by_cases otherFocal : other = focal
    · subst other
      simp [eraseFocalHistory, Ne.symm different]
    · by_cases otherActor : other = actor
      · subst other
        simp [eraseFocalHistory, different]
      · simp [eraseFocalHistory, otherFocal, otherActor]

/-- Consequently, invoking a nonfocal policy and then erasing the focal
transcript is the same law as invoking that policy from the erased execution. -/
theorem invoke_eraseFocalExecution_of_ne (runtime : GraphRuntime Player L Δ)
    (focal actor : Player) (different : actor ≠ focal)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution : runtime.application.PolicyExecution) :
    (runtime.application.invoke players environment execution (.player actor)).map
        (eraseFocalExecution runtime focal) =
      runtime.application.invoke players environment
        (eraseFocalExecution runtime focal execution) (.player actor) := by
  simp only [MessageApplication.invoke, FinDist.map_bind]
  rw [eraseFocalExecution_history_of_ne runtime focal actor different execution]
  apply FinDist.bind_congr
  intro command _
  exact runtime.playerStep_eraseFocalExecution_of_ne focal actor different execution command

/-- Residual graph law for a unilateral native deviation.  Focal cache markers
and focal own-action history are deliberately absent from its interpretation. -/
def deviationContinuationAt (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (focal : Player) (histories : Player → List (Entry runtime)) :
    (state : State Player L Δ) → state.Follows whole 0 → FinDist (VEnv L Δ)
  | .running suffix ideal _values _bindings _candidates site _clock _enteredAt, follows =>
      let walk := Classical.choice (State.prefix_of_running_follows whole suffix
        ideal _values _bindings _candidates site _clock _enteredAt follows)
      continuation runtime suffix (walk.profileTail profile) site ideal
        (eraseFocalLogical focal (fun who => projectLogicalHistory who (observe who ideal)
          (histories who) whole 0 site))
        (eraseFocalHistory focal histories)

/-- At a typed cursor the deviation continuation exposes the supplied prefix,
just like `continuationAt_running`, with only focal bookkeeping erased. -/
theorem deviationContinuationAt_running (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (focal : Player) (execution : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows whole 0)
    (suffix : Graph Player L Γ Δ) (site : Nat) (walk : Prefix Δ whole suffix site)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (atCursor : execution.native.application =
      .running suffix ideal values bindings candidates site clock enteredAt) :
    deviationContinuationAt runtime whole profile focal execution.principalHistory
        execution.native.application follows =
      continuation runtime suffix (walk.profileTail profile) site ideal
        (eraseFocalLogical focal (fun who => projectLogicalHistory who (observe who ideal)
          (execution.principalHistory who) whole 0 site))
        (eraseFocalHistory focal execution.principalHistory) := by
  generalize stateEq : execution.native.application = state at follows ⊢
  have same : state = .running suffix ideal values bindings candidates site clock enteredAt :=
    stateEq.symm.trans atCursor
  clear stateEq atCursor
  subst state
  simp only [deviationContinuationAt]
  congr 2
  exact Subsingleton.elim _ walk

/-- A focal history update is invisible to the deviation continuation's cache
and logical-history inputs. -/
@[simp] theorem eraseFocalHistory_update_self (focal : Player)
    {runtime : GraphRuntime Player L Δ} (histories : Player → List (Entry runtime))
    (history : List (Entry runtime)) :
    eraseFocalHistory focal (Function.update histories focal history) =
      eraseFocalHistory focal histories := by
  funext who
  by_cases same : who = focal
  · subst who
    simp [eraseFocalHistory]
  · simp [eraseFocalHistory, Function.update, same]

/-- Nonfocal histories are retained exactly. -/
theorem eraseFocalHistory_of_ne (focal who : Player) (different : who ≠ focal)
    {runtime : GraphRuntime Player L Δ} (histories : Player → List (Entry runtime)) :
    eraseFocalHistory focal histories who = histories who := by
  simp [eraseFocalHistory, different]

/-- An arbitrary focal-player invocation preserves the sanitized residual law.
No assumption is made on the focal native policy: its newly recorded command
and any private candidate preparation are erased, while every nonfocal history
and every graph-semantic field remain unchanged. -/
theorem deviationContinuationAt_focal_player_invoke
    (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (profile : BehavioralProfile whole)
    (focal : Player) (execution : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows whole 0)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) :
    deviationContinuationAt runtime whole profile focal execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke players environment execution (.player focal)).bindOnSupport
        fun after supported => deviationContinuationAt runtime whole profile focal
          after.principalHistory after.native.application
          (runtime.invoke_follows whole 0 players environment (.player focal)
            execution after follows supported) := by
  obtain ⟨target, suffix, site, ideal, values, bindings, candidates, clock, enteredAt,
      walk, atCursor⟩ := (show execution.native.application.Follows whole 0 from follows)
  simp only [Nat.zero_add] at atCursor
  rw [runtime.deviationContinuationAt_running whole profile focal execution follows
    suffix site walk ideal values bindings candidates clock enteredAt atCursor]
  symm
  apply (FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun _ => continuation runtime suffix (walk.profileTail profile) site ideal
      (eraseFocalLogical focal (fun who => projectLogicalHistory who (observe who ideal)
        (execution.principalHistory who) whole 0 site))
      (eraseFocalHistory focal execution.principalHistory)) ?_).trans
    (FinDist.bind_const _ _)
  intro after supported
  have stepSupport := supported
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at stepSupport
  obtain ⟨command, _commandMem, stepMem⟩ := stepSupport
  have phase := runtime.playerStep_phase focal execution after command stepMem
  rw [atCursor] at phase
  have runMem : after ∈ (runtime.application.runPolicies players environment
      [.player focal] execution).support := by
    simpa [MessageApplication.runPolicies] using supported
  obtain ⟨candidates', clock', enteredAt', atNext⟩ :=
    runtime.runPolicies_running_eq_of_phase_eq suffix ideal values bindings candidates
      site clock enteredAt players environment [.player focal] execution after
      atCursor runMem phase
  rw [runtime.deviationContinuationAt_running whole profile focal after _ suffix site walk
    ideal values bindings candidates' clock' enteredAt' atNext]
  have histories : eraseFocalHistory focal after.principalHistory =
      eraseFocalHistory focal execution.principalHistory := by
    funext who
    by_cases same : who = focal
    · subst who
      simp [eraseFocalHistory]
    · rw [eraseFocalHistory_of_ne focal who same,
        eraseFocalHistory_of_ne focal who same]
      exact runtime.application.playerStep_other_history focal who same execution command
        after stepMem
  have logical : eraseFocalLogical focal (fun who =>
        projectLogicalHistory who (observe who ideal) (after.principalHistory who)
          whole 0 site) =
      eraseFocalLogical focal (fun who =>
        projectLogicalHistory who (observe who ideal) (execution.principalHistory who)
          whole 0 site) := by
    funext who
    by_cases same : who = focal
    · subst who
      simp [eraseFocalLogical]
    · rw [show eraseFocalLogical focal (fun who =>
          projectLogicalHistory who (observe who ideal) (after.principalHistory who)
            whole 0 site) who =
          projectLogicalHistory who (observe who ideal) (after.principalHistory who)
            whole 0 site by simp [eraseFocalLogical, same]]
      rw [show eraseFocalLogical focal (fun who =>
          projectLogicalHistory who (observe who ideal) (execution.principalHistory who)
            whole 0 site) who =
          projectLogicalHistory who (observe who ideal) (execution.principalHistory who)
            whole 0 site by simp [eraseFocalLogical, same]]
      rw [runtime.application.playerStep_other_history focal who same execution command
        after stepMem]
  rw [histories, logical]

end Vegas.GraphRuntime
