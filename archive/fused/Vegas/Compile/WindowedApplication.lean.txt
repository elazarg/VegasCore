/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.Activation
import Vegas.Compile.ApplicationDeadlines
import Vegas.Compile.ApplicationImageClock
import Interaction.MessageApplicationPolicyLaws

/-! # Activation-relative ordered applications

This runtime instance measures each response window from the instruction's
activation. It explicitly replaces the image's absolute timing policy; guards,
fallback expressions, and the availability of fallback handlers are retained.
The original absolute-deadline application remains a separate instance.

Activation metadata is public. Private preparation, message submission,
delivery, rejection, replay, and clock advancement do not restart a window.
Actual resolution activates the next emitted instruction immediately. The
shared runner still supplies all message-pool operations and policy histories.
Neither clock progress nor delivery nor an expiry-producing service is assumed
or supplied here. Enriched observations require an explicit policy comparison.
-/

noncomputable section

namespace Vegas

open EventGraph Interaction GameTheory.Math.Probability

/-- An ordered application with explicitly supplied response durations.
Existing absolute deadlines are superseded, not interpreted as durations. -/
structure WindowedApplication (P : Type) (L : IExpr) where
  image : ApplicationImage P L
  windowOf : Nat → Nat

namespace WindowedApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Application state and publicly observable activation metadata. -/
structure State (P : Type) (L : IExpr) where
  base : ApplicationImage.State P L
  active : Option (Activation Nat)

def initial (runtime : WindowedApplication P L)
    (base : ApplicationImage.State P L) : State P L :=
  ⟨base, (runtime.image.activeAddress? base.memory).map (⟨·, base.memory.clock⟩)⟩

/-- Record a new origin exactly when the active address changes. Generated
instruction addresses are unique; aliases are excluded by compiler coverage. -/
def advanceTo (runtime : WindowedApplication P L) (state : State P L)
    (next : ApplicationImage.State P L) : State P L :=
  ⟨next, Activation.refresh state.active (runtime.image.activeAddress? next.memory)
    next.memory.clock⟩

/-- A stable activation chooses an absolute-deadline image for this call.
Ordered admission makes the assigned deadlines at other addresses irrelevant. -/
def atOrigin (runtime : WindowedApplication P L) (origin : Nat) : ApplicationImage P L :=
  runtime.image.withDeadlines (fun address => origin + runtime.windowOf address)

/-- Inconsistent activation metadata fails closed. Successful handling uses
the original validator and first-resolution semantics at a stable deadline. -/
def handle (runtime : WindowedApplication P L) (state : State P L)
    (message : Message P (ApplicationImage.Payload P L)) : Option (State P L) := do
  let activation ← state.active
  if runtime.image.activeAddress? state.base.memory = some activation.key then
    let next ← (runtime.atOrigin activation.since).orderedApplication.handle state.base message
    pure (runtime.advanceTo state next)
  else none

def environmentStep (runtime : WindowedApplication P L) (state : State P L) :
    ApplicationImage.EnvironmentCommand → FinDist (State P L)
  | .advance clock => FinDist.pure { state with base := state.base.advance clock }
  | .sample address =>
      (runtime.image.orderedApplication.environmentStep state.base (.sample address)).map
        (runtime.advanceTo state)

/-- The shared message interpreter, with activation included in both public
views. The raw payload and command alphabets are unchanged. -/
def application (runtime : WindowedApplication P L) : MessageApplication P where
  Application := State P L
  Payload := ApplicationImage.Payload P L
  PrivateCommand := ApplicationImage.PrivateCommand L
  EnvironmentCommand := ApplicationImage.EnvironmentCommand
  PlayerView := ApplicationImage.Memory P L × Option (Activation Nat)
  EnvironmentView := ApplicationImage.Memory P L × Option (Activation Nat)
  privateStep state who command := match command with
    | .register slot value => { state with base := state.base.register who slot value }
  environmentStep := runtime.environmentStep
  handle := runtime.handle
  observePlayer state _ := (state.base.memory, state.active)
  observeEnvironment state := (state.base.memory, state.active)

@[simp] theorem application_advance (runtime : WindowedApplication P L)
    (state : State P L) (clock : Nat) :
    runtime.application.environmentStep state (.advance clock) =
      FinDist.pure { state with base := state.base.advance clock } := rfl

/-- The tracked obligation is exactly the public active address, and its
origin is bounded by the current public clock. -/
def Consistent (runtime : WindowedApplication P L) (state : State P L) : Prop :=
  state.active.map Activation.key = runtime.image.activeAddress? state.base.memory ∧
    ∀ activation ∈ state.active, activation.since ≤ state.base.memory.clock

omit [DecidableEq P] in
theorem initial_consistent (runtime : WindowedApplication P L)
    (base : ApplicationImage.State P L) : runtime.Consistent (runtime.initial base) := by
  cases hactive : runtime.image.activeAddress? base.memory <;>
    simp [Consistent, initial, hactive]

omit [DecidableEq P] in
theorem advanceTo_consistent (runtime : WindowedApplication P L) (state : State P L)
    (next : ApplicationImage.State P L) (hstate : runtime.Consistent state)
    (hclock : state.base.memory.clock ≤ next.memory.clock) :
    runtime.Consistent (runtime.advanceTo state next) := by
  refine ⟨Activation.refresh_key _ _ _, ?_⟩
  exact Activation.refresh_since_le _ _ _
    (fun activation hactivation => Nat.le_trans (hstate.2 activation hactivation) hclock)

omit [DecidableEq P] in
/-- Administrative changes and rejected/stuttering effects cannot restart a
consistent active window. -/
theorem advanceTo_same_address (runtime : WindowedApplication P L) (state : State P L)
    (next : ApplicationImage.State P L) (hstate : runtime.Consistent state)
    (hsame : runtime.image.activeAddress? next.memory =
      runtime.image.activeAddress? state.base.memory) :
    (runtime.advanceTo state next).active = state.active := by
  exact Activation.refresh_unchanged _ _ _ (hstate.1.trans hsame.symm)

omit [DecidableEq P] in
/-- A newly active instruction gets the successor state's public clock,
independently of time spent at earlier instructions. -/
theorem advanceTo_new_address (runtime : WindowedApplication P L) (state : State P L)
    (next : ApplicationImage.State P L) (hstate : runtime.Consistent state)
    (hchanged : runtime.image.activeAddress? state.base.memory ≠
      runtime.image.activeAddress? next.memory) :
    (runtime.advanceTo state next).active =
      (runtime.image.activeAddress? next.memory).map (⟨·, next.memory.clock⟩) := by
  apply Activation.refresh_changed
  rwa [hstate.1]

/-- Successful relative-time handling is an actual ordered handler call with
the activation-derived absolute deadline; the resulting state is then tracked. -/
theorem handle_some (runtime : WindowedApplication P L) (state next : State P L)
    (message : Message P (ApplicationImage.Payload P L))
    (hnext : runtime.handle state message = some next) :
    ∃ activation base,
      state.active = some activation ∧
      runtime.image.activeAddress? state.base.memory = some activation.key ∧
      (runtime.atOrigin activation.since).orderedApplication.handle state.base message =
        some base ∧ next = runtime.advanceTo state base := by
  unfold handle at hnext
  cases hactive : state.active with
  | none => simp [hactive] at hnext
  | some activation =>
      simp only [hactive, Option.bind_eq_bind, Option.bind_some] at hnext
      split at hnext
      · rename_i hcurrent
        cases hbase : (runtime.atOrigin activation.since).orderedApplication.handle
            state.base message with
        | none => simp [hbase] at hnext
        | some base =>
            simp only [hbase, Option.bind_some, Option.pure_def, Option.some.injEq] at hnext
            exact ⟨activation, base, rfl, hcurrent, hbase, hnext.symm⟩
      · contradiction

theorem handle_consistent (runtime : WindowedApplication P L) (state next : State P L)
    (message : Message P (ApplicationImage.Payload P L))
    (hstate : runtime.Consistent state)
    (hnext : runtime.handle state message = some next) : runtime.Consistent next := by
  obtain ⟨activation, base, _, _, hbase, rfl⟩ := runtime.handle_some state next message hnext
  apply runtime.advanceTo_consistent state base hstate
  exact Nat.le_of_eq
    ((runtime.atOrigin activation.since).ordered_handle_clock state.base base message hbase).symm

theorem environmentStep_consistent (runtime : WindowedApplication P L)
    (state next : State P L) (command : ApplicationImage.EnvironmentCommand)
    (hstate : runtime.Consistent state)
    (hnext : next ∈ (runtime.environmentStep state command).support) :
    runtime.Consistent next := by
  cases command with
  | advance clock =>
      rw [environmentStep, FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨hstate.1, fun activation hactivation =>
        Nat.le_trans (hstate.2 activation hactivation) (Nat.le_max_left _ _)⟩
  | sample address =>
      simp only [environmentStep, FinDist.support_map, Set.mem_image] at hnext
      obtain ⟨base, hbase, rfl⟩ := hnext
      exact runtime.advanceTo_consistent state base hstate
        (runtime.image.ordered_environmentStep_clock_mono state.base base (.sample address) hbase)

/-- Every supported policy run preserves the public activation invariant.
The players, environment, and invocation schedule are unrestricted. -/
theorem runPolicies_consistent (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (state next : runtime.application.PolicyExecution)
    (hstate : runtime.Consistent state.native.application)
    (hnext : next ∈ (runtime.application.runPolicies players environment schedule state).support) :
    runtime.Consistent next.native.application := by
  exact runtime.application.runPolicies_application_invariant runtime.Consistent
    (fun state who command h => by cases command; exact h)
    (fun state message next h hnext => runtime.handle_consistent state next message h hnext)
    (fun state command next h hnext =>
      runtime.environmentStep_consistent state next command h hnext)
    players environment schedule state next hstate hnext

end WindowedApplication

end Vegas

/-- info: 'Vegas.WindowedApplication.runPolicies_consistent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_consistent
