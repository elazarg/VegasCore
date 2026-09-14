/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedResolution

/-! # Resolution frames and the pre-timeout protocol boundary

Clock resolution leaves the private commitment service unchanged. Before any
timeout, ordinary inclusion has exactly the untimed validator's event effect;
the additional scan only records public readiness timestamps. These are local
operational facts, not yet a whole-program coupling or a service theorem.
-/

namespace Interaction.SealedResolution

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}

@[simp] theorem PublicState.stamp_events (state : PublicState Principal Value) (node : Nat) :
    (state.stamp node).events = state.events := by
  unfold PublicState.stamp
  split <;> rfl

@[simp] theorem PublicState.stamp_timeouts (state : PublicState Principal Value) (node : Nat) :
    (state.stamp node).timeouts = state.timeouts := by
  unfold PublicState.stamp
  split <;> rfl

@[simp] theorem PublicState.stamp_clock (state : PublicState Principal Value) (node : Nat) :
    (state.stamp node).clock = state.clock := by
  unfold PublicState.stamp
  split <;> rfl

/-- Discharging timed-out prerequisites is exactly the same readiness test as
checking the resolution state's combined event-or-timeout completion flag. -/
@[simp] theorem PublicState.prerequisitesDone_discharge
    (state : PublicState Principal Value) (rule : SealedRule Principal) :
    SealedProgram.prerequisitesDone state.events (rule.discharge state.timeouts) =
      rule.requires.all state.completed := by
  cases rule with
  | mk kind requires =>
      change (requires.filter fun node => !state.timeouts.contains node).all
          (SealedProgram.done state.events) =
        requires.all fun node =>
          SealedProgram.done state.events node || state.timeouts.contains node
      induction requires with
      | nil => rfl
      | cons node rest ih =>
          cases hcontains : state.timeouts.contains node with
          | false =>
              simp only [List.filter_cons, hcontains, Bool.not_false,
                if_true, List.all_cons, Bool.or_false, ih]
          | true =>
              simp only [List.filter_cons, hcontains, Bool.not_true,
                Bool.false_eq_true, if_false, List.all_cons, Bool.or_true,
                Bool.true_and, ih]

theorem visit_clock (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) (node : Nat) :
    (runtime.visit resolveExpired state node).clock = state.clock := by
  unfold visit
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · dsimp only
        split
        · exact state.stamp_clock node
        · split <;> simp_all [expire]
      · dsimp only
        split <;> simp_all [expire]

theorem visit_false_timeouts (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) (node : Nat) :
    (runtime.visit false state node).timeouts = state.timeouts := by
  unfold visit
  split
  · rfl
  · split
    · rfl
    · split <;> simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      · split <;> simp
      · exact state.stamp_timeouts node

theorem visit_false_events (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) (node : Nat) (hclear : state.timeouts = []) :
    (runtime.visit false state node).events = state.events := by
  unfold visit
  split
  · rfl
  · split
    · rfl
    · split <;> simp [hclear]

theorem refresh_clock (runtime : SealedResolution Principal Value) (resolveExpired : Bool)
    (state : PublicState Principal Value) :
    (runtime.refresh resolveExpired state).clock = state.clock := by
  unfold refresh
  generalize List.range runtime.program.rules.length = nodes
  induction nodes generalizing state with
  | nil => rfl
  | cons node rest ih =>
      exact (ih (runtime.visit resolveExpired state node)).trans
        (runtime.visit_clock resolveExpired state node)

theorem refresh_false_timeouts (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) :
    (runtime.refresh false state).timeouts = state.timeouts := by
  unfold refresh
  generalize List.range runtime.program.rules.length = nodes
  induction nodes generalizing state with
  | nil => rfl
  | cons node rest ih =>
      exact (ih (runtime.visit false state node)).trans (runtime.visit_false_timeouts state node)

theorem refresh_false_events (runtime : SealedResolution Principal Value)
    (state : PublicState Principal Value) (hclear : state.timeouts = []) :
    (runtime.refresh false state).events = state.events := by
  unfold refresh
  generalize List.range runtime.program.rules.length = nodes
  induction nodes generalizing state with
  | nil => rfl
  | cons node rest ih =>
      have hnext := (runtime.visit_false_timeouts state node).trans hclear
      exact (ih (runtime.visit false state node) hnext).trans
        (runtime.visit_false_events state node hclear)

@[simp] theorem tick_service (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value) :
    (runtime.tick state).service = state.service := rfl

@[simp] theorem tick_clock (runtime : SealedResolution Principal Value)
    (state : ApplicationState Principal Value) :
    (runtime.tick state).visible.clock = state.visible.clock + 1 :=
  runtime.refresh_clock true _

theorem validateMessage?_no_timeout [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value) (state : ApplicationState Principal Value)
    (hclear : state.visible.timeouts = [])
    (message : Message Principal (SealedProgram.Payload Principal Value)) :
    runtime.validateMessage? state message =
      runtime.program.validateMessage? state.service state.visible.events message := by
  cases message with
  | mk id payload => cases payload <;> simp [validateMessage?, SealedProgram.Payload.node?, hclear]

/-- No protocol traffic can reopen an expired node, regardless of its payload,
the owner's later registration, or the current private service. -/
theorem validateMessage?_expired [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value) (state : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value)) (node : Nat)
    (hnode : message.payload.node? = some node) (hexpired : node ∈ state.visible.timeouts) :
    runtime.validateMessage? state message = none := by
  simp [validateMessage?, hnode, hexpired]

theorem handle_service [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (state next : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.handle state message = some next) : next.service = state.service := by
  unfold handle at hnext
  cases hvalid : runtime.validateMessage? state message <;> simp [hvalid] at hnext
  subst next
  rfl

theorem handle_clock [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (state next : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.handle state message = some next) :
    next.visible.clock = state.visible.clock := by
  unfold handle at hnext
  cases hvalid : runtime.validateMessage? state message with
  | none => simp only [hvalid, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hnext
  | some event =>
      simp only [hvalid, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
      subst next
      exact runtime.refresh_clock false _

/-- Inclusion retains all existing timeout records and creates no new one. -/
theorem handle_timeouts [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value)
    (state next : ApplicationState Principal Value)
    (message : Message Principal (SealedProgram.Payload Principal Value))
    (hnext : runtime.handle state message = some next) :
    next.visible.timeouts = state.visible.timeouts := by
  unfold handle at hnext
  cases hvalid : runtime.validateMessage? state message with
  | none => simp only [hvalid, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at hnext
  | some event =>
      simp only [hvalid, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at hnext
      subst next
      exact runtime.refresh_false_timeouts _

/-- With no previous timeout, erasing clock and readiness data from an accepted
inclusion gives precisely the original sealed validator's event update. -/
theorem handle_no_timeout [DecidableEq Principal] [DecidableEq Value]
    (runtime : SealedResolution Principal Value) (state : ApplicationState Principal Value)
    (hclear : state.visible.timeouts = [])
    (message : Message Principal (SealedProgram.Payload Principal Value)) :
    (runtime.handle state message).map
        (fun next => (next.service, next.visible.events, next.visible.timeouts)) =
      (runtime.program.validateMessage? state.service state.visible.events message).map
        (fun event => (state.service, state.visible.events ++ [event], [])) := by
  unfold handle
  rw [runtime.validateMessage?_no_timeout state hclear message]
  cases runtime.program.validateMessage? state.service state.visible.events message with
  | none => rfl
  | some event =>
      let recorded := { state.visible with events := state.visible.events ++ [event] }
      change some (state.service, (runtime.refresh false recorded).events,
        (runtime.refresh false recorded).timeouts) =
          some (state.service, state.visible.events ++ [event], [])
      rw [runtime.refresh_false_events recorded hclear, runtime.refresh_false_timeouts]
      exact congrArg some (by simp [recorded, hclear])

end Interaction.SealedResolution
