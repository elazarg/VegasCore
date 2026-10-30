/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveDefaultCompletion

/-! # Native information fibers before public default

A deciding input is clear precisely when its displayed whole default set is
empty. Equal actual observations retain the complete public default history,
so every history in a clear information fiber is clear. These are properties
of the sole native application and its ordinary response-menu restrictions.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- A deciding native input displays an empty whole public default set. -/
def ClearInput (input : (runtime.reactiveApplication leaks).Info) : Prop :=
  ∃ past view, input = some (past, view) ∧
    view.application.publicView.observation.defaulted = ∅

/-- Only the deciding player receives a clear input, and its clearance is
exactly that of the actual native configuration. -/
theorem clearInput_observe_iff (who : Player)
    (state : (runtime.reactiveApplication leaks).ProtocolState) :
    runtime.ClearInput leaks ((runtime.reactiveApplication leaks).observe who state) ↔
      (runtime.reactiveApplication leaks).actor state = some who ∧
        ∀ control, state = some control → control.execution.application.config.defaulted = ∅ := by
  cases state with
  | none => simp [ClearInput, ReactiveApplication.observe, ReactiveApplication.actor]
  | some control =>
      by_cases active : control.actor = some who
      · have defaults : (control.execution.observe (runtime.reactiveApplication leaks)
            who).application.publicView.observation.defaulted =
          control.execution.application.config.defaulted := rfl
        simp [ClearInput, ReactiveApplication.observe, ReactiveApplication.actor, active, defaults]
      · simp [ClearInput, ReactiveApplication.observe, ReactiveApplication.actor, active]

/-- At deciding inputs, clearance and public default are complementary. Inactive
inputs belong to neither region. -/
theorem clearInput_iff_not_publicDefaultInput
    (input : (runtime.reactiveApplication leaks).Info) (deciding : input.isSome) :
    runtime.ClearInput leaks input ↔ ¬ runtime.PublicDefaultInput leaks input := by
  cases input with
  | none => cases deciding
  | some input =>
      rcases input with ⟨past, view⟩
      simp [ClearInput, PublicDefaultInput]

/-- Equal actual observations at a decision retain the entire default history,
including the positions of silent automatic completions. -/
theorem informationFiber_defaults (who : Player)
    (reference : (runtime.reactiveApplication leaks).Control)
    (active : reference.actor = some who)
    (state : (runtime.reactiveApplication leaks).ProtocolState)
    (same : (runtime.reactiveApplication leaks).observe who state =
      (runtime.reactiveApplication leaks).observe who (some reference)) :
    ∀ current, state = some current →
      current.execution.application.config.defaults =
        reference.execution.application.config.defaults := by
  intro current currentEq
  rw [currentEq] at same
  simp only [ReactiveApplication.observe, active, ↓reduceIte] at same
  split at same
  · have records := congrArg
      (fun input => input.2.application.publicView.observation.defaults) (Option.some.inj same)
    exact records
  · cases same

/-- Every control with the same deciding observation as a clear reference has
an empty whole public default set. No receipt or initialization premise is needed. -/
theorem informationFiber_clear (who : Player)
    (reference : (runtime.reactiveApplication leaks).Control)
    (active : reference.actor = some who)
    (clear : reference.execution.application.config.defaulted = ∅)
    (state : (runtime.reactiveApplication leaks).ProtocolState)
    (same : (runtime.reactiveApplication leaks).observe who state =
      (runtime.reactiveApplication leaks).observe who (some reference)) :
    ∀ current, state = some current → current.execution.application.config.defaulted = ∅ := by
  intro current currentEq
  have records := runtime.informationFiber_defaults leaks who reference active state same
    current currentEq
  have defaults := congrArg DefaultHistory.defaulted records
  exact defaults.trans clear

variable (menu : (runtime.reactiveApplication leaks).ResponseMenu)
  (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
  (scheduler : (runtime.reactiveApplication leaks).Scheduler)

local notation "N" => menu.information initial horizon scheduler
local notation "E" => menu.protocol initial horizon scheduler

/-- Every history in a clear decision-information fiber has an empty whole
native default set, including histories with zero assessment probability. -/
theorem informationHistory_clear {who : Player} (site : (N).InformationSite who)
    (clear : runtime.ClearInput leaks site.1)
    (history : (N).InformationHistory who site.1) :
    ∀ current, history.1.state = some current →
      current.execution.application.config.defaulted = ∅ := by
  have observed := (menu.info initial horizon scheduler who history.1.trace).symm.trans
    history.2
  have actual := observed ▸ clear
  exact ((runtime.clearInput_observe_iff leaks who history.1.state).mp actual).2

/-- A complete information fiber retains the reference's exact public default
history, independently of which history an assessment supports. -/
theorem informationHistory_defaults {who : Player} (site : (N).InformationSite who)
    (reference : (runtime.reactiveApplication leaks).Control)
    (active : reference.actor = some who)
    (atSite : site.1 = (runtime.reactiveApplication leaks).observe who (some reference))
    (history : (N).InformationHistory who site.1) :
    ∀ current, history.1.state = some current →
      current.execution.application.config.defaults =
        reference.execution.application.config.defaults := by
  have observed := (menu.info initial horizon scheduler who history.1.trace).symm.trans
    (history.2.trans atSite)
  exact runtime.informationFiber_defaults leaks who reference active history.1.state observed

/-- Clearance at a later legal native history implies clearance at every
preceding history; public default cannot disappear along the path. -/
theorem clear_before_reaches {first last : (E).History}
    (reached : (E).HistoryReaches first last)
    (clear : ∀ current, last.state = some current →
      current.execution.application.config.defaulted = ∅) :
    ∀ current, first.state = some current → current.execution.application.config.defaulted = ∅ :=
    by
  intro current currentEq
  by_contra nonempty
  have initialDefault : runtime.PublicDefault leaks first.state := by
    rw [currentEq]
    exact nonempty
  have finalDefault := runtime.publicDefault_of_reaches leaks menu initial horizon scheduler
    reached initialDefault
  cases currentLast : last.state with
  | none => rw [currentLast] at finalDefault; exact finalDefault.elim
  | some control =>
      rw [currentLast] at finalDefault
      exact finalDefault (clear control currentLast)

end Vegas.EventGraphRuntime
