/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.LastKeyLaw
import Vegas.EventGraph.LastErasedLaw

/-! # Native automatic completion and erased keys

Automatic completion preserves the last-served law of erased keys, along every
automatic path and through bounded draining. Draining also maps states whose
configurations have one erased key to states whose configurations have one
erased key: automatic readiness reads only the cut and the defaulted players,
so both drains complete the same events with the same forced failures.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.State

open EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Bounded automatic draining preserves the last-served erased-key law. -/
theorem drain_lastErasedLaw {profile : graph.BehavioralProfile} {who : Player}
    (independent : LastIndependent profile who) (state : State graph) :
    lastErasedLaw profile who state.drain.config = lastErasedLaw profile who state.config :=
  lastErasedLaw_eq_of_lastLaw_eq (drain_lastLaw independent state)

/-- Every automatic path preserves the last-served erased-key law. -/
theorem automatic_path_lastErasedLaw {profile : graph.BehavioralProfile} {who : Player}
    (independent : LastIndependent profile who) {before after : State graph}
    (path : Relation.ReflTransGen AutomaticStep before after) :
    lastErasedLaw profile who after.config = lastErasedLaw profile who before.config := by
  induction path with
  | refl => rfl
  | tail _ step previous =>
      obtain ⟨event, eligible, rfl⟩ := step
      exact (lastErasedLaw_eq_of_lastLaw_eq
        (completeAutomatic_lastLaw independent _ event eligible)).trans previous

/-- A forced failure maps configurations with one erased key to configurations
with one erased key. -/
theorem completeFailure_erasedKey_congr {left right : State graph}
    (same : erasedKey left.config = erasedKey right.config) (event : graph.EventId)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event) :
    erasedKey (left.completeFailure event leftReady).config =
      erasedKey (right.completeFailure event rightReady).config := by
  unfold completeFailure
  cases nodeView graph event with
  | bind => exact erasedKey_complete_congr same event leftReady rightReady _ _
  | resolve => exact erasedKey_complete_congr same event leftReady rightReady _ _
  | sample => exact same

/-- Automatic readiness is read from the erased key. -/
theorem automaticReady_eq_of_erasedKey_eq {left right : State graph}
    (same : erasedKey left.config = erasedKey right.config) :
    left.AutomaticReady = right.AutomaticReady := by
  have cut := cut_eq_of_erasedKey_eq same
  have defaulted := defaulted_eq_of_erasedKey_eq same
  funext event
  unfold AutomaticReady
  rw [cut, defaulted]

private theorem choose_eq_of_predicate_eq {α : Type} (left right : α → Prop)
    (same : left = right) (leftExists : ∃ value, left value)
    (rightExists : ∃ value, right value) :
    Classical.choose leftExists = Classical.choose rightExists := by
  cases same
  rfl

theorem drainFuel_erasedKey_congr (fuel : Nat) {left right : State graph}
    (same : erasedKey left.config = erasedKey right.config) :
    erasedKey (drainFuel fuel left).config = erasedKey (drainFuel fuel right).config := by
  induction fuel generalizing left right with
  | zero => exact same
  | succ fuel ih =>
      have predicates := automaticReady_eq_of_erasedKey_eq same
      by_cases leftPending : ∃ event, left.AutomaticReady event
      · have rightPending : ∃ event, right.AutomaticReady event := by
          rwa [← predicates]
        have chosen := choose_eq_of_predicate_eq left.AutomaticReady right.AutomaticReady
          predicates leftPending rightPending
        simp only [drainFuel, dite_eq_left leftPending, dite_eq_left rightPending]
        apply ih
        have rightEligible : right.AutomaticReady (Classical.choose leftPending) := by
          rw [chosen]
          exact Classical.choose_spec rightPending
        have paired := completeFailure_erasedKey_congr same (Classical.choose leftPending)
          (Classical.choose_spec leftPending).1 rightEligible.1
        unfold completeAutomatic
        simpa only [chosen] using paired
      · have rightClear : ¬ ∃ event, right.AutomaticReady event := by
          rwa [← predicates]
        simp only [drainFuel, dite_eq_right leftPending, dite_eq_right rightClear]
        exact same

/-- **Draining is read from the erased key.** -/
theorem drain_erasedKey_congr {left right : State graph}
    (same : erasedKey left.config = erasedKey right.config) :
    erasedKey left.drain.config = erasedKey right.drain.config := by
  have fuel : left.config.remaining = right.config.remaining := by
    unfold EventGraph.Config.remaining
    rw [cut_eq_of_erasedKey_eq same]
  unfold drain
  rw [fuel]
  exact drainFuel_erasedKey_congr _ same

/-- A forced failure maps configurations with one key to configurations with
one key. -/
theorem completeFailure_runKey_congr {left right : State graph}
    (same : runKey left.config = runKey right.config) (event : graph.EventId)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event) :
    runKey (left.completeFailure event leftReady).config =
      runKey (right.completeFailure event rightReady).config := by
  unfold completeFailure
  cases nodeView graph event with
  | bind => exact runKey_complete_congr same event leftReady rightReady _ _
  | resolve => exact runKey_complete_congr same event leftReady rightReady _ _
  | sample => exact same

theorem drainFuel_runKey_congr (fuel : Nat) {left right : State graph}
    (same : runKey left.config = runKey right.config) :
    runKey (drainFuel fuel left).config = runKey (drainFuel fuel right).config := by
  induction fuel generalizing left right with
  | zero => exact same
  | succ fuel ih =>
      have predicates : left.AutomaticReady = right.AutomaticReady := by
        have records : completionOf left.config = completionOf right.config :=
          congrArg (fun key => key.2.2) same
        have cut : left.config.cut = right.config.cut := congrArg Prod.fst same
        have defaulted := defaulted_eq_of_completionOf_eq records
        funext event
        unfold AutomaticReady
        rw [cut, defaulted]
      by_cases leftPending : ∃ event, left.AutomaticReady event
      · have rightPending : ∃ event, right.AutomaticReady event := by
          rwa [← predicates]
        have chosen := choose_eq_of_predicate_eq left.AutomaticReady right.AutomaticReady
          predicates leftPending rightPending
        simp only [drainFuel, dite_eq_left leftPending, dite_eq_left rightPending]
        apply ih
        have rightEligible : right.AutomaticReady (Classical.choose leftPending) := by
          rw [chosen]
          exact Classical.choose_spec rightPending
        have paired := completeFailure_runKey_congr same (Classical.choose leftPending)
          (Classical.choose_spec leftPending).1 rightEligible.1
        unfold completeAutomatic
        simpa only [chosen] using paired
      · have rightClear : ¬ ∃ event, right.AutomaticReady event := by
          rwa [← predicates]
        simp only [drainFuel, dite_eq_right leftPending, dite_eq_right rightClear]
        exact same

/-- **Draining is read from the key.** -/
theorem drain_runKey_congr {left right : State graph}
    (same : runKey left.config = runKey right.config) :
    runKey left.drain.config = runKey right.drain.config := by
  have fuel : left.config.remaining = right.config.remaining := by
    unfold EventGraph.Config.remaining
    rw [show left.config.cut = right.config.cut from congrArg Prod.fst same]
  unfold drain
  rw [fuel]
  exact drainFuel_runKey_congr _ same

/-- The runtime state of a configuration with the initial runtime tables. -/
def ofConfig (config : graph.Config) : State graph :=
  { State.initial config.inputs with config := config }

/-- The configuration reached by draining a configuration. -/
def drainConfig (config : graph.Config) : graph.Config := (ofConfig config).drain.config

/-- Draining a state reaches a configuration with the key of draining its
configuration. -/
theorem drain_runKey_eq (state : State graph) :
    runKey state.drain.config = runKey (drainConfig state.config) :=
  drain_runKey_congr rfl

/-- Draining a configuration preserves its last-served erased-key law. -/
theorem drainConfig_lastErasedLaw {profile : graph.BehavioralProfile} {who : Player}
    (independent : LastIndependent profile who) (config : graph.Config) :
    lastErasedLaw profile who (drainConfig config) = lastErasedLaw profile who config :=
  drain_lastErasedLaw independent (ofConfig config)

/-- A quiescent state's configuration is its own drain, up to key. -/
theorem runKey_drainConfig_of_quiescent (state : State graph)
    (quiet : ∀ event, ¬ state.AutomaticReady event) :
    runKey (drainConfig state.config) = runKey state.config := by
  rw [← drain_runKey_eq, drain_eq_of_clear state quiet]

/-- Draining a drained configuration changes no key. -/
theorem drainConfig_drain (state : State graph) :
    runKey (drainConfig state.drain.config) = runKey (drainConfig state.config) := by
  rw [← drain_runKey_eq state]
  exact runKey_drainConfig_of_quiescent (ofConfig state.drain.config)
    (fun event eligible => drain_quiescent state event eligible)

end Vegas.EventGraphRuntime.State
