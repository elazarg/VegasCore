module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.CanonicalOutcomePublication
public import Vegas.Pending.CanonicalKeyLaw
public import Vegas.EventGraph.CanonicalStep

@[expose] public section

/-! # The canonical outcome law at its head event

The outcome law of a ready-independent profile ignores automatic default
completion. At a ready event that precedes every unfinished event, the canonical
run takes that event first: an active owner draws its action from the profile,
and a chance event steps without any player.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Automatic default completion preserves the outcome law of a
ready-independent profile through a key-determined readout. -/
theorem outcomeLaw_drain {Outcome : Type*} {profile : graph.BehavioralProfile}
    (independent : ReadyIndependent profile) (read : graph.Config → Outcome)
    (keyed : ∀ left right : graph.Config, runKey left = runKey right → read left = read right)
    (state : EventGraphRuntime.State graph) :
    outcomeLaw profile read state.drain.config = outcomeLaw profile read state.config :=
  outcomeLaw_eq_of_canonicalLaw_eq read keyed
    (EventGraphRuntime.State.drain_canonicalLaw independent state)

omit [DecidableEq Player] in
private theorem remaining_succ_of_ready (config : graph.Config) {event : graph.EventId}
    (ready : config.cut.Ready event) : ∃ fuel, config.remaining = fuel + 1 := by
  have nonzero : config.remaining ≠ 0 := by
    intro zero
    have terminal := config.terminal_iff_remaining_zero.mpr zero
    apply ready.1
    rw [EventOrder.Cut.Terminal] at terminal
    rw [terminal]
    exact Finset.mem_univ _
  exact Nat.exists_eq_succ_of_ne_zero nonzero

/-- A step from a configuration continues with one less unit of fuel. -/
private theorem step_bind_runPlan_fuel {Result : Type*} (plan : graph.EventPlan)
    (after : PMF graph.Config → PMF Result) (config : graph.Config)
    {event : graph.EventId} (ready : config.cut.Ready event) (action : graph.Action event)
    {fuel : Nat} (fuelEq : config.remaining = fuel + 1) :
    (config.step event ready action).bind (fun next => after (graph.runPlan plan fuel next)) =
      (config.step event ready action).bind
        (fun next => after (graph.runPlan plan next.remaining next)) := by
  apply bind_congr_on_support _
  intro next member
  have progress := config.remaining_step event ready action next member
  have remaining : next.remaining = fuel := by omega
  rw [remaining]

/-- **The owned head step.** At a ready event of an active owner that precedes
every unfinished event, the outcome law draws the owner's action from the
profile and continues from the stepped configuration. -/
theorem outcomeLaw_actor {Outcome : Type*} (profile : graph.BehavioralProfile)
    (read : graph.Config → Outcome) (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val)
    (who : Player) (actor : graph.actor? event = some who) (active : who ∉ config.defaulted) :
    outcomeLaw profile read config =
      (profile who event actor (graph.playerObserve who config) active).bind fun action =>
        (config.step event ready action).bind (outcomeLaw profile read) := by
  obtain ⟨fuel, fuelEq⟩ := remaining_succ_of_ready config ready
  unfold outcomeLaw
  rw [fuelEq, graph.runPlan_canonical_actor profile fuel config event ready least who actor
    active, PMF.map_bind]
  apply bind_congr_on_support _
  intro action _
  rw [PMF.map_bind]
  exact step_bind_runPlan_fuel _ (PMF.map read) config ready action fuelEq

/-- **The chance head step.** At a ready chance event that precedes every
unfinished event, every action steps to the same outcome law. -/
theorem step_bind_outcomeLaw_ownerless {Outcome : Type*} (profile : graph.BehavioralProfile)
    (read : graph.Config → Outcome) (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event)
    (least : ∀ other, other ∉ config.cut.completed → event.val ≤ other.val)
    (ownerless : graph.actor? event = none) (action : graph.Action event) :
    (config.step event ready action).bind (outcomeLaw profile read) =
      outcomeLaw profile read config := by
  obtain ⟨fuel, fuelEq⟩ := remaining_succ_of_ready config ready
  symm
  unfold outcomeLaw
  rw [fuelEq, graph.runPlan_canonical_ownerless profile fuel config event ready least ownerless,
    (graph.nodes event).action_eq_of_actor_none ownerless
      (EventCode.actionOfActorNone (graph.nodes event) ownerless) action, PMF.map_bind]
  exact step_bind_runPlan_fuel _ (PMF.map read) config ready action fuelEq

end Vegas.EventGraphRuntime
