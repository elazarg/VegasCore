/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Information
import GameTheory.Core.Form

/-! # Behavioral and public-scheduler semantics for event graphs

Player policies consume their actual player observations. Schedulers consume
only actual public observations and the finite set of enabled event identities.
Both the canonical and noncanonical games use the same cut-based executor.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- A player's policy supplies an action exactly at events owned by that
player, from the player's actual graph observation. -/
def BehavioralPolicy (graph : Vegas.EventGraph Player L) (who : Player) : Type :=
  ∀ (event : graph.EventId), graph.actor? event = some who →
    graph.PlayerObservation who → FinDist (graph.Action event)

/-- A playerwise behavioral profile. -/
abbrev BehavioralProfile (graph : Vegas.EventGraph Player L) :=
  ∀ who, BehavioralPolicy graph who

/-- A public scheduler selects one member of the currently enabled set. The
enabled set is computed from public completion identities, while the scheduler
receives no full semantic or private store. -/
def PublicScheduler (graph : Vegas.EventGraph Player L) : Type :=
  (observation : graph.PublicObservation) →
  (enabled : Finset graph.EventId) → enabled.Nonempty →
    FinDist {event : graph.EventId // event ∈ enabled}

namespace EventCode

/-- The unique action of a nonstrategic node. An ownerless node can only be a
sample node, with its trivial unit action. -/
def actionOfActorNone {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L}
    (code : EventCode layout output) (ownerless : code.actor = none) :
    EventField.Action output := by
  cases code with
  | bind owner payload => simp [actor] at ownerless
  | resolve owner payload binding checks => simp [actor] at ownerless
  | sample payload law => exact PUnit.unit

end EventCode

omit [DecidableEq Player] in
/-- A nonterminal cut has a nonempty executable enabled set. -/
theorem enabled_nonempty_of_not_terminal
    {graph : Vegas.EventGraph Player L}
    (config : graph.Config) (notTerminal : ¬ config.cut.Terminal) :
    config.cut.enabled.Nonempty := by
  obtain ⟨event, ready⟩ := config.cut.exists_ready_of_not_terminal notTerminal
  exact ⟨event, (EventOrder.Cut.mem_enabled _ _).mpr ready⟩

/-- Combine public scheduling with owner-local behavioral choices to obtain the
ideal executor's dependent randomized event plan. Chance nodes contribute only
their unit action; their retained law is sampled by `Config.step`. -/
def policyPlan (graph : Vegas.EventGraph Player L)
    (profile : BehavioralProfile graph) (scheduler : PublicScheduler graph) :
    graph.EventPlan :=
  fun config notTerminal =>
    let enabledNonempty := enabled_nonempty_of_not_terminal config notTerminal
    (scheduler (graph.publicObserve config) config.cut.enabled enabledNonempty).bind
      fun selected =>
        have ready : config.cut.Ready selected.1 :=
          (EventOrder.Cut.mem_enabled _ _).mp selected.2
        let readyEvent : {event : graph.EventId // config.cut.Ready event} :=
          ⟨selected.1, ready⟩
        match ownerEq : graph.actor? selected.1 with
        | some owner =>
            (profile owner selected.1 ownerEq (graph.playerObserve owner config)).map
              fun action => ⟨readyEvent, action⟩
        | none =>
            FinDist.pure ⟨readyEvent,
              EventCode.actionOfActorNone (graph.nodes selected.1) ownerEq⟩

/-- Execute a behavioral profile from one concrete input environment under a
public scheduler. -/
def runPolicies (graph : Vegas.EventGraph Player L)
    (scheduler : PublicScheduler graph) (profile : BehavioralProfile graph)
    (inputs : graph.Inputs) : FinDist graph.Config :=
  graph.run inputs (graph.policyPlan profile scheduler)

/-- Every supported policy execution completes the finite event graph. -/
theorem runPolicies_terminal (graph : Vegas.EventGraph Player L)
    (scheduler : PublicScheduler graph) (profile : BehavioralProfile graph)
    (inputs : graph.Inputs) (result : graph.Config)
    (member : result ∈ (graph.runPolicies scheduler profile inputs).support) :
    result.cut.Terminal := by
  exact graph.run_terminal inputs (graph.policyPlan profile scheduler) result member

/-- Attach the executor's terminality proof to every supported result. This is
only a proof-carrying relabeling of `runPolicies`, not a second executor. -/
def terminalOutcomes (graph : Vegas.EventGraph Player L)
    (scheduler : PublicScheduler graph) (profile : BehavioralProfile graph)
    (inputs : graph.Inputs) :
    FinDist {config : graph.Config // config.cut.Terminal} :=
  let law := graph.runPolicies scheduler profile inputs
  law.bindOnSupport fun result member =>
    FinDist.pure ⟨result, graph.runPolicies_terminal scheduler profile inputs result member⟩

/-- Forgetting the terminality certificate recovers the original execution law
exactly. -/
@[simp] theorem terminalOutcomes_map_val (graph : Vegas.EventGraph Player L)
    (scheduler : PublicScheduler graph) (profile : BehavioralProfile graph)
    (inputs : graph.Inputs) :
    (graph.terminalOutcomes scheduler profile inputs).map Subtype.val =
      graph.runPolicies scheduler profile inputs := by
  unfold terminalOutcomes
  rw [FinDist.map_bindOnSupport]
  simp

/-- The utility-free game signature of one event graph. Outcomes retain the
complete terminal configuration, including its scheduling and action trace. -/
def gameSignature (graph : Vegas.EventGraph Player L) : GameSignature Player where
  Strategy := graph.BehavioralPolicy
  Outcome := {config : graph.Config // config.cut.Terminal}

/-- Pull a utility on the graph's complete typed output store back to terminal
game outcomes. This canonical lift deliberately ignores trace metadata; a
trace-sensitive utility should instead consume the terminal configuration
subtype directly. -/
def liftOutcomeUtility (graph : Vegas.EventGraph Player L)
    (utility : graph.Outcome → Player → ℝ) :
    (graph.gameSignature).Outcome → Player → ℝ :=
  fun result who => utility (result.1.outcome result.2) who

/-- The graph game samples private/public initial inputs before execution, but
each player supplies one strategy across the entire input law. -/
def gameForm (graph : Vegas.EventGraph Player L) (inputs : FinDist graph.Inputs)
    (scheduler : PublicScheduler graph) : GameForm Player where
  sig := graph.gameSignature
  play profile := inputs.bind fun initial => graph.terminalOutcomes scheduler profile initial

/-- The canonical public scheduler always chooses the least enabled event id.
It ignores public store contents but remains an ordinary scheduler specialization. -/
def canonicalScheduler (graph : Vegas.EventGraph Player L) : PublicScheduler graph :=
  fun _ enabled nonempty =>
    FinDist.pure ⟨enabled.min' nonempty, Finset.min'_mem enabled nonempty⟩

omit [DecidableEq Player] in
/-- The canonical selector is not merely least among ready events: it is the
least unfinished event in the fixed numeric source order. -/
theorem canonical_min_ready_is_least_unfinished
    {graph : Vegas.EventGraph Player L} (cut : graph.order.Cut)
    (notTerminal : ¬ cut.Terminal) :
    let enabledNonempty : cut.enabled.Nonempty := by
      obtain ⟨event, ready⟩ := cut.exists_ready_of_not_terminal notTerminal
      exact ⟨event, (EventOrder.Cut.mem_enabled _ _).mpr ready⟩
    let selected := cut.enabled.min' enabledNonempty
    cut.Ready selected ∧ ∀ event, event ∉ cut.completed → selected.val ≤ event.val := by
  dsimp only
  let enabledNonempty : cut.enabled.Nonempty := by
    obtain ⟨event, ready⟩ := cut.exists_ready_of_not_terminal notTerminal
    exact ⟨event, (EventOrder.Cut.mem_enabled _ _).mpr ready⟩
  let selected := cut.enabled.min' enabledNonempty
  have selectedReady : cut.Ready selected :=
    (EventOrder.Cut.mem_enabled _ _).mp (Finset.min'_mem _ _)
  refine ⟨selectedReady, ?_⟩
  intro event unfinished
  obtain ⟨readyEvent, readyEventReady, readyEventLe⟩ :=
    cut.exists_ready_le_of_unfinished event unfinished
  exact (Finset.min'_le cut.enabled readyEvent
    ((EventOrder.Cut.mem_enabled _ _).mpr readyEventReady)).trans readyEventLe

/-- A concrete noncanonical scheduler useful for witnesses: choose the greatest
currently enabled event id. -/
def greatestScheduler (graph : Vegas.EventGraph Player L) : PublicScheduler graph :=
  fun _ enabled nonempty =>
    FinDist.pure ⟨enabled.max' nonempty, Finset.max'_mem enabled nonempty⟩

/-- Canonical-order specialization of the same ready-event graph game. -/
def canonicalGame (graph : Vegas.EventGraph Player L) (inputs : FinDist graph.Inputs) :
    GameForm Player :=
  graph.gameForm inputs graph.canonicalScheduler

end Vegas.EventGraph
