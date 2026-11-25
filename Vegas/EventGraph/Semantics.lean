module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.Information
public import GameTheory.Core.Form

@[expose] public section

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
    (observation : graph.PlayerObservation who) → who ∉ observation.defaulted →
      PMF (graph.Action event)

/-- A playerwise behavioral profile. -/
abbrev BehavioralProfile (graph : Vegas.EventGraph Player L) :=
  ∀ who, BehavioralPolicy graph who

/-- Every local action law of the profile has finite support. -/
def ProfileFiniteSupport (graph : Vegas.EventGraph Player L)
    (profile : graph.BehavioralProfile) : Prop :=
  ∀ who event actor observation active,
    (profile who event actor observation active).support.Finite

/-- Every event has finitely many actions, so every behavioral policy of the
graph, including every deviation, branches finitely. -/
def FiniteActions (graph : Vegas.EventGraph Player L) : Prop :=
  ∀ event, Finite (graph.Action event)

theorem FiniteActions.profileFiniteSupport {graph : Vegas.EventGraph Player L}
    (finite : graph.FiniteActions) (profile : graph.BehavioralProfile) :
    graph.ProfileFiniteSupport profile := fun _ event _ _ _ =>
  have := finite event
  Set.toFinite _

/-- A public scheduler selects one member of the currently enabled set. The
enabled set is computed from public completion identities, while the scheduler
receives no full semantic or private store. -/
def PublicScheduler (graph : Vegas.EventGraph Player L) : Type :=
  (observation : graph.PublicObservation) →
  (enabled : Finset graph.EventId) → enabled.Nonempty →
    PMF {event : graph.EventId // event ∈ enabled}

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

omit [DecidableEq Player] in
/-- An ownerless event has only one action. -/
theorem action_eq_of_actor_none {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {output : EventField Player L}
    (code : EventCode layout output) (ownerless : code.actor = none)
    (left right : EventField.Action output) : left = right := by
  cases code with
  | bind owner payload => simp [actor] at ownerless
  | resolve owner payload binding checks => simp [actor] at ownerless
  | sample payload law => exact Subsingleton.elim left right

end EventCode

section

variable {graph : Vegas.EventGraph Player L}

/-- The action law a profile supplies at one event: a defaulted owner's forced
failure, the owner's policy at its actual observation, or a chance node's unit
action. -/
def actionLaw (profile : graph.BehavioralProfile) (config : graph.Config)
    (event : graph.EventId) : PMF (graph.Action event) :=
  match ownerEq : (graph.nodes event).actor with
  | some owner =>
      if inactive : owner ∈ config.defaulted then
        PMF.pure ((graph.nodes event).failureAction owner ownerEq)
      else profile owner event ownerEq (graph.playerObserve owner config) inactive
  | none => PMF.pure (EventCode.actionOfActorNone (graph.nodes event) ownerEq)

/-- The action law at an owned event. -/
theorem actionLaw_of_actor (profile : graph.BehavioralProfile) (config : graph.Config)
    {event : graph.EventId} {owner : Player} (ownerEq : (graph.nodes event).actor = some owner) :
    actionLaw profile config event =
      if inactive : owner ∈ config.defaulted then
        PMF.pure ((graph.nodes event).failureAction owner ownerEq)
      else profile owner event ownerEq (graph.playerObserve owner config) inactive := by
  unfold actionLaw
  split
  · next same sameEq =>
      obtain rfl : same = owner := Option.some.inj (sameEq.symm.trans ownerEq)
      rfl
  · next noneEq => exact absurd (noneEq.symm.trans ownerEq) (by simp)

/-- The action law at an ownerless event. -/
theorem actionLaw_of_ownerless (profile : graph.BehavioralProfile) (config : graph.Config)
    {event : graph.EventId} (ownerless : (graph.nodes event).actor = none) :
    actionLaw profile config event =
      PMF.pure (EventCode.actionOfActorNone (graph.nodes event) ownerless) := by
  unfold actionLaw
  split
  · next same sameEq => exact absurd (sameEq.symm.trans ownerless) (by simp)
  · rfl

/-- One event's action drawn from the profile and then executed. -/
def eventStep (profile : graph.BehavioralProfile) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event) : PMF graph.Config :=
  (actionLaw profile config event).bind (config.step event ready)

theorem eventStep_congr_event (profile : graph.BehavioralProfile) (config : graph.Config)
    {event other : graph.EventId} (same : event = other) (ready : config.cut.Ready event)
    (otherReady : config.cut.Ready other) :
    eventStep profile config event ready = eventStep profile config other otherReady := by
  subst same
  rfl

end

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
        (actionLaw profile config selected.1).map fun action =>
          ⟨⟨selected.1, (EventOrder.Cut.mem_enabled _ _).mp selected.2⟩, action⟩

section

variable {graph : Vegas.EventGraph Player L}

/-- The policy plan selects an enabled event publicly and then draws the action
law of that event. -/
theorem policyPlan_eq (profile : graph.BehavioralProfile) (scheduler : graph.PublicScheduler)
    (config : graph.Config) (notTerminal : ¬ config.cut.Terminal) :
    graph.policyPlan profile scheduler config notTerminal =
      (scheduler (graph.publicObserve config) config.cut.enabled
        (enabled_nonempty_of_not_terminal config notTerminal)).bind fun selected =>
          (actionLaw profile config selected.1).map fun action =>
            ⟨⟨selected.1, (EventOrder.Cut.mem_enabled _ _).mp selected.2⟩, action⟩ := rfl

/-- One step of the runner under a policy plan. -/
theorem runPlan_policyPlan_succ (profile : graph.BehavioralProfile)
    (scheduler : graph.PublicScheduler) (fuel : Nat) (config : graph.Config)
    (notTerminal : ¬ config.cut.Terminal) :
    graph.runPlan (graph.policyPlan profile scheduler) (fuel + 1) config =
      (scheduler (graph.publicObserve config) config.cut.enabled
        (enabled_nonempty_of_not_terminal config notTerminal)).bind fun selected =>
          (eventStep profile config selected.1
            ((EventOrder.Cut.mem_enabled _ _).mp selected.2)).bind
              (graph.runPlan (graph.policyPlan profile scheduler) fuel) := by
  rw [EventGraph.runPlan, dite_eq_right notTerminal, policyPlan_eq, PMF.bind_bind]
  congr 1
  funext selected
  rw [PMF.bind_map, eventStep, PMF.bind_bind]
  rfl

end

/-- Execute a behavioral profile from one concrete input environment under a
public scheduler. -/
def runPolicies (graph : Vegas.EventGraph Player L)
    (scheduler : PublicScheduler graph) (profile : BehavioralProfile graph)
    (inputs : graph.Inputs) : PMF graph.Config :=
  graph.run inputs (graph.policyPlan profile scheduler)

/-- A policy plan branches finitely when the profile does: the scheduler
selects among finitely many enabled events. -/
theorem policyPlan_support_finite (graph : Vegas.EventGraph Player L)
    (profile : BehavioralProfile graph) (finiteProfile : graph.ProfileFiniteSupport profile)
    (scheduler : PublicScheduler graph) (config : graph.Config)
    (notTerminal : ¬ config.cut.Terminal) :
    (graph.policyPlan profile scheduler config notTerminal).support.Finite := by
  unfold policyPlan
  rw [PMF.support_bind]
  refine (Set.toFinite _).biUnion fun selected _ => ?_
  rw [PMF.support_map]
  cases actor : (graph.nodes selected.1).actor with
  | none => simp [actionLaw_of_ownerless profile config actor]
  | some owner =>
      rw [actionLaw_of_actor profile config actor]
      split
      · simp
      · exact (finiteProfile _ _ _ _ _).image _

theorem runPolicies_support_finite (graph : Vegas.EventGraph Player L)
    (scheduler : PublicScheduler graph) (profile : BehavioralProfile graph)
    (finiteProfile : graph.ProfileFiniteSupport profile) (inputs : graph.Inputs) :
    (graph.runPolicies scheduler profile inputs).support.Finite :=
  graph.runPlan_support_finite _ (graph.policyPlan_support_finite profile finiteProfile scheduler)
    _ _

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
    PMF {config : graph.Config // config.cut.Terminal} :=
  let law := graph.runPolicies scheduler profile inputs
  law.bindOnSupport fun result member =>
    PMF.pure ⟨result, graph.runPolicies_terminal scheduler profile inputs result member⟩

/-- Forgetting the terminality certificate recovers the original execution law
exactly. -/
@[simp] theorem terminalOutcomes_map_val (graph : Vegas.EventGraph Player L)
    (scheduler : PublicScheduler graph) (profile : BehavioralProfile graph)
    (inputs : graph.Inputs) :
    (graph.terminalOutcomes scheduler profile inputs).map Subtype.val =
      graph.runPolicies scheduler profile inputs := by
  unfold terminalOutcomes
  rw [map_bindOnSupport,
    bindOnSupport_eq_bind_of_eq_on_support _ (g := PMF.pure) fun _ _ => PMF.pure_map _ _,
    PMF.bind_pure]

/-- The utility-free game signature of one event graph. Outcomes retain the
complete terminal configuration, including its scheduling and action trace. -/
def gameSignature (graph : Vegas.EventGraph Player L) : GameSignature Player where
  Strategy := graph.BehavioralPolicy
  Outcome := {config : graph.Config // config.cut.Terminal}

/-- The graph game samples private/public initial inputs before execution, but
each player supplies one strategy across the entire input law. -/
def gameForm (graph : Vegas.EventGraph Player L) (inputs : PMF graph.Inputs)
    (scheduler : PublicScheduler graph) : GameForm Player where
  sig := graph.gameSignature
  play profile := inputs.bind fun initial => graph.terminalOutcomes scheduler profile initial

/-- Forgetting terminality proofs gives the complete configuration execution law. -/
theorem gameForm_play_map_val (graph : Vegas.EventGraph Player L) (inputs : PMF graph.Inputs)
    (scheduler : PublicScheduler graph) (profile : BehavioralProfile graph) :
    ((graph.gameForm inputs scheduler).play profile).map Subtype.val =
      inputs.bind (graph.runPolicies scheduler profile) := by
  change (inputs.bind fun initial => graph.terminalOutcomes scheduler profile initial).map _ = _
  simp only [PMF.map_bind, terminalOutcomes_map_val]

/-- Every play of a finitely branching profile from a finite input law has
finite support, so every utility is integrable against it. -/
theorem gameForm_play_support_finite (graph : Vegas.EventGraph Player L)
    (inputs : PMF graph.Inputs) (finiteInputs : inputs.support.Finite)
    (scheduler : PublicScheduler graph) (profile : BehavioralProfile graph)
    (finiteProfile : graph.ProfileFiniteSupport profile) :
    ((graph.gameForm inputs scheduler).play profile).support.Finite := by
  change (inputs.bind fun initial =>
    graph.terminalOutcomes scheduler profile initial).support.Finite
  rw [PMF.support_bind]
  refine finiteInputs.biUnion fun initial _ => ?_
  have finiteRun := graph.runPolicies_support_finite scheduler profile finiteProfile initial
  rw [← graph.terminalOutcomes_map_val scheduler profile initial, PMF.support_map] at finiteRun
  exact finiteRun.of_finite_image Subtype.val_injective.injOn

/-- The canonical public scheduler always chooses the least enabled event id.
It ignores public store contents but remains an ordinary scheduler specialization. -/
def canonicalScheduler (graph : Vegas.EventGraph Player L) : PublicScheduler graph :=
  fun _ enabled nonempty =>
    PMF.pure ⟨enabled.min' nonempty, Finset.min'_mem enabled nonempty⟩

section

variable {graph : Vegas.EventGraph Player L}

/-- The canonical runner completes the least ready event. -/
theorem runPlan_canonical_succ (profile : graph.BehavioralProfile) (fuel : Nat)
    (config : graph.Config) (notTerminal : ¬ config.cut.Terminal) (event : graph.EventId)
    (ready : config.cut.Ready event) (least : ∀ other, config.cut.Ready other → event ≤ other) :
    graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) (fuel + 1) config =
      (eventStep profile config event ready).bind
        (graph.runPlan (graph.policyPlan profile graph.canonicalScheduler) fuel) := by
  rw [runPlan_policyPlan_succ profile _ fuel config notTerminal]
  simp only [EventGraph.canonicalScheduler, PMF.pure_bind]
  congr 1
  apply eventStep_congr_event
  apply le_antisymm
  · exact Finset.min'_le _ _ ((EventOrder.Cut.mem_enabled _ _).mpr ready)
  · exact least _ ((EventOrder.Cut.mem_enabled _ _).mp (Finset.min'_mem _ _))

omit [DecidableEq Player] in
/-- A nonterminal cut has a least ready event. -/
theorem exists_least_ready (config : graph.Config) (notTerminal : ¬ config.cut.Terminal) :
    ∃ event, config.cut.Ready event ∧ ∀ other, config.cut.Ready other → event ≤ other := by
  let nonempty := enabled_nonempty_of_not_terminal config notTerminal
  refine ⟨config.cut.enabled.min' nonempty,
    (EventOrder.Cut.mem_enabled _ _).mp (Finset.min'_mem _ _), fun other ready => ?_⟩
  exact Finset.min'_le _ _ ((EventOrder.Cut.mem_enabled _ _).mpr ready)

end

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
    PMF.pure ⟨enabled.max' nonempty, Finset.max'_mem enabled nonempty⟩

/-- Canonical-order specialization of the same ready-event graph game. -/
def canonicalGame (graph : Vegas.EventGraph Player L) (inputs : PMF graph.Inputs) :
    GameForm Player :=
  graph.gameForm inputs graph.canonicalScheduler

end Vegas.EventGraph
