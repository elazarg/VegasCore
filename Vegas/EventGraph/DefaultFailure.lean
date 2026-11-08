/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.PublicationDecision

/-! # Every default ends in a failed publication

Suppose every binding of a graph is read by a later publication of the same
owner. A player defaults either by publishing a failure, or by omitting a
binding, which leaves the publication reading that binding still pending.
Once defaulted, the player is forced to withhold at every later publication.
So in every terminal configuration a defaulted player has a publication whose
output is a failure, whatever order the scheduler chose.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

variable (graph) in
/-- Every binding is read by a publication of the same owner. -/
def BindingsRevealed : Prop :=
  ∀ (event : graph.EventId) (owner : Player) (payload : L.Ty),
    graph.outputLayout event = .binding owner payload →
      ∃ reveal, graph.actor? reveal = some owner ∧
        (graph.outputLayout reveal).IsPublication ∧
        (.inr event : graph.Field) ∈ (graph.nodes reveal).readFields

namespace EventCode

variable {Field : Type} [DecidableEq Field] {layout : Field → EventField Player L}

omit [DecidableEq Player] in
/-- A default comes from a failed publication or from a binding. -/
theorem causesDefault_cases {output : EventField Player L} (code : EventCode layout output)
    (action : code.Action) (value : output.Value) (causes : code.causesDefault action value) :
    (output.IsPublication ∧ EventField.FailedValue output value) ∨
      ∃ owner payload, output = .binding owner payload := by
  cases code with
  | bind owner payload => exact Or.inr ⟨owner, payload, rfl⟩
  | resolve owner payload binding checks => exact Or.inl ⟨trivial, causes⟩
  | sample => exact absurd causes (by simp [causesDefault])

end EventCode

variable (graph) in
/-- Each defaulted player has a completed failed publication or a pending publication. -/
def DefaultsAccounted (config : graph.Config) : Prop :=
  ∀ who ∈ config.defaulted,
    (∃ reveal ∈ config.cut.completed, graph.actor? reveal = some who ∧
      (graph.outputLayout reveal).IsPublication ∧
      ∃ value, config.outputs reveal = some value ∧ EventField.FailedValue _ value) ∨
    (∃ reveal ∉ config.cut.completed, graph.actor? reveal = some who ∧
      (graph.outputLayout reveal).IsPublication)

namespace EventCode

variable {Field : Type} [DecidableEq Field] {layout : Field → EventField Player L}

omit [DecidableEq Player] in
/-- A binding node's actor is its output's owner. -/
theorem actor_eq_of_binding {output : EventField Player L} {owner : Player} {payload : L.Ty}
    (code : EventCode layout output) (binding : output = .binding owner payload) :
    code.actor = some owner := by
  cases code <;> simp_all [actor]

end EventCode

/-- The output of a step at a defaulted owner's publication is a failure. -/
theorem failed_of_defaulted_publication (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event) {who : Player}
    (actor : graph.actor? event = some who) (inactive : who ∈ config.defaulted)
    (publication : (graph.outputLayout event).IsPublication)
    (value : (graph.outputLayout event).Value)
    (supported : value ∈ (((graph.nodes event).eval? (config.effectiveAction event action)
      config.store).get (EventCode.eval?_isSome_of_reads (graph.nodes event) _ config.store
        (fun _ read => config.read_available ready read))).support) :
    EventField.FailedValue _ value := by
  have owned : (graph.nodes event).actor = some who := actor
  have effective : config.effectiveAction event action =
      (graph.nodes event).failureAction who owned := by
    unfold Config.effectiveAction EventCode.effectiveAction
    split
    · next owner ownerEq =>
        obtain rfl : owner = who := Option.some.inj (ownerEq.symm.trans owned)
        rw [ite_eq_left inactive]
    · next noneEq => exact absurd (noneEq.symm.trans owned) (by simp)
  obtain ⟨failure, evaluated, causes⟩ := (graph.nodes event).failureAction_eval? who owned
    config.store (fun _ read => config.read_available ready read)
  have law : (graph.nodes event).eval? (config.effectiveAction event action) config.store =
      some (PMF.pure failure) := by rw [effective, evaluated]
  simp only [law, Option.get_some, PMF.support_pure, Set.mem_singleton_iff] at supported
  subst supported
  rcases (graph.nodes event).causesDefault_cases _ _ causes with ⟨_, failed⟩ | ⟨_, _, binding⟩
  · exact failed
  · rw [binding] at publication
    exact publication.elim

/-- **Defaults stay accounted.** -/
theorem DefaultsAccounted.step (revealed : graph.BindingsRevealed) {config : graph.Config}
    (accounted : graph.DefaultsAccounted config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event) (next : graph.Config)
    (member : next ∈ (config.step event ready action).support) :
    graph.DefaultsAccounted next := by
  rw [Config.step, PMF.support_map] at member
  obtain ⟨value, supported, rfl⟩ := member
  intro who defaulted
  have completedIff (other : graph.EventId) :
      other ∈ (config.complete event ready action value).cut.completed ↔
        other = event ∨ other ∈ config.cut.completed := by
    simp
  have keep (other : graph.EventId) (different : other ≠ event) :
      (config.complete event ready action value).outputs other = config.outputs other :=
    config.complete_output_of_ne event other ready action value different
  by_cases before : who ∈ config.defaulted
  · rcases accounted who before with ⟨reveal, done, actor, publication, failed⟩ |
      ⟨reveal, pending, actor, publication⟩
    · have different : reveal ≠ event := fun same => ready.1 (same ▸ done)
      exact Or.inl ⟨reveal, (completedIff reveal).mpr (Or.inr done), actor, publication,
        by rw [keep reveal different]; exact failed⟩
    · by_cases same : reveal = event
      · subst same
        exact Or.inl ⟨reveal, (completedIff reveal).mpr (Or.inl rfl), actor, publication, value,
          config.complete_output_same reveal ready action value,
          failed_of_defaulted_publication config reveal ready action actor before publication
            value supported⟩
      · exact Or.inr ⟨reveal, fun done => by
          rcases (completedIff reveal).mp done with hit | old
          · exact same hit
          · exact pending old, actor, publication⟩
  · -- A new default at this event.
    have recorded : (EventGraph.completion graph event (config.actualDecision event action)
        value).defaultEvent = some who := by
      change who ∈ (config.complete event ready action value).defaults.defaulted at defaulted
      rw [Config.complete_defaults] at defaulted
      cases found : (EventGraph.completion graph event (config.actualDecision event action)
          value).defaultEvent with
      | none =>
          rw [found, DefaultHistory.defaulted_record_none] at defaulted
          exact absurd defaulted before
      | some other =>
          rw [found, DefaultHistory.defaulted_record_some, Finset.mem_insert] at defaulted
          rcases defaulted with same | old
          · rw [same]
          · exact absurd old before
    simp only [EventGraph.completion, Option.bind_eq_some_iff] at recorded
    obtain ⟨chosen, _, eventDefault⟩ := recorded
    unfold EventCode.defaultEvent at eventDefault
    split at eventDefault
    · next causes =>
        have actorEq : graph.actor? event = some who := eventDefault
        rcases (graph.nodes event).causesDefault_cases chosen value causes with
          ⟨publication, failed⟩ | ⟨owner, payload, binding⟩
        · exact Or.inl ⟨event, (completedIff event).mpr (Or.inl rfl), actorEq, publication,
            value, config.complete_output_same event ready action value, failed⟩
        · obtain ⟨reveal, revealActor, publication, reads⟩ :=
            revealed event owner payload binding
          have ownerEq : owner = who := Option.some.inj
            (((graph.nodes event).actor_eq_of_binding binding).symm.trans actorEq)
          subst ownerEq
          have pending : reveal ∉ config.cut.completed := fun done =>
            ready.1 (config.cut.predecessor_closed done
              (graph.reads_available reveal (.inr event) reads))
          have different : reveal ≠ event := by
            intro same
            subst same
            rw [binding] at publication
            exact publication.elim
          exact Or.inr ⟨reveal, fun done => by
            rcases (completedIff reveal).mp done with hit | old
            · exact different hit
            · exact pending old, revealActor, publication⟩
    · exact absurd eventDefault (by simp)

theorem defaultsAccounted_of_reachable (revealed : graph.BindingsRevealed)
    {inputs : graph.Inputs} {config : graph.Config} (reach : Config.Reachable inputs config) :
    graph.DefaultsAccounted config := by
  induction reach with
  | initial =>
      intro who defaulted
      exact absurd defaulted (by
        simp [Config.defaulted, Config.defaults, Config.initial, EventCompletion.defaults,
          DefaultHistory.defaulted])
  | step _ event ready action next member ih =>
      exact ih.step revealed event ready action next member

/-- **Every default ends in a failed publication.** In a reachable terminal
configuration of a graph whose bindings are all revealed, a defaulted player
has a publication whose output is a failure. -/
theorem failed_publication_of_defaulted (revealed : graph.BindingsRevealed)
    {inputs : graph.Inputs} {config : graph.Config} (reach : Config.Reachable inputs config)
    (terminal : config.cut.Terminal) {who : Player} (defaulted : who ∈ config.defaulted) :
    ∃ reveal, graph.actor? reveal = some who ∧ (graph.outputLayout reveal).IsPublication ∧
      ∃ value, config.outputs reveal = some value ∧ EventField.FailedValue _ value := by
  rcases defaultsAccounted_of_reachable revealed reach who defaulted with
    ⟨reveal, _, actor, publication, failed⟩ | ⟨reveal, pending, _, _⟩
  · exact ⟨reveal, actor, publication, failed⟩
  · exact absurd (terminal ▸ Finset.mem_univ reveal) pending

end Vegas.EventGraph
