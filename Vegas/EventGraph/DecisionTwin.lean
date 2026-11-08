/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.EventGraph.SchedulerErasure

/-! # Decisions of defaulted players are invisible

A completion records its event, the actual decision and the public default. A
player's decision is observed only by that player, through its own completions.
Once the player has defaulted, every later kernel of that player is forced, so
its recorded decisions influence nothing. Erasing the decisions recorded for
defaulted players therefore commutes with execution: every runner law, read
through the erasure, is the same from a configuration and from its erasure.

In particular two completions of an event of an active owner that store the
same value and default that owner yield configurations with one erasure, and
so the same law of every erasure-invariant readout.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

open Classical in
variable (graph) in
/-- Erase the decision of a completion whose owner is in `defaulted`. -/
def eraseCompletion (defaulted : Finset Player) (completion : graph.Completion) :
    graph.Completion :=
  if ∃ owner, graph.actor? completion.event = some owner ∧ owner ∈ defaulted then
    ⟨completion.event, none, completion.defaultEvent⟩
  else completion

@[simp] theorem eraseCompletion_event (defaulted : Finset Player)
    (completion : graph.Completion) :
    (graph.eraseCompletion defaulted completion).event = completion.event := by
  unfold eraseCompletion
  split <;> rfl

@[simp] theorem eraseCompletion_defaultEvent (defaulted : Finset Player)
    (completion : graph.Completion) :
    (graph.eraseCompletion defaulted completion).defaultEvent = completion.defaultEvent := by
  unfold eraseCompletion
  split <;> rfl

/-- Erasing with a larger set absorbs an earlier erasure. -/
theorem eraseCompletion_absorb {smaller larger : Finset Player} (subset : smaller ⊆ larger)
    (completion : graph.Completion) :
    graph.eraseCompletion larger (graph.eraseCompletion smaller completion) =
      graph.eraseCompletion larger completion := by
  by_cases erased : ∃ owner, graph.actor? completion.event = some owner ∧ owner ∈ smaller
  · obtain ⟨owner, actor, member⟩ := erased
    have later : ∃ owner, graph.actor? completion.event = some owner ∧ owner ∈ larger :=
      ⟨owner, actor, subset member⟩
    have first : graph.eraseCompletion smaller completion =
        ⟨completion.event, none, completion.defaultEvent⟩ := by
      unfold eraseCompletion
      exact ite_eq_left ⟨owner, actor, member⟩
    rw [first]
    unfold eraseCompletion
    rw [ite_eq_left later, ite_eq_left later]
  · have first : graph.eraseCompletion smaller completion = completion := by
      unfold eraseCompletion
      exact ite_eq_right erased
    rw [first]

namespace Config

/-- A configuration with the decisions recorded for its defaulted players erased. -/
def erase (config : graph.Config) : graph.Config where
  inputs := config.inputs
  cut := config.cut
  outputs := config.outputs
  output_available := config.output_available
  history := config.history.map (graph.eraseCompletion config.defaulted)
  history_nodup := by
    rw [List.map_map]
    have same : EventCompletion.event ∘ graph.eraseCompletion config.defaulted =
        EventCompletion.event := by
      funext completion
      exact eraseCompletion_event _ completion
    rw [same]
    exact config.history_nodup
  history_exact := by
    intro event
    rw [List.map_map]
    have same : EventCompletion.event ∘ graph.eraseCompletion config.defaulted =
        EventCompletion.event := by
      funext completion
      exact eraseCompletion_event _ completion
    rw [same]
    exact config.history_exact event

theorem erase_history (config : graph.Config) :
    config.erase.history = config.history.map (graph.eraseCompletion config.defaulted) := rfl

theorem erase_events (config : graph.Config) :
    config.erase.history.map EventCompletion.event = config.history.map EventCompletion.event := by
  rw [erase_history, List.map_map]
  congr 1
  funext completion
  exact eraseCompletion_event _ completion

theorem erase_defaults (config : graph.Config) : config.erase.defaults = config.defaults := by
  unfold Config.defaults EventCompletion.defaults
  rw [erase_history, List.map_map]
  simp only [Function.comp_def, eraseCompletion_defaultEvent]

theorem erase_defaulted (config : graph.Config) : config.erase.defaulted = config.defaulted := by
  unfold Config.defaulted
  rw [erase_defaults]

theorem erase_actualDecision (config : graph.Config) (event : graph.EventId)
    (action : graph.Action event) :
    config.erase.actualDecision event action = config.actualDecision event action := by
  unfold Config.actualDecision
  rw [erase_defaulted]

theorem erase_effectiveAction (config : graph.Config) (event : graph.EventId)
    (action : graph.Action event) :
    config.erase.effectiveAction event action = config.effectiveAction event action := by
  unfold Config.effectiveAction
  rw [erase_defaulted]

omit [DecidableEq Player] in
/-- Configurations agreeing on every field are equal. -/
theorem ext_fields {left right : graph.Config} (inputs : left.inputs = right.inputs)
    (cut : left.cut = right.cut) (outputs : left.outputs = right.outputs)
    (history : left.history = right.history) : left = right := by
  cases left
  cases right
  cases inputs
  cases cut
  cases outputs
  cases history
  rfl

theorem erase_erase (config : graph.Config) : config.erase.erase = config.erase := by
  refine ext_fields rfl rfl rfl ?_
  rw [erase_history, erase_defaulted, erase_history, List.map_map]
  congr 1
  funext completion
  exact eraseCompletion_absorb (subset_refl _) completion

theorem defaulted_subset_complete (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    config.defaulted ⊆ (config.complete event ready action value).defaulted := by
  unfold Config.defaulted Config.defaults
  rw [complete_history]
  exact EventCompletion.defaults_mono _ _

theorem complete_defaulted_erase (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    (config.erase.complete event ready action value).defaulted =
      (config.complete event ready action value).defaulted := by
  unfold Config.defaulted Config.defaults
  rw [complete_history, complete_history, EventCompletion.defaults_append,
    EventCompletion.defaults_append, erase_actualDecision]
  change (config.erase.defaults.record _).defaulted = (config.defaults.record _).defaulted
  rw [erase_defaults]

/-- Completing an erased configuration and erasing again is erasing the completion. -/
theorem erase_complete_erase (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    (config.erase.complete event ready action value).erase =
      (config.complete event ready action value).erase := by
  refine ext_fields rfl rfl rfl ?_
  rw [erase_history, erase_history, complete_defaulted_erase, complete_history, complete_history,
    erase_actualDecision, erase_history, List.map_append, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro completion _
  exact eraseCompletion_absorb (defaulted_subset_complete config event ready action value)
    completion

/-- A ready step of an erased configuration has the step's evaluator law. -/
theorem erase_step (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event) :
    ∃ law : PMF (graph.outputLayout event).Value,
      config.step event ready action = law.map (config.complete event ready action) ∧
      config.erase.step event ready action =
        law.map (config.erase.complete event ready action) := by
  have available := EventCode.eval?_isSome_of_reads (graph.nodes event)
    (config.effectiveAction event action) config.store
    (fun _ read => config.read_available ready read)
  refine ⟨_, config.step_eq_map_of_eval event ready action _ (Option.some_get available).symm,
    config.erase.step_eq_map_of_eval event ready action _ ?_⟩
  rw [erase_effectiveAction]
  exact (Option.some_get available).symm

end Config

theorem ownCompletions_map_erase (who : Player) (defaulted : Finset Player)
    (active : who ∉ defaulted) (history : List graph.Completion) :
    graph.ownCompletions who (history.map (graph.eraseCompletion defaulted)) =
      graph.ownCompletions who history := by
  induction history with
  | nil => rfl
  | cons head tail ih =>
      unfold ownCompletions at ih ⊢
      rw [List.map_cons, List.filter_cons, List.filter_cons, ih]
      by_cases actor : graph.actor? head.event = some who
      · have same : graph.eraseCompletion defaulted head = head := by
          unfold eraseCompletion
          refine ite_eq_right ?_
          rintro ⟨owner, owned, member⟩
          rw [actor] at owned
          cases owned
          exact active member
        rw [same]
      · have notOwn (completion : graph.Completion) (same : completion.event = head.event) :
            decide (graph.actor? completion.event = some who ∧ completion.decision.isSome) =
              false := by
          have other : graph.actor? completion.event ≠ some who := by
            rw [same]
            exact actor
          simp [other]
        rw [notOwn _ (eraseCompletion_event _ _), notOwn _ rfl]
        simp

theorem playerObserve_erase (who : Player) (config : graph.Config)
    (active : who ∉ config.defaulted) :
    graph.playerObserve who config.erase = graph.playerObserve who config := by
  unfold playerObserve
  rw [Config.erase_events, Config.erase_defaults, Config.erase_history,
    ownCompletions_map_erase who _ active]
  rfl

theorem publicObserve_erase (config : graph.Config) :
    graph.publicObserve config.erase = graph.publicObserve config := by
  unfold publicObserve
  rw [Config.erase_events, Config.erase_defaults]
  rfl

private theorem policy_congr {who : Player} (policy : graph.BehavioralPolicy who)
    (event : graph.EventId) (actor : (graph.nodes event).actor = some who)
    {left right : graph.PlayerObservation who} (same : left = right)
    (leftActive : who ∉ left.defaulted) (rightActive : who ∉ right.defaulted) :
    policy event actor left leftActive = policy event actor right rightActive := by
  subst same
  rfl

/-- Every action law ignores the decisions of defaulted players. -/
theorem actionLaw_erase (profile : graph.BehavioralProfile) (config : graph.Config)
    (event : graph.EventId) :
    actionLaw profile config.erase event = actionLaw profile config event := by
  cases ownerEq : (graph.nodes event).actor with
  | none =>
      rw [actionLaw_of_ownerless _ _ ownerEq, actionLaw_of_ownerless _ _ ownerEq]
  | some owner =>
      rw [actionLaw_of_actor _ _ ownerEq, actionLaw_of_actor _ _ ownerEq]
      by_cases inactive : owner ∈ config.defaulted
      · rw [dite_eq_left (by rw [Config.erase_defaulted]; exact inactive), dite_eq_left inactive]
      · rw [dite_eq_right (by rw [Config.erase_defaulted]; exact inactive),
          dite_eq_right inactive]
        exact policy_congr _ event ownerEq (playerObserve_erase owner config inactive) _ _

/-- **Runs ignore the decisions of defaulted players.** Every policy run, read
through the erasure, has the same law from a configuration and from its
erasure, for every public scheduler. -/
theorem runPlan_map_erase (profile : graph.BehavioralProfile) (scheduler : graph.PublicScheduler) :
    ∀ (fuel : Nat) (config : graph.Config),
      (graph.runPlan (graph.policyPlan profile scheduler) fuel config).map Config.erase =
        (graph.runPlan (graph.policyPlan profile scheduler) fuel config.erase).map
          Config.erase := by
  intro fuel
  induction fuel with
  | zero =>
      intro config
      simp only [EventGraph.runPlan, PMF.pure_map, Config.erase_erase]
  | succ fuel ih =>
      intro config
      by_cases terminal : config.cut.Terminal
      · have terminalErased : config.erase.cut.Terminal := terminal
        rw [EventGraph.runPlan, dite_eq_left terminal, EventGraph.runPlan,
          dite_eq_left terminalErased, PMF.pure_map, PMF.pure_map, Config.erase_erase]
      · have notTerminalErased : ¬ config.erase.cut.Terminal := terminal
        rw [runPlan_policyPlan_succ profile scheduler fuel config terminal,
          runPlan_policyPlan_succ profile scheduler fuel config.erase notTerminalErased,
          publicObserve_erase, PMF.map_bind, PMF.map_bind]
        refine congrArg₂ PMF.bind rfl (funext fun selected => ?_)
        have ready : config.cut.Ready selected.1 := (EventOrder.Cut.mem_enabled _ _).mp selected.2
        change ((eventStep profile config selected.1 ready).bind _).map Config.erase =
          ((eventStep profile config.erase selected.1 ready).bind _).map Config.erase
        unfold eventStep
        rw [actionLaw_erase, PMF.bind_bind, PMF.bind_bind, PMF.map_bind, PMF.map_bind]
        refine congrArg₂ PMF.bind rfl (funext fun action => ?_)
        obtain ⟨law, stepEq, erasedEq⟩ := config.erase_step selected.1 ready action
        rw [stepEq, erasedEq, PMF.bind_map, PMF.bind_map, PMF.map_bind, PMF.map_bind]
        refine congrArg₂ PMF.bind rfl (funext fun value => ?_)
        simp only [Function.comp_apply]
        rw [ih, ih (config.erase.complete selected.1 ready action value),
          Config.erase_complete_erase]

/-- A readout that ignores the decisions of defaulted players has the same run
law from a configuration and from its erasure. -/
theorem runPlan_map_of_erase_invariant {Outcome : Type*} (profile : graph.BehavioralProfile)
    (scheduler : graph.PublicScheduler) (read : graph.Config → Outcome)
    (invariant : ∀ config, read config.erase = read config) (fuel : Nat)
    {left right : graph.Config} (same : left.erase = right.erase) :
    (graph.runPlan (graph.policyPlan profile scheduler) fuel left).map read =
      (graph.runPlan (graph.policyPlan profile scheduler) fuel right).map read := by
  have factored : read = read ∘ Config.erase := by
    funext config
    exact (invariant config).symm
  rw [factored, ← PMF.map_comp, ← PMF.map_comp, runPlan_map_erase profile scheduler fuel left,
    runPlan_map_erase profile scheduler fuel right, same]

/-- **Decisions that default their owner are interchangeable.** Two completions
of an active owner's ready event storing the same value, each defaulting the
owner, give configurations with one erasure. -/
theorem Config.erase_complete_of_defaulting (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (owner : Player)
    (owned : graph.actor? event = some owner) (active : owner ∉ config.defaulted)
    (first second : graph.Action event) (value : (graph.outputLayout event).Value)
    (firstDefaults : (graph.nodes event).defaultEvent first value = some owner)
    (secondDefaults : (graph.nodes event).defaultEvent second value = some owner) :
    (config.complete event ready first value).erase =
      (config.complete event ready second value).erase := by
  have decision (action : graph.Action event) :
      config.actualDecision event action = some action := by
    unfold Config.actualDecision EventCode.actualDecision
    have owned' : (graph.nodes event).actor = some owner := owned
    rw [owned']
    simp [active]
  have completionEq (action : graph.Action event)
      (defaults : (graph.nodes event).defaultEvent action value = some owner) :
      EventGraph.completion graph event (config.actualDecision event action) value =
        ⟨event, some action, some owner⟩ := by
    rw [decision]
    simp [EventGraph.completion, defaults]
  have defaultedEq : (config.complete event ready first value).defaulted =
      (config.complete event ready second value).defaulted := by
    unfold Config.defaulted Config.defaults
    rw [complete_history, complete_history, EventCompletion.defaults_append,
      EventCompletion.defaults_append, completionEq first firstDefaults,
      completionEq second secondDefaults]
  have member : owner ∈ (config.complete event ready first value).defaulted := by
    unfold Config.defaulted Config.defaults
    rw [complete_history, EventCompletion.defaults_append, completionEq first firstDefaults]
    rw [DefaultHistory.defaulted_record_some]
    exact Finset.mem_insert_self _ _
  refine Config.ext_fields rfl rfl rfl ?_
  rw [Config.erase_history, Config.erase_history, ← defaultedEq, complete_history,
    complete_history, completionEq first firstDefaults, completionEq second secondDefaults,
    List.map_append, List.map_append]
  congr 1
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
  unfold eraseCompletion
  rw [ite_eq_left ⟨owner, owned, member⟩, ite_eq_left ⟨owner, owned, member⟩]

/-- A resolution whose binding failed publishes a failure whatever is disclosed. -/
theorem Config.step_of_binding_failed (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) {owner : Player} {payload : L.Ty}
    {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (failed : binding.get? config.store = some .failure) (action : graph.Action event) :
    config.step event ready action = PMF.pure (config.complete event ready action
      (cast (congrArg EventField.Value outputEq.symm) .failure)) := by
  have footprint := EventCode.readFields_cast outputEq (graph.nodes event)
  rw [codeEq] at footprint
  have available : ∀ field ∈ insert binding.field (GuardCheck.listReadFields checks),
      (config.store field).isSome = true := by
    intro field member
    apply config.read_available ready
    rw [← footprint]
    exact member
  have anyDisclose (disclose : Bool) :
      EventCode.resolveOutput? binding checks disclose config.store = some .failure := by
    rw [← EventCode.resolveOutput?_false_eq_failure binding checks config.store available]
    unfold EventCode.resolveOutput?
    rw [failed]
    cases disclose <;> rfl
  obtain ⟨disclose, rfl⟩ : ∃ disclose : Bool,
      action = cast (congrArg EventField.Action outputEq.symm) disclose :=
    ⟨cast (congrArg EventField.Action outputEq) action, by simp⟩
  rw [config.step_eq_map_of_code event ready outputEq (.resolve owner payload binding checks)
    codeEq disclose (PMF.pure .failure) (by rw [EventCode.resolve_eval?, anyDisclose]; rfl),
    PMF.pure_map]

omit [DecidableEq Player] in
/-- A failed publication defaults its owner whatever is disclosed. -/
theorem defaultEvent_of_failed_publication (event : graph.EventId) {owner : Player}
    {payload : L.Ty} {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (action : graph.Action event) :
    (graph.nodes event).defaultEvent action
      (cast (congrArg EventField.Value outputEq.symm) .failure) = some owner := by
  obtain ⟨disclose, rfl⟩ : ∃ disclose : Bool,
      action = cast (congrArg EventField.Action outputEq.symm) disclose :=
    ⟨cast (congrArg EventField.Action outputEq) action, by simp⟩
  have transport {output : EventField Player L} (same : graph.outputLayout event = output)
      (code : EventCode graph.layout output)
      (sameCode : cast (congrArg (EventCode graph.layout) same) (graph.nodes event) = code)
      (choice : output.Action) (value : output.Value) :
      (graph.nodes event).defaultEvent (cast (congrArg EventField.Action same.symm) choice)
        (cast (congrArg EventField.Value same.symm) value) = code.defaultEvent choice value := by
    cases same
    subst sameCode
    rfl
  rw [transport outputEq _ codeEq disclose .failure]
  rfl

/-- **Disclosures at a failed binding are interchangeable.** At a ready
resolution of an active owner whose binding failed, every two disclosures give
the same law of every readout that ignores the decisions of defaulted players. -/
theorem runPlan_map_of_binding_failed {Outcome : Type*} (profile : graph.BehavioralProfile)
    (scheduler : graph.PublicScheduler) (read : graph.Config → Outcome)
    (invariant : ∀ config, read config.erase = read config) (fuel : Nat)
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    {owner : Player} {payload : L.Ty} {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (active : owner ∉ config.defaulted) (first second : graph.Action event) :
    (graph.runPlan (graph.policyPlan profile scheduler) fuel (config.complete event ready first
        (cast (congrArg EventField.Value outputEq.symm) .failure))).map read =
      (graph.runPlan (graph.policyPlan profile scheduler) fuel (config.complete event ready second
        (cast (congrArg EventField.Value outputEq.symm) .failure))).map read := by
  have owned : graph.actor? event = some owner := by
    have actorEq := EventCode.actor_cast outputEq (graph.nodes event)
    rw [codeEq] at actorEq
    exact actorEq.symm
  exact runPlan_map_of_erase_invariant profile scheduler read invariant fuel
    (Config.erase_complete_of_defaulting config event ready owner owned active first second _
      (defaultEvent_of_failed_publication event outputEq codeEq first)
      (defaultEvent_of_failed_publication event outputEq codeEq second))

/-- The completion record of an event in an erasure is the erased record. -/
theorem completionOf_erase (config : graph.Config) (event : graph.EventId) :
    completionOf config.erase event =
      (completionOf config event).map (graph.eraseCompletion config.defaulted) := by
  unfold completionOf
  rw [Config.erase_history]
  generalize config.history = history
  induction history with
  | nil => rfl
  | cons head tail ih =>
      by_cases same : head.event = event
      · simp [same]
      · simp [same, ih]

end Vegas.EventGraph
