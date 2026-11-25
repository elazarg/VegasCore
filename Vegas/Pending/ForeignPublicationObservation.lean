module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.CompletionObservation
public import Vegas.EventGraph.ObservationStep
public import Vegas.Pending.EffectiveOpening

@[expose] public section

/-! # Observations after a foreign publication

The primary graph observation identifies the preceding view and the public
publication result. Withholding and an opening rejected by the guards can
give the same public result. Effective opening makes disclosure itself
readable from that result.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- A primary foreign publication's focal observation records the preceding
observation and its exact public result. No condition on disclosure or guard
acceptance is needed. -/
theorem foreign_publication_step_observation_eq_iff
    (focal owner : Player) (foreign : owner ≠ focal) (event : graph.EventId)
    {payload : L.Ty} {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (left right leftNext rightNext : graph.Config)
    (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (leftAction rightAction : graph.Action event)
    (leftTaken : leftNext ∈ (left.step event leftReady leftAction).support)
    (rightTaken : rightNext ∈ (right.step event rightReady rightAction).support) :
    graph.playerObserve focal leftNext = graph.playerObserve focal rightNext ↔
      graph.playerObserve focal left = graph.playerObserve focal right ∧
        leftNext.outputs event = rightNext.outputs event := by
  have visible : graph.fieldVisibleTo focal (.inr event) := by
    change (graph.outputLayout event).VisibleTo focal
    rw [outputEq]
    trivial
  constructor
  · intro same
    have leftRollback :=
      beforeCompletion_playerObserve_of_step focal left event leftReady leftAction leftNext
        leftTaken
    have rightRollback :=
      beforeCompletion_playerObserve_of_step focal right event rightReady rightAction rightNext
        rightTaken
    exact ⟨leftRollback.symm.trans ((congrArg (beforeCompletion event) same).trans rightRollback),
      graph.store_eq_of_playerObserve_eq focal leftNext rightNext same (.inr event) visible⟩
  · rintro ⟨same, publicResult⟩
    rw [Config.step, PMF.support_map] at leftTaken rightTaken
    obtain ⟨leftValue, _, rfl⟩ := leftTaken
    obtain ⟨rightValue, _, rfl⟩ := rightTaken
    rw [Config.complete_output_same, Config.complete_output_same] at publicResult
    obtain rfl := Option.some.inj publicResult
    obtain ⟨value, rfl⟩ : ∃ value : PublicationResult (L.Val payload),
        leftValue = cast (congrArg EventField.Value outputEq.symm) value :=
      ⟨cast (congrArg EventField.Value outputEq) leftValue, by simp⟩
    obtain ⟨first, rfl⟩ : ∃ first : Bool,
        leftAction = cast (congrArg EventField.Action outputEq.symm) first :=
      ⟨cast (congrArg EventField.Action outputEq) leftAction, by simp⟩
    obtain ⟨second, rfl⟩ : ∃ second : Bool,
        rightAction = cast (congrArg EventField.Action outputEq.symm) second :=
      ⟨cast (congrArg EventField.Action outputEq) rightAction, by simp⟩
    apply playerObserve_complete_congr focal left right same
    · exact fun _ => rfl
    · intro focalActor
      exact (foreign (Option.some.inj
        ((nodeView_resolve_actor outputEq codeEq).symm.trans focalActor))).elim
    · have defaults : left.defaulted = right.defaulted :=
        congrArg (fun observation : graph.PlayerObservation focal => observation.defaulted) same
      rw [left.completion_resolve_defaultEvent event owner payload binding checks
            outputEq codeEq first value,
          right.completion_resolve_defaultEvent event owner payload binding checks
            outputEq codeEq second value, defaults]

/-- At a rejected foreign opening, different requested actions have identical
graph observation laws. This includes disclosure and withholding. -/
theorem foreign_rejected_publication_observation_distribution
    (focal owner : Player) (foreign : owner ≠ focal) (event : graph.EventId)
    {payload : L.Ty} {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    {outputEq : graph.outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks}
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (config : graph.Config) (ready : config.cut.Ready event)
    (rejected : openingAccepted event config.store = false)
    (first second : graph.Action event) :
    (config.step event ready first).map (graph.playerObserve focal) =
      (config.step event ready second).map (graph.playerObserve focal) := by
  let failure := cast (congrArg EventField.Value outputEq.symm) .failure
  let next := fun action => config.complete event ready action failure
  have firstLaw := step_of_opening_rejected config event ready node rejected first
  have secondLaw := step_of_opening_rejected config event ready node rejected second
  have firstTaken : next first ∈ (config.step event ready first).support := by
    rw [firstLaw, PMF.mem_support_pure_iff]
  have secondTaken : next second ∈ (config.step event ready second).support := by
    rw [secondLaw, PMF.mem_support_pure_iff]
  have observed := (foreign_publication_step_observation_eq_iff focal owner foreign event
    outputEq codeEq config config (next first) (next second) ready ready first second
    firstTaken secondTaken).mpr ⟨rfl, by
      simp only [next, Config.complete_output_same]⟩
  rw [firstLaw, secondLaw, PMF.pure_map, PMF.pure_map]
  exact congrArg PMF.pure observed

section Resolution

variable {event : graph.EventId} {owner : Player} {payload : L.Ty}
  {binding : FieldRef graph.layout (.binding owner payload)}
  {checks : List (GuardCheck graph.layout payload)}
  {outputEq : graph.outputLayout event = .publication payload}
  {codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
    .resolve owner payload binding checks}
  (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)

include node

omit [DecidableEq Player] in
/-- An accepted opening successfully publishes the value of its immutable binding. -/
theorem openingAccepted_value (config : graph.Config)
    (accepted : openingAccepted event config.store = true) :
    ∃ value, binding.get? config.store = some (.success value) ∧
      EventCode.resolveOutput? binding checks true config.store = some (.success value) := by
  obtain ⟨value, resolved⟩ :
      ∃ value, EventCode.resolveOutput? binding checks true config.store =
        some (.success value) := by
    simp only [openingAccepted, node] at accepted
    cases stored : EventCode.resolveOutput? binding checks true config.store with
    | none => simp [stored] at accepted
    | some output =>
      cases output with
      | failure => simp [stored] at accepted
      | success value => exact ⟨value, rfl⟩
  refine ⟨value, ?_, resolved⟩
  cases stored : binding.get? config.store with
  | none => simp [EventCode.resolveOutput?, stored] at resolved
  | some bound =>
    cases guards : GuardCheck.allAccepted? checks config.store bound with
    | none => simp [EventCode.resolveOutput?, stored, guards] at resolved
    | some admitted =>
      cases admitted with
      | false => simp [EventCode.resolveOutput?, stored, guards] at resolved
      | true =>
        have equal : bound = .success value := by
          simpa [EventCode.resolveOutput?, stored, guards] using resolved
        exact congrArg some equal

/-- A disclosure supported by the effective-opening reference has an active
owner and is accepted. -/
theorem effectiveOpening_publication_disclosure_safe
    (base : graph.BehavioralProfile) (config : graph.Config) (action : graph.Action event)
    (chosen : action ∈ (actionDistribution (effectiveOpening base) config event).support)
    (disclose : (cast (congrArg EventField.Action outputEq) action : Bool) = true) :
    owner ∉ config.defaulted ∧ openingAccepted event config.store = true := by
  let owned := nodeView_resolve_actor outputEq codeEq
  rw [actionDistribution_of_actor _ _ owned] at chosen
  by_cases inactive : owner ∈ config.defaulted
  · rw [dite_eq_left inactive, PMF.mem_support_pure_iff] at chosen
    have failed := EventCode.failureAction_eq_cast outputEq (graph.nodes event)
      (.resolve owner payload binding checks) codeEq owner owned rfl
    rw [chosen, failed, cast_cast, cast_eq] at disclose
    cases disclose
  · refine ⟨inactive, ?_⟩
    rw [dite_eq_right inactive, effectiveOpening_of_resolve base node owned,
      PMF.mem_support_pure_iff] at chosen
    change action = cast (congrArg EventField.Action outputEq.symm)
      (openingAccepted event (graph.playerStore owner config.store)) at chosen
    rw [openingAccepted_playerStore event owned] at chosen
    rw [chosen] at disclose
    simpa using disclose

/-- An active, accepted disclosure publishes exactly its immutable binding value. -/
theorem publication_disclosed_value_of_accepted
    (config next : graph.Config)
    (ready : config.cut.Ready event) (active : owner ∉ config.defaulted)
    (action : graph.Action event)
    (moved : next ∈ (config.step event ready action).support)
    (disclose : (cast (congrArg EventField.Action outputEq) action : Bool) = true)
    (accepted : openingAccepted event config.store = true) :
    ∃ value, binding.get? config.store = some (.success value) ∧
      next.outputs event = some (cast (congrArg EventField.Value outputEq.symm) (.success value)) :=
    by
  obtain ⟨value, stored, resolved⟩ := openingAccepted_value node config accepted
  have actionEq : action = cast (congrArg EventField.Action outputEq.symm) true := by
    rw [← disclose, cast_cast, cast_eq]
  have evaluates : (EventCode.resolve owner payload binding checks).eval?
      ((EventCode.resolve owner payload binding checks).effectiveAction config.defaulted true)
        config.store = some (PMF.pure (.success value)) := by
    simp only [EventCode.effectiveAction, EventCode.actor, ite_eq_right active,
      EventCode.resolve_eval?, resolved, Option.map_some]
  rw [actionEq, config.step_eq_map_of_code event ready outputEq _ codeEq true _
    evaluates, PMF.pure_map, PMF.mem_support_pure_iff] at moved
  exact ⟨value, stored, moved ▸ Config.complete_output_same ..⟩

end Resolution

/-- If every requested disclosure here is active and accepted, the public
result recovers the requested Boolean. Withholding remains unrestricted. -/
theorem publication_action_from_output_of_safe
    (config next : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    {outputEq : graph.outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks}
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (action : graph.Action event)
    (safe : (cast (congrArg EventField.Action outputEq) action : Bool) = true →
      owner ∉ config.defaulted ∧ openingAccepted event config.store = true)
    (moved : next ∈ (config.step event ready action).support) :
    cast (congrArg EventField.Action outputEq) action =
      ((next.outputs event).map fun value =>
        !(cast (congrArg EventField.Value outputEq) value).isFailure).getD false := by
  let resolve := EventCode.resolve owner payload binding checks
  let encode := cast (congrArg EventField.Action outputEq.symm)
  let decoded := cast (congrArg EventField.Value outputEq)
  have falseStep : config.step event ready (encode false) = PMF.pure
      (config.complete event ready (encode false)
        (cast (congrArg EventField.Value outputEq.symm) .failure)) := by
    have footprint := EventCode.readFields_cast outputEq (graph.nodes event)
    rw [codeEq] at footprint
    have available : ∀ field ∈ insert binding.field (GuardCheck.listReadFields checks),
        (config.store field).isSome = true := by
      intro field member
      apply config.read_available ready
      rw [← footprint]
      exact member
    have effective : resolve.effectiveAction config.defaulted false = false := by
      by_cases inactive : owner ∈ config.defaulted <;>
        simp [resolve, EventCode.effectiveAction, EventCode.actor, inactive,
          EventCode.failureAction]
    have evaluates : resolve.eval? (resolve.effectiveAction config.defaulted false) config.store =
        some (PMF.pure .failure) := by
      rw [effective]
      change (EventCode.resolve owner payload binding checks).eval? false config.store = _
      rw [EventCode.resolve_eval?, EventCode.resolveOutput?_false_eq_failure _ _ _ available]
      rfl
    exact (config.step_eq_map_of_code event ready outputEq resolve codeEq false _ evaluates).trans
      (PMF.pure_map _ _)
  have readCompletion (disclose : Bool) (value : PublicationResult (L.Val payload))
      (output : next.outputs event = some (cast (congrArg EventField.Value outputEq.symm) value))
      (same : disclose = !value.isFailure) :
      cast (congrArg EventField.Action outputEq) (encode disclose) =
        ((next.outputs event).map fun value => !(decoded value).isFailure).getD false := by
    simp [output, encode, decoded, same]
  have withheld (actionEq : action = encode false) :
      cast (congrArg EventField.Action outputEq) action =
        ((next.outputs event).map fun value => !(decoded value).isFailure).getD false := by
    rw [actionEq, falseStep, PMF.mem_support_pure_iff] at moved
    have output := moved ▸ (Config.complete_output_same
      config event ready (encode false) (cast (congrArg EventField.Value outputEq.symm) .failure))
    rw [actionEq]
    exact readCompletion false .failure output rfl
  cases disclosed : (cast (congrArg EventField.Action outputEq) action : Bool) with
  | false =>
    have actionEq : action = encode false := by
      rw [← disclosed]
      simp [encode]
    simpa only [disclosed] using withheld actionEq
  | true =>
    obtain ⟨active, accepted⟩ := safe disclosed
    obtain ⟨value, _, output⟩ :=
      publication_disclosed_value_of_accepted node config next ready active action moved
        disclosed accepted
    rw [output]
    simp [PublicationResult.isFailure]

/-- Under the effective-opening reference, a supported publication action
discloses exactly when the result is a success. This also covers an owner
already defaulted at the start, whose action is forced. -/
theorem effectiveOpening_publication_action_from_output
    (base : graph.BehavioralProfile) (config next : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    {outputEq : graph.outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks}
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (action : graph.Action event)
    (chosen : action ∈ (actionDistribution (effectiveOpening base) config event).support)
    (moved : next ∈ (config.step event ready action).support) :
    cast (congrArg EventField.Action outputEq) action =
      ((next.outputs event).map fun value =>
        !(cast (congrArg EventField.Value outputEq) value).isFailure).getD false := by
  exact publication_action_from_output_of_safe config next event ready node action
    (effectiveOpening_publication_disclosure_safe node base config action chosen) moved

end Vegas.EventGraphRuntime
