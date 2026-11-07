/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealRunStep
import Vegas.Game.RevealBlockEndpoint

/-! # Agreement from the deviator's view of the closure

While the deviator records no decision on a step of a run, every step settles,
so the closure's key stays the starting one. The closure stores the output of
every honest reveal ready along the way, and that output says whether the
opening is accepted and, if so, which value is opened. Outputs of reveals are
visible to every player. So two steps whose starting closures look alike to
the deviator keep their ready reveals accepted alike, with equal stored
bindings when accepted or the deviator's.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}

/-- **The closure along a run without decisions of the deviator.** On a path
whose new records are classified as in a run, where the deviator records no
decision, the closure's key stays the starting one. -/
theorem run_path_closure_settles (base : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        (serviceGraph setup mode).normalizeProfile base owner event actor
          ((serviceGraph setup mode).playerObserve owner config) active =
          PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (independent : ReadyIndependent ((serviceGraph setup mode).normalizeProfile base))
    (who : Player) {start finish : Nat} {origin final : (serviceGraph setup mode).Config}
    (sound : BlockRecordsSound who start finish origin final)
    (quiet : ∀ event : (serviceGraph setup mode).EventId, event ∉ origin.cut.completed →
      (serviceGraph setup mode).actor? event = some who →
        ∀ record, completionOf final event = some record → record.decision = none) :
    ∀ current : (serviceGraph setup mode).Config,
      Relation.ReflTransGen Config.Step origin current →
      Relation.ReflTransGen Config.Step current final →
      runKey (closure ((serviceGraph setup mode).normalizeProfile base) who current) =
        runKey (closure ((serviceGraph setup mode).normalizeProfile base) who origin) := by
  intro current walked
  induction walked with
  | refl => intro _; rfl
  | @tail before after walked moved ih =>
  intro rest
  have previous := ih (Relation.ReflTransGen.head moved rest)
  obtain ⟨event, ready, action, member⟩ := moved
  have fresh : event ∉ origin.cut.completed := fun done =>
    ready.1 (Config.Step.path_completed_mono walked done)
  rcases run_step_settles base decides who member rest sound fresh with
    ⟨settles, settledEq⟩ | ⟨mine, decided⟩
  · rw [settledEq, closure_settled_runKey independent _ before rfl event settles]
    exact previous
  · obtain ⟨value, _, recorded⟩ := step_record_path member rest
    exact (decided (quiet event fresh mine _ recorded)).elim

/-- **The closure's output at an honest reveal.** At a ready reveal of an
active honest owner, the closure stores the opened binding's value when the
opening is accepted and a failure otherwise. -/
theorem honest_closure_output (base : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        (serviceGraph setup mode).normalizeProfile base owner event actor
          ((serviceGraph setup mode).playerObserve owner config) active =
          PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (independent : ReadyIndependent ((serviceGraph setup mode).normalizeProfile base))
    (who : Player) {config : (serviceGraph setup mode).Config}
    {event : (serviceGraph setup mode).EventId} (ready : config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    (honest : owner ≠ who) (active : owner ∉ config.defaulted) :
    (openingAccepted event config.store = true → ∃ value,
      binding.get? config.store = some (.success value) ∧
      (closure ((serviceGraph setup mode).normalizeProfile base) who config).outputs event =
        some (cast (congrArg EventField.Value outputEq.symm) (PublicationResult.success value))) ∧
    (openingAccepted event config.store = false →
      (closure ((serviceGraph setup mode).normalizeProfile base) who config).outputs event =
        some (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure)) := by
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  have owned := nodeView_resolve_actor outputEq codeEq
  have ownedNode : (G.nodes event).actor = some owner := owned
  have foreign : G.actor? event ≠ some who := fun same =>
    honest (Option.some.inj (owned.symm.trans same))
  have publication : (G.outputLayout event).IsPublication := by
    rw [outputEq]
    trivial
  have settles := honest_settles base decides who ready publication foreign
  have acting : actionLaw R config event = PMF.pure (cast (congrArg EventField.Action
      outputEq.symm) (openingAccepted event config.store)) := by
    rw [actionLaw_of_actor _ _ ownedNode, dite_eq_right active]
    exact decides config event owner payload binding checks outputEq codeEq node owned active
  refine ⟨fun accepted => ?_, fun rejected => ?_⟩
  · obtain ⟨opened, resolved⟩ := resolveOutput_of_accepted node accepted
    have stepEq := resolve_step_eq ready outputEq codeEq active true (.success opened) resolved
    rw [← accepted] at stepEq
    refine ⟨opened, binding_get_of_resolveOutput_success resolved, ?_⟩
    exact (closure_settles_record independent _ config rfl event _ _ settles acting
      (eval_eq_of_step stepEq)).1
  · have stepEq := step_of_opening_rejected config event ready node rejected
      (cast (congrArg EventField.Action outputEq.symm) (openingAccepted event config.store))
    exact (closure_settles_record independent _ config rfl event _ _ settles acting
      (eval_eq_of_step stepEq)).1

/-- Configurations whose keys look alike to a player store alike every field
visible to that player. -/
theorem store_visible_of_keyView {graph : Vegas.EventGraph Player L} (who : Player)
    {left right : graph.Config}
    (views : keyView who (runKey left) = keyView who (runKey right)) {field : graph.Field}
    (visible : graph.fieldVisibleTo who field) : left.store field = right.store field := by
  rw [keyView_runKey, keyView_runKey] at views
  have stores := congrArg (fun observation : graph.PlayerObservation who => observation.store)
    (Option.some.inj views)
  rw [normalizeObservation_playerObserve, normalizeObservation_playerObserve] at stores
  simp only at stores
  have atField := congrFun stores field
  rwa [playerStore_of_visible (visible := visible),
    playerStore_of_visible (visible := visible)] at atField

/-- **Agreement from the closure's view.** Two configurations reached without
decisions of the deviator, with records classified as in a run, from starting
configurations whose closures look alike to the deviator, and with equal cuts,
accept alike every ready reveal of an active honest owner and store alike the
binding of every ready reveal that is accepted or the deviator's. -/
theorem run_agree_of_closure (base : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        (serviceGraph setup mode).normalizeProfile base owner event actor
          ((serviceGraph setup mode).playerObserve owner config) active =
          PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store)))
    (independent : ReadyIndependent ((serviceGraph setup mode).normalizeProfile base))
    (who : Player) {start finish : Nat}
    {leftOrigin rightOrigin current other : (serviceGraph setup mode).Config}
    (views : keyView who (runKey (closure ((serviceGraph setup mode).normalizeProfile base) who
      leftOrigin)) = keyView who (runKey (closure ((serviceGraph setup mode).normalizeProfile
        base) who rightOrigin)))
    (leftPath : Relation.ReflTransGen Config.Step leftOrigin current)
    (rightPath : Relation.ReflTransGen Config.Step rightOrigin other)
    (leftSound : BlockRecordsSound who start finish leftOrigin current)
    (rightSound : BlockRecordsSound who start finish rightOrigin other)
    (leftQuiet : ∀ event : (serviceGraph setup mode).EventId, event ∉ leftOrigin.cut.completed →
      (serviceGraph setup mode).actor? event = some who →
        ∀ record, completionOf current event = some record → record.decision = none)
    (rightQuiet : ∀ event : (serviceGraph setup mode).EventId,
      event ∉ rightOrigin.cut.completed → (serviceGraph setup mode).actor? event = some who →
        ∀ record, completionOf other event = some record → record.decision = none)
    (cuts : current.cut = other.cut) :
    ∀ (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
    nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq →
    current.cut.Ready event → owner ∉ current.defaulted → owner ∉ other.defaulted →
    (owner ≠ who → openingAccepted event current.store = openingAccepted event other.store) ∧
    (openingAccepted event current.store = true ∨ owner = who →
      binding.get? current.store = binding.get? other.store) := by
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  have leftKey := run_path_closure_settles base decides independent who leftSound leftQuiet
    current leftPath .refl
  have rightKey := run_path_closure_settles base decides independent who rightSound rightQuiet
    other rightPath .refl
  have visibleStores (field : G.Field) (visible : G.fieldVisibleTo who field) :
      (closure R who current).store field = (closure R who other).store field := by
    exact (congrArg (fun key => key.2.1 field) leftKey).trans
      ((store_visible_of_keyView who views visible).trans
        (congrArg (fun key => key.2.1 field) rightKey).symm)
  have closureStored {config : G.Config} {field : G.Field} (stored : (config.store field).isSome) :
      (closure R who config).store field = config.store field := by
    obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp stored
    rw [Config.Step.path_store_of_some (closure_path R who config) field value found, found]
  intro event owner payload binding checks outputEq codeEq node ready leftActive rightActive
  have otherReady : other.cut.Ready event := cuts ▸ ready
  have footprint := EventCode.readFields_cast outputEq (G.nodes event)
  rw [codeEq] at footprint
  have read : binding.field ∈ (G.nodes event).readFields := by
    rw [← footprint]
    exact Finset.mem_insert_self _ _
  by_cases isWho : owner = who
  · subst isWho
    refine ⟨fun different => (different rfl).elim, fun _ => ?_⟩
    have visibleField : G.fieldVisibleTo owner binding.field := by
      unfold EventGraph.fieldVisibleTo
      rw [binding.layout_eq]
      exact (rfl : owner = owner)
    apply FieldRef.get?_congr
    rw [← closureStored (current.read_available ready read),
      ← closureStored (other.read_available otherReady read)]
    exact visibleStores _ visibleField
  have publication : (G.outputLayout event).IsPublication := by
    rw [outputEq]
    trivial
  have outputs : (closure R who current).outputs event = (closure R who other).outputs event :=
    visibleStores (.inr event) (fieldVisibleTo_of_publication who publication)
  obtain ⟨leftAccepted, leftRejected⟩ := honest_closure_output base decides independent who
    ready node isWho leftActive
  obtain ⟨rightAccepted, rightRejected⟩ := honest_closure_output base decides independent who
    otherReady node isWho rightActive
  have castInj {first second : PublicationResult (L.Val payload)}
      (same : some (cast (congrArg EventField.Value outputEq.symm) first) =
        some (cast (congrArg EventField.Value outputEq.symm) second)) : first = second :=
    (cast_inj _).mp (Option.some.inj same)
  cases leftEq : openingAccepted event current.store <;>
    cases rightEq : openingAccepted event other.store
  · exact ⟨fun _ => rfl, fun opened => by
      rcases opened with opened | same
      · cases opened
      · exact (isWho same).elim⟩
  · obtain ⟨value, _, rightOutput⟩ := rightAccepted rightEq
    have := castInj ((leftRejected leftEq).symm.trans (outputs.trans rightOutput))
    cases this
  · obtain ⟨value, _, leftOutput⟩ := leftAccepted leftEq
    have := castInj (leftOutput.symm.trans (outputs.trans (rightRejected rightEq)))
    cases this
  · obtain ⟨leftValue, leftStored, leftOutput⟩ := leftAccepted leftEq
    obtain ⟨rightValue, rightStored, rightOutput⟩ := rightAccepted rightEq
    have same := castInj (leftOutput.symm.trans (outputs.trans rightOutput))
    cases same
    exact ⟨fun _ => rfl, fun _ => leftStored.trans rightStored.symm⟩

end Vegas
