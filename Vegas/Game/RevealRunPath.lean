/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealRunClosure

/-! # The closure along a run of reveals

Along a graph path whose new records are classified as in a run of
concurrent reveals (automatic, the deviator's, an honest accepted opening, or
an honest expired rejected opening), every step either settles its event, with
the reference's determined action, or records a decision of the active
deviator. So when the only decision the deviator records on the path is at
`target`, the closure's key is fixed until `target` completes, and afterwards is
the closure after completing `target` from the starting closure.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}

/-- A step whose new record is recorded at a later configuration. -/
theorem step_record_path {before after final : (serviceGraph setup mode).Config}
    {event : (serviceGraph setup mode).EventId} {ready : before.cut.Ready event}
    {action : (serviceGraph setup mode).Action event}
    (member : after ∈ (before.step event ready action).support)
    (path : Relation.ReflTransGen Config.Step after final) :
    ∃ value, after = before.complete event ready action value ∧
      completionOf final event = some (EventGraph.completion (serviceGraph setup mode) event
        (before.actualDecision event action) value) := by
  have stepped := member
  rw [Config.step, PMF.support_map] at stepped
  obtain ⟨value, _, rfl⟩ := stepped
  refine ⟨value, rfl, Config.Step.path_completionOf_of_some path event _ ?_⟩
  rw [completionOf_complete, Function.update_self]

/-- **A step of a run settles, or records a decision of the active deviator.**
On a path whose new records are classified as in a run of concurrent reveals,
under a reference whose honest owners open a reveal exactly when its opening is
accepted, each step completing a new event is the settling of that event, or
records a decision at an event of the deviator. -/
theorem run_step_settles (base : (serviceGraph setup mode).BehavioralProfile)
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
    (who : Player) {start finish : Nat}
    {origin before after final : (serviceGraph setup mode).Config}
    {event : (serviceGraph setup mode).EventId} {ready : before.cut.Ready event}
    {action : (serviceGraph setup mode).Action event}
    (member : after ∈ (before.step event ready action).support)
    (path : Relation.ReflTransGen Config.Step after final)
    (sound : BlockRecordsSound who start finish origin final)
    (fresh : event ∉ origin.cut.completed) :
    (∃ settles : Settles ((serviceGraph setup mode).normalizeProfile base) who before event,
      after = settled before event settles) ∨
    ((serviceGraph setup mode).actor? event = some who ∧
      before.actualDecision event action ≠ none) := by
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  obtain ⟨value, afterEq, recorded⟩ := step_record_path member path
  have done : event ∈ final.cut.completed :=
    Config.Step.path_completed_mono path (by
      rw [afterEq, Config.complete_cut, EventOrder.Cut.mem_complete]
      exact Or.inl rfl)
  have decisionOf {decision : Option (G.Action event)} {default : Option Player}
      (found : completionOf final event = some ⟨event, decision, default⟩) :
      before.actualDecision event action = decision := by
    rw [recorded] at found
    have records := Option.some.inj found
    simp only [EventGraph.completion, EventCompletion.mk.injEq, true_and, heq_eq_eq] at records
    exact records.1
  -- an owner without a recorded decision was defaulted before the step
  have defaultedOf {owner : Player} (owned : (G.nodes event).actor = some owner)
      (none : before.actualDecision event action = none) : owner ∈ before.defaulted := by
    by_contra active
    have := (EventCode.effectiveAction_of_active _ before.defaulted owner owned active
      action).2
    unfold Config.actualDecision at none
    rw [this] at none
    cases none
  have automatic {owner : Player} (owned : (G.nodes event).actor = some owner)
      (none : before.actualDecision event action = none) :
      ∃ settles : Settles R who before event, after = settled before event settles := by
    have inactive := defaultedOf owned none
    have settles : Settles R who before event := settles_of_defaulted ready owned inactive
    refine ⟨settles, step_eq_settled settles owned member ?_⟩
    unfold Config.actualDecision
    rw [EventCode.actualDecision_of_defaulted _ _ owner owned inactive,
      EventCode.actualDecision_of_defaulted _ _ owner owned inactive]
  have honest {owner : Player} {payload : L.Ty}
      {binding : FieldRef G.layout (.binding owner payload)}
      {checks : List (GuardCheck G.layout payload)}
      {outputEq : G.outputLayout event = .publication payload}
      {codeEq : cast (congrArg (EventCode G.layout) outputEq) (G.nodes event) =
        .resolve owner payload binding checks}
      (different : owner ≠ who)
      (node : nodeView G event = .resolve owner payload binding checks outputEq codeEq)
      (available : ∀ field ∈ (G.nodes event).readFields, (final.store field).isSome)
      (disclose : Bool) (accepted : openingAccepted event final.store = disclose)
      {default : Option Player}
      (found : completionOf final event =
        some ⟨event, some (cast (congrArg EventField.Action outputEq.symm) disclose), default⟩) :
      ∃ settles : Settles R who before event, after = settled before event settles := by
    have owned := nodeView_resolve_actor outputEq codeEq
    have ownedNode : (G.nodes event).actor = some owner := owned
    have decided := decisionOf found
    have active : owner ∉ before.defaulted := fun inactive => by
      unfold Config.actualDecision at decided
      rw [EventCode.actualDecision_of_defaulted _ _ owner ownedNode inactive] at decided
      cases decided
    have foreign : G.actor? event ≠ some who := fun same => different (Option.some.inj
      (owned.symm.trans same))
    have publication : (G.outputLayout event).IsPublication := by
      rw [outputEq]
      trivial
    have settles := honest_settles base decides who ready publication foreign
    refine ⟨settles, step_eq_settled settles ownedNode member ?_⟩
    obtain ⟨acting, _⟩ := settles.2.2.2.choose_spec.choose_spec
    have kernel : actionLaw R before event = PMF.pure (cast (congrArg EventField.Action
        outputEq.symm) (openingAccepted event before.store)) := by
      rw [actionLaw_of_actor _ _ ownedNode, dite_eq_right active]
      exact decides before event owner payload binding checks outputEq codeEq node owned active
    have chosen : settles.2.2.2.choose = cast (congrArg EventField.Action outputEq.symm)
        (openingAccepted event before.store) := by
      have := acting.symm.trans kernel
      have supports := congrArg PMF.support this
      simpa [PMF.support_pure] using supports
    have readsAvailable : ∀ field ∈ (G.nodes event).readFields, (before.store field).isSome :=
      fun field read => before.read_available ready read
    have stillAccepted : openingAccepted event before.store = disclose := by
      rw [← openingAccepted_path_eq (Relation.ReflTransGen.head ⟨event, ready, action, member⟩
        path) readsAvailable]
      exact accepted
    rw [decided, chosen, stillAccepted]
    unfold Config.actualDecision
    rw [(EventCode.effectiveAction_of_active _ before.defaulted owner ownedNode active _).2]
  rcases sound event fresh done with ⟨silent, _, owner, owned, _⟩ |
    ⟨early, late, mine | opened | expired⟩
  · exact Or.inl (automatic owned (decisionOf silent))
  · by_cases none : before.actualDecision event action = none
    · exact Or.inl (automatic mine none)
    · exact Or.inr ⟨mine, none⟩
  · obtain ⟨owner, payload, binding, checks, outputEq, codeEq, different, node, available,
      accepted, found, _⟩ := opened
    exact Or.inl (honest different node available true accepted found)
  · obtain ⟨owner, payload, binding, checks, outputEq, codeEq, different, node, available,
      accepted, found, _⟩ := expired
    exact Or.inl (honest different node available false accepted found)

/-- A completion supported by one configuration's step is supported by the
step of another configuration where the event is ready, with the same
effective action and the same stored footprint. -/
theorem complete_mem_step_of_agree {graph : Vegas.EventGraph Player L}
    {before other : graph.Config} {event : graph.EventId} {ready : before.cut.Ready event}
    {otherReady : other.cut.Ready event} {action : graph.Action event}
    {value : (graph.outputLayout event).Value}
    (member : before.complete event ready action value ∈ (before.step event ready action).support)
    (effective : other.effectiveAction event action = before.effectiveAction event action)
    (agree : Store.AgreeOn other.store before.store (graph.nodes event).readFields) :
    other.complete event otherReady action value ∈
      (other.step event otherReady action).support := by
  have evaluates : (graph.nodes event).eval? (other.effectiveAction event action) other.store =
      (graph.nodes event).eval? (before.effectiveAction event action) before.store := by
    rw [effective]
    exact EventCode.eval?_congr _ _ _ _ agree
  have available := EventCode.eval?_isSome_of_reads (graph.nodes event)
    (before.effectiveAction event action) before.store
    (fun _ read => before.read_available ready read)
  obtain ⟨law, lawEq⟩ := Option.isSome_iff_exists.mp available
  rw [before.step_eq_map_of_eval event ready action law lawEq, PMF.support_map] at member
  obtain ⟨found, foundMember, foundEq⟩ := member
  have values : found = value := by
    have := congrArg (fun next : graph.Config => next.outputs event) foundEq
    simpa only [Config.complete_output_same, Option.some.injEq] using this
  rw [other.step_eq_map_of_eval event otherReady action law (evaluates.trans lawEq),
    PMF.support_map]
  exact ⟨found, foundMember, by rw [values]⟩

/-- **The closure along a run.** On a path from `origin` whose new records are
classified as in a run of concurrent reveals, where the active deviator records
a decision at no event but `target`, the closure's key stays the starting one
until `target` completes, and afterwards is the key of the closure after
completing `target` from the starting closure with the recorded action and
output. -/
theorem run_path_closure (base : (serviceGraph setup mode).BehavioralProfile)
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
    (target : (serviceGraph setup mode).EventId)
    (targetOwned : (serviceGraph setup mode).actor? target = some who)
    (once : ∀ event : (serviceGraph setup mode).EventId, event ≠ target →
      event ∉ origin.cut.completed → (serviceGraph setup mode).actor? event = some who →
        ∀ record, completionOf final event = some record → record.decision = none)
    (active : who ∉ origin.defaulted) (pending : target ∉ origin.cut.completed) :
    ∀ current : (serviceGraph setup mode).Config,
      Relation.ReflTransGen Config.Step origin current →
      Relation.ReflTransGen Config.Step current final →
      (target ∉ current.cut.completed → who ∉ current.defaulted ∧
        runKey (closure ((serviceGraph setup mode).normalizeProfile base) who current) =
          runKey (closure ((serviceGraph setup mode).normalizeProfile base) who origin)) ∧
      (target ∈ current.cut.completed →
        ∃ (ready : (closure ((serviceGraph setup mode).normalizeProfile base) who
            origin).cut.Ready target)
          (action : (serviceGraph setup mode).Action target)
          (value : ((serviceGraph setup mode).outputLayout target).Value),
          (closure ((serviceGraph setup mode).normalizeProfile base) who origin).complete
              target ready action value ∈
            ((closure ((serviceGraph setup mode).normalizeProfile base) who origin).step
              target ready action).support ∧
          completionOf current target = some (EventGraph.completion (serviceGraph setup mode)
            target (some action) value) ∧
          runKey (closure ((serviceGraph setup mode).normalizeProfile base) who current) =
            runKey (closure ((serviceGraph setup mode).normalizeProfile base) who
              ((closure ((serviceGraph setup mode).normalizeProfile base) who origin).complete
                target ready action value))) := by
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  have targetNode : (G.nodes target).actor = some who := targetOwned
  intro current walked
  induction walked with
  | refl =>
      intro _
      exact ⟨fun _ => ⟨active, rfl⟩, fun done => (pending done).elim⟩
  | @tail before after walked moved ih =>
  intro rest
  have before' := ih (Relation.ReflTransGen.head moved rest)
  obtain ⟨event, ready, action, member⟩ := moved
  have fresh : event ∉ origin.cut.completed := fun done =>
    ready.1 (Config.Step.path_completed_mono walked done)
  obtain ⟨value, afterEq, recorded⟩ := step_record_path member rest
  have decidedContra (different : event ≠ target) (mine : G.actor? event = some who)
      (decided : before.actualDecision event action ≠ none) : False :=
    decided (once event different fresh mine _ recorded)
  have keepRecord : ∀ record, completionOf before target = some record →
      completionOf after target = some record := fun record found =>
    Config.Step.path_completionOf_of_some (.single ⟨event, ready, action, member⟩) target
      record found
  have afterMono : before.cut.completed ⊆ after.cut.completed :=
    Config.Step.completed_mono ⟨event, ready, action, member⟩
  rcases run_step_settles base decides who member rest sound fresh with
    ⟨settles, settledEq⟩ | ⟨mine, decided⟩
  · have closureEq : runKey (closure R who after) = runKey (closure R who before) := by
      rw [settledEq]
      exact closure_settled_runKey independent _ before rfl event settles
    by_cases targetDone : target ∈ before.cut.completed
    · obtain ⟨readyT, actionT, valueT, supported, found, key⟩ := before'.2 targetDone
      exact ⟨fun notDone => (notDone (afterMono targetDone)).elim, fun _ =>
        ⟨readyT, actionT, valueT, supported, keepRecord _ found, closureEq.trans key⟩⟩
    · obtain ⟨whoActive, key⟩ := before'.1 targetDone
      have different : event ≠ target := by
        rintro rfl
        rcases settles.2.2.1 with foreign | defaulted
        · exact foreign targetOwned
        · exact whoActive defaulted
      have stillPending : target ∉ after.cut.completed := by
        rw [settledEq]
        unfold settled
        rw [Config.complete_cut, EventOrder.Cut.mem_complete]
        rintro (same | old)
        · exact different same.symm
        · exact targetDone old
      refine ⟨fun _ => ⟨?_, closureEq.trans key⟩, fun done => (stillPending done).elim⟩
      rw [settledEq]
      exact ((settled_shape settles).2 whoActive).2
  · by_cases targetDone : target ∈ before.cut.completed
    · have different : event ≠ target := fun same => ready.1 (same ▸ targetDone)
      exact (decidedContra different mine decided).elim
    obtain ⟨whoActive, key⟩ := before'.1 targetDone
    by_cases different : event ≠ target
    · exact (decidedContra different mine decided).elim
    push Not at different
    subst different
    have actual : before.actualDecision event action = some action :=
      (EventCode.effectiveAction_of_active _ before.defaulted who targetNode whoActive action).2
    have closurePath := closure_path R who before
    have readyClosure : (closure R who before).cut.Ready event := by
      refine ⟨fun done => ?_, fun prior member =>
        Config.Step.path_completed_mono closurePath (ready.2 member)⟩
      exact ((closure_shape R who _ before rfl).1 event done ready.1).2 whoActive targetOwned
    have cuts : (closure R who before).cut = (closure R who origin).cut :=
      congrArg Prod.fst key
    have stores : (closure R who before).store = (closure R who origin).store :=
      congrArg (fun key => key.2.1) key
    have records : completionOf (closure R who before) = completionOf (closure R who origin) :=
      congrArg (fun key => key.2.2) key
    have readyOrigin : (closure R who origin).cut.Ready event := cuts ▸ readyClosure
    have originActive : who ∉ (closure R who origin).defaulted := by
      rw [← defaulted_eq_of_completionOf_eq records]
      exact (closure_shape R who _ before rfl).2 whoActive
    have absorbed := closure_complete_runKey independent _ before rfl event ready targetOwned
      whoActive action value readyClosure
    have congruent : runKey (closure R who ((closure R who before).complete event readyClosure
        action value)) = runKey (closure R who ((closure R who origin).complete event readyOrigin
          action value)) :=
      closure_runKey_congr independent.congr _ _ _ rfl
        (runKey_complete_congr key event readyClosure readyOrigin action value)
    have supported : (closure R who origin).complete event readyOrigin action value ∈
        ((closure R who origin).step event readyOrigin action).support := by
      refine complete_mem_step_of_agree (afterEq ▸ member) ?_ ?_
      · unfold Config.effectiveAction
        rw [(EventCode.effectiveAction_of_active _ _ who targetNode originActive action).1,
          (EventCode.effectiveAction_of_active _ _ who targetNode whoActive action).1]
      · intro field read
        rw [← stores]
        obtain ⟨stored, found⟩ := Option.isSome_iff_exists.mp (before.read_available ready read)
        rw [Config.Step.path_store_of_some closurePath field stored found, found]
    refine ⟨fun notDone => (notDone ?_).elim, fun _ =>
      ⟨readyOrigin, action, value, supported, ?_, ?_⟩⟩
    · rw [afterEq, Config.complete_cut, EventOrder.Cut.mem_complete]
      exact Or.inl rfl
    · rw [afterEq, completionOf_complete, Function.update_self, actual]
    · rw [afterEq, absorbed, congruent]

end Vegas
