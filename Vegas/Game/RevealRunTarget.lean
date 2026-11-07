/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealRunAgree
import Vegas.Game.LastOwnedPhase

/-! # The deviator's next reveal in a run

Inside a run of reveals whose earlier events have completed, let `target` be
the deviator's earliest reveal of the run not yet completed. While `target`
is pending, it is the only event of the deviator that can be ready. At the
closure, while the deviator is active, `target` is ready and is the only ready
event: every other event either settles or waits for `target`.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}

/-- **Only the target can be ready for the deviator.** In a run whose earlier
events and whose deviator reveals before `target` have completed, every ready
event of the deviator at a later configuration with `target` pending is
`target`. -/
theorem ready_owned_eq_target (who : Player) (relaxed : RelaxedOrder (serviceGraph setup mode))
    {start finish : Nat} (run : RevealRun (serviceGraph setup mode) start finish)
    {origin : (serviceGraph setup mode).Config}
    (earlier : ∀ event : (serviceGraph setup mode).EventId, event.val < start →
      event ∈ origin.cut.completed)
    (target : (serviceGraph setup mode).EventId)
    (targetOwned : (serviceGraph setup mode).actor? target = some who)
    (targetLate : target.val < finish)
    (before : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < target.val → (serviceGraph setup mode).actor? event = some who →
        event ∈ origin.cut.completed)
    {config : (serviceGraph setup mode).Config}
    (path : Relation.ReflTransGen Config.Step origin config)
    (pending : target ∉ config.cut.completed) {event : (serviceGraph setup mode).EventId}
    (ready : config.cut.Ready event) (owned : (serviceGraph setup mode).actor? event = some who) :
    event = target := by
  let G := serviceGraph setup mode
  have mono := Config.Step.path_completed_mono path
  by_cases early : event.val < start
  · exact (ready.1 (mono (earlier event early))).elim
  push Not at early
  by_cases late : finish ≤ event.val
  · exfalso
    have closing : finish < G.order.eventCount := lt_of_le_of_lt late event.isLt
    let closer : G.EventId := ⟨finish, closing⟩
    have targetBefore : target ∈ G.order.predecessors closer :=
      relaxed.predecessor_of_later_not_publication (run.closed closer rfl)
        (show target.val < closer.val from targetLate)
    rcases Nat.eq_or_lt_of_le late with same | later
    · have equal : event = closer := Fin.ext same.symm
      subst equal
      exact pending (ready.2 targetBefore)
    · have closerDone : closer ∈ config.cut.completed :=
        ready.2 (relaxed.predecessor_of_not_publication (run.closed closer rfl) later)
      exact pending (config.cut.predecessor_closed closerDone targetBefore)
  push Not at late
  rcases Nat.lt_trichotomy event.val target.val with smaller | same | larger
  · exact (ready.1 (mono (before event early smaller owned))).elim
  · exact Fin.ext same
  · exact (pending (ready.2 ((relaxed target event).mpr ⟨larger, fun independent =>
      independent.2.2.2 (targetOwned.trans owned.symm)⟩))).elim

/-- **The target is alone at the closure.** While the deviator is active at a
point of a run whose earlier events and whose deviator reveals before a pending
`target` have completed, `target` is ready at the closure and every ready event
there is `target`. -/
theorem closure_target_alone (base : (serviceGraph setup mode).BehavioralProfile)
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
    (who : Player) (relaxed : RelaxedOrder (serviceGraph setup mode))
    (concurrent : (serviceGraph setup mode).RevealsOnlyConcurrent)
    {start finish : Nat} (run : RevealRun (serviceGraph setup mode) start finish)
    {config : (serviceGraph setup mode).Config}
    (earlier : ∀ event : (serviceGraph setup mode).EventId, event.val < start →
      event ∈ config.cut.completed)
    (target : (serviceGraph setup mode).EventId)
    (targetOwned : (serviceGraph setup mode).actor? target = some who)
    (targetLate : target.val < finish)
    (before : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < target.val → (serviceGraph setup mode).actor? event = some who →
        event ∈ config.cut.completed)
    (active : who ∉ config.defaulted) (pending : target ∉ config.cut.completed) :
    (closure ((serviceGraph setup mode).normalizeProfile base) who config).cut.Ready target ∧
      ∀ event, (closure ((serviceGraph setup mode).normalizeProfile base) who
        config).cut.Ready event → event = target := by
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  have path := closure_path R who config
  have completedIff := closure_completed_iff_target base decides who relaxed run earlier target
    targetOwned targetLate before active pending
  have targetPending : target ∉ (closure R who config).cut.completed := fun done =>
    ((completedIff target).mp done).2 .refl
  have closureActive := (closure_shape R who _ config rfl).2 active
  have closureEarlier : ∀ event : G.EventId, event.val < start →
      event ∈ (closure R who config).cut.completed :=
    fun event early => Config.Step.path_completed_mono path (earlier event early)
  have closureBefore : ∀ event : G.EventId, start ≤ event.val → event.val < target.val →
      G.actor? event = some who → event ∈ (closure R who config).cut.completed :=
    fun event early smaller owned => Config.Step.path_completed_mono path
      (before event early smaller owned)
  refine ⟨⟨targetPending, fun prior member => ?_⟩, fun event ready => ?_⟩
  · have smaller := G.order.predecessor_lt member
    refine (completedIff prior).mpr ⟨lt_trans smaller targetLate, fun depends => ?_⟩
    have cycle := depends.le
    omega
  · by_contra different
    by_cases owned : G.actor? event = some who
    · exact different (ready_owned_eq_target who relaxed run closureEarlier target targetOwned
        targetLate closureBefore .refl targetPending ready owned)
    · have publication : (G.outputLayout event).IsPublication := by
        rcases concurrent (closure R who config).cut ready
            ⟨targetPending, fun prior member => (completedIff prior).mpr
              ⟨lt_trans (G.order.predecessor_lt member) targetLate, fun depends => by
                have := depends.le
                have := G.order.predecessor_lt member
                omega⟩⟩ different with independent | independent
        · exact independent.1
        · exact independent.2.1
      exact closure_quiet R who config event
        (honest_settles base decides who ready publication owned)

section Advance

variable {graph : Vegas.EventGraph Player L}

/-- The closure key after an owned event takes an action from a configuration
of a key where it is ready; the key itself when it takes no action or is ready
at no configuration of the key. -/
def closureAdvance (reference : graph.BehavioralProfile) (who : Player)
    (event : graph.EventId) (owned : graph.actor? event = some who)
    (key : RunKey graph) : Option (graph.Action event) → RunKey graph
  | none => key
  | some action =>
      open scoped Classical in
      if found : ∃ config : graph.Config, runKey config = key ∧ config.cut.Ready event then
        runKey (closure reference who
          (ownedStepped event owned found.choose found.choose_spec.2 action))
      else key

/-- The closure advance from a configuration where the owned event is ready. -/
theorem closureAdvance_runKey {reference : graph.BehavioralProfile} {who : Player}
    (keyed : ∀ {left right : graph.Config}, runKey left = runKey right →
      ∀ event, actionLaw reference left event = actionLaw reference right event)
    (event : graph.EventId) (owned : graph.actor? event = some who) (config : graph.Config)
    (ready : config.cut.Ready event) (action : graph.Action event) :
    closureAdvance reference who event owned (runKey config) (some action) =
      runKey (closure reference who (ownedStepped event owned config ready action)) := by
  have found : ∃ other : graph.Config, runKey other = runKey config ∧ other.cut.Ready event :=
    ⟨config, rfl, ready⟩
  dsimp only [closureAdvance]
  rw [dite_eq_left found]
  have keys : runKey (ownedStepped event owned found.choose found.choose_spec.2 action) =
      runKey (ownedStepped event owned config ready action) := by
    have mapped := step_map_runKey_congr found.choose_spec.1 event found.choose_spec.2 ready
      action
    rw [step_eq_ownedStepped event owned found.choose found.choose_spec.2 action,
      step_eq_ownedStepped event owned config ready action, PMF.pure_map, PMF.pure_map]
      at mapped
    have supports := congrArg PMF.support mapped
    rw [PMF.support_pure, PMF.support_pure] at supports
    exact Set.singleton_eq_singleton_iff.mp supports
  exact closure_runKey_congr keyed _ _ _ rfl keys

/-- Without a configuration of the key where the owned event is ready, the key
does not advance. -/
theorem closureAdvance_of_not_ready {reference : graph.BehavioralProfile} {who : Player}
    (event : graph.EventId) (owned : graph.actor? event = some who) (key : RunKey graph)
    (blocked : ∀ config : graph.Config, runKey config = key → ¬ config.cut.Ready event)
    (choice : Option (graph.Action event)) :
    closureAdvance reference who event owned key choice = key := by
  cases choice with
  | none => rfl
  | some action =>
      dsimp only [closureAdvance]
      rw [dite_eq_right]
      rintro ⟨config, keyEq, ready⟩
      exact blocked config keyEq ready

/-- A completion supported by an owned event's step is the owned step. -/
theorem ownedStepped_eq_of_mem {event : graph.EventId} {who : Player}
    (owned : graph.actor? event = some who) {config next : graph.Config}
    {ready : config.cut.Ready event} {action : graph.Action event}
    (member : next ∈ (config.step event ready action).support) :
    next = ownedStepped event owned config ready action := by
  rw [step_eq_ownedStepped event owned config ready action, PMF.mem_support_pure_iff] at member
  exact member

end Advance

/-- A recorded own decision is read from the normalized view. -/
theorem observedAction_of_record {graph : Vegas.EventGraph Player L} {who : Player}
    {config : graph.Config} {event : graph.EventId} (owned : graph.actor? event = some who)
    {action : graph.Action event} {value : (graph.outputLayout event).Value}
    (recorded : completionOf config event =
      some (EventGraph.completion graph event (some action) value)) :
    observedAction event (graph.normalizeObservation who (graph.playerObserve who config)) =
      some action := by
  rw [observedAction_normalize, recorded]
  have keep : (decide (graph.actor? event = some who) && (some action).isSome) = true := by
    simp only [owned, decide_true, Option.isSome_some, Bool.and_self]
  simp only [Option.filter_some, EventGraph.completion, keep, ite_true, Option.bind_some,
    Bool.decide_and, Bool.decide_eq_true]
  exact recordAction_completion event (some action) value

/-- **The end of a step to the deviator's next reveal.** On a path from a point
of a run to a configuration where `target` has completed, with records
classified as in a run and a decision of the deviator only at `target`, the
closure's key at the end is the closure advance of the starting closure's key
by the deviator's observed action at `target`. -/
theorem targetStep_end (base : (serviceGraph setup mode).BehavioralProfile)
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
    (who : Player) {start finish : Nat} (run : RevealRun (serviceGraph setup mode) start finish)
    {origin final : (serviceGraph setup mode).Config}
    (path : Relation.ReflTransGen Config.Step origin final)
    (sound : BlockRecordsSound who start finish origin final)
    (target : (serviceGraph setup mode).EventId)
    (targetOwned : (serviceGraph setup mode).actor? target = some who)
    (decided : DecidesOnly who origin (· = target) final)
    (earlier : ∀ event : (serviceGraph setup mode).EventId, event.val < start →
      event ∈ origin.cut.completed)
    (targetLate : target.val < finish)
    (before : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < target.val → (serviceGraph setup mode).actor? event = some who →
        event ∈ origin.cut.completed)
    (activePending : who ∉ origin.defaulted → target ∉ origin.cut.completed)
    (done : target ∈ final.cut.completed) :
    runKey (closure ((serviceGraph setup mode).normalizeProfile base) who final) =
      closureAdvance ((serviceGraph setup mode).normalizeProfile base) who target targetOwned
        (runKey (closure ((serviceGraph setup mode).normalizeProfile base) who origin))
        (observedAction target ((serviceGraph setup mode).normalizeObservation who
          ((serviceGraph setup mode).playerObserve who final))) := by
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  by_cases active : who ∉ origin.defaulted
  · have pending := activePending active
    obtain ⟨ready, action, value, supported, recorded, key⟩ :=
      (run_path_closure base decides independent who sound target targetOwned
        (fun event different fresh mine => decided event different fresh mine) active pending
        final path .refl).2 done
    rw [observedAction_of_record targetOwned recorded,
      closureAdvance_runKey independent.congr target targetOwned _ ready action,
      ← ownedStepped_eq_of_mem targetOwned supported]
    exact key
  · push Not at active
    have quiet : ∀ event : G.EventId, event ∉ origin.cut.completed →
        G.actor? event = some who →
          ∀ record, completionOf final event = some record → record.decision = none := by
      intro event fresh mine record found
      by_cases same : event = target
      · subst same
        have doneEvent : event ∈ final.cut.completed := done
        obtain ⟨middle, next, readyMiddle, action, walked, member, rest⟩ :=
          path_new_event path fresh doneEvent
        obtain ⟨value, _, stepRecord⟩ := step_record_path member rest
        rw [stepRecord] at found
        cases found
        have inactive : who ∈ middle.defaulted :=
          Config.Step.path_defaulted_mono walked active
        have ownedNode : (G.nodes event).actor = some who := targetOwned
        unfold Config.actualDecision
        rw [EventCode.actualDecision_of_defaulted _ _ who ownedNode inactive]
        rfl
      · exact decided event same fresh mine record found
    rw [run_path_closure_settles base decides independent who sound quiet final path .refl]
    symm
    apply closureAdvance_of_not_ready
    intro config keyEq ready
    have completedTarget : target ∈ (closure R who origin).cut.completed :=
      closure_completes_done base decides who run earlier
        (fun _ _ _ _ => Or.inr active) target targetLate
    have cuts : config.cut = (closure R who origin).cut := congrArg Prod.fst keyEq
    exact ready.1 (cuts ▸ completedTarget)

omit [DecidableEq Player] in
/-- A configuration is the restriction of its successors to a set equal to its
completed events. -/
theorem Config.restrictionOf_of_completed {graph : Vegas.EventGraph Player L} [DecidableEq Player]
    {before after : graph.Config} {done : Finset graph.EventId}
    (same : before.cut.completed = done) (path : Relation.ReflTransGen Config.Step before after) :
    before.RestrictionOf (fun event => event ∈ done) after := by
  subst same
  exact Config.restrictionOf_completed_path path

/-- An event of a defaulted player completed along a path records no decision. -/
theorem record_silent_of_defaulted {who : Player}
    {before after : (serviceGraph setup mode).Config}
    (path : Relation.ReflTransGen Config.Step before after)
    (inactive : who ∈ before.defaulted) {event : (serviceGraph setup mode).EventId}
    (owned : (serviceGraph setup mode).actor? event = some who)
    (fresh : event ∉ before.cut.completed) {record : (serviceGraph setup mode).Completion}
    (found : completionOf after event = some record) :
    record.decision = none := by
  have done : event ∈ after.cut.completed := (completionOf_isSome_iff after event).mp (by
    rw [found]; rfl)
  obtain ⟨middle, next, ready, action, walked, member, rest⟩ := path_new_event path fresh done
  obtain ⟨value, _, recorded⟩ := step_record_path member rest
  rw [recorded] at found
  cases found
  have ownedNode : ((serviceGraph setup mode).nodes event).actor = some who := owned
  unfold Config.actualDecision
  rw [EventCode.actualDecision_of_defaulted _ _ who ownedNode
    (Config.Step.path_defaulted_mono walked inactive)]
  rfl

/-- An own decision is observed only when recorded with a decision. -/
theorem observedAction_eq_none_of_silent {graph : Vegas.EventGraph Player L} {who : Player}
    {config : graph.Config} {event : graph.EventId}
    (silent : ∀ record, completionOf config event = some record → record.decision = none) :
    observedAction event (graph.normalizeObservation who (graph.playerObserve who config)) =
      none := by
  rw [observedAction_normalize]
  cases found : completionOf config event with
  | none => rfl
  | some record =>
      have quiet := silent record found
      simp [Option.filter_some, quiet]

/-- A completed event's observed own decision is kept by the closure. -/
theorem observedAction_closure {graph : Vegas.EventGraph Player L}
    (reference : graph.BehavioralProfile) (who : Player) {config : graph.Config}
    {event : graph.EventId} (done : event ∈ config.cut.completed) :
    observedAction event (graph.normalizeObservation who (graph.playerObserve who
      (closure reference who config))) =
      observedAction event (graph.normalizeObservation who (graph.playerObserve who config)) := by
  rw [observedAction_normalize, observedAction_normalize]
  obtain ⟨record, found⟩ := Option.isSome_iff_exists.mp
    ((completionOf_isSome_iff config event).mpr done)
  rw [Config.Step.path_completionOf_of_some (closure_path reference who config) event record
    found, found]

/-- Observed own decisions are read from the key's view. -/
theorem observedAction_of_keyView {graph : Vegas.EventGraph Player L} (who : Player)
    {left right : graph.Config} (views : keyView who (runKey left) = keyView who (runKey right))
    (event : graph.EventId) :
    observedAction event (graph.normalizeObservation who (graph.playerObserve who left)) =
      observedAction event (graph.normalizeObservation who (graph.playerObserve who right)) := by
  rw [keyView_runKey, keyView_runKey] at views
  rw [Option.some.inj views]

/-- Once the deviator has defaulted at a point of a run, the closure advance at
its next reveal keeps the closure's key. -/
theorem closureAdvance_of_defaulted (base : (serviceGraph setup mode).BehavioralProfile)
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
    (who : Player) {start finish : Nat} (run : RevealRun (serviceGraph setup mode) start finish)
    {config : (serviceGraph setup mode).Config}
    (earlier : ∀ event : (serviceGraph setup mode).EventId, event.val < start →
      event ∈ config.cut.completed)
    (inactive : who ∈ config.defaulted) (target : (serviceGraph setup mode).EventId)
    (targetOwned : (serviceGraph setup mode).actor? target = some who)
    (targetLate : target.val < finish) (choice : Option ((serviceGraph setup mode).Action target)) :
    closureAdvance ((serviceGraph setup mode).normalizeProfile base) who target targetOwned
      (runKey (closure ((serviceGraph setup mode).normalizeProfile base) who config)) choice =
      runKey (closure ((serviceGraph setup mode).normalizeProfile base) who config) := by
  apply closureAdvance_of_not_ready
  intro other keyEq ready
  have completedTarget := closure_completes_done base decides who run earlier
    (fun _ _ _ _ => Or.inr inactive) target targetLate
  have cuts := congrArg Prod.fst keyEq
  exact ready.1 (by
    change target ∈ other.cut.completed
    rw [show other.cut = _ from cuts]
    exact completedTarget)

/-- **Reflection through a step to the deviator's next reveal.** When the ends
of two such steps have closures that look alike to the deviator, so did their
starts. -/
theorem targetStep_reflect (base : (serviceGraph setup mode).BehavioralProfile)
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
    (who : Player) (relaxed : RelaxedOrder (serviceGraph setup mode))
    {start finish : Nat} (run : RevealRun (serviceGraph setup mode) start finish)
    (target : (serviceGraph setup mode).EventId)
    (targetOwned : (serviceGraph setup mode).actor? target = some who)
    (targetLate : target.val < finish)
    {leftOrigin leftFinal rightOrigin rightFinal : (serviceGraph setup mode).Config}
    (leftPath : Relation.ReflTransGen Config.Step leftOrigin leftFinal)
    (rightPath : Relation.ReflTransGen Config.Step rightOrigin rightFinal)
    (leftSound : BlockRecordsSound who start finish leftOrigin leftFinal)
    (rightSound : BlockRecordsSound who start finish rightOrigin rightFinal)
    (leftDecided : DecidesOnly who leftOrigin (· = target) leftFinal)
    (rightDecided : DecidesOnly who rightOrigin (· = target) rightFinal)
    (leftEarlier : ∀ event : (serviceGraph setup mode).EventId, event.val < start →
      event ∈ leftOrigin.cut.completed)
    (rightEarlier : ∀ event : (serviceGraph setup mode).EventId, event.val < start →
      event ∈ rightOrigin.cut.completed)
    (leftBefore : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < target.val → (serviceGraph setup mode).actor? event = some who →
        event ∈ leftOrigin.cut.completed)
    (rightBefore : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < target.val → (serviceGraph setup mode).actor? event = some who →
        event ∈ rightOrigin.cut.completed)
    (leftPending : who ∉ leftOrigin.defaulted → target ∉ leftOrigin.cut.completed)
    (rightPending : who ∉ rightOrigin.defaulted → target ∉ rightOrigin.cut.completed)
    (leftSilent : ∀ record, completionOf leftOrigin target = some record →
      record.decision = none)
    (rightSilent : ∀ record, completionOf rightOrigin target = some record →
      record.decision = none)
    (leftDone : target ∈ leftFinal.cut.completed) (rightDone : target ∈ rightFinal.cut.completed)
    (views : keyView who (runKey (closure ((serviceGraph setup mode).normalizeProfile base) who
      leftFinal)) = keyView who (runKey (closure ((serviceGraph setup mode).normalizeProfile
        base) who rightFinal))) :
    keyView who (runKey (closure ((serviceGraph setup mode).normalizeProfile base) who
      leftOrigin)) = keyView who (runKey (closure ((serviceGraph setup mode).normalizeProfile
        base) who rightOrigin)) := by
  classical
  let G := serviceGraph setup mode
  let R := G.normalizeProfile base
  have observed : observedAction target (G.normalizeObservation who (G.playerObserve who
      leftFinal)) = observedAction target (G.normalizeObservation who (G.playerObserve who
        rightFinal)) := by
    rw [← observedAction_closure R who leftDone, ← observedAction_closure R who rightDone]
    exact observedAction_of_keyView who views target
  -- the deviator's own action at the target when it was active
  have activeObserved {origin final : G.Config}
      (path : Relation.ReflTransGen Config.Step origin final)
      (sound : BlockRecordsSound who start finish origin final)
      (decided : DecidesOnly who origin (· = target) final) (active : who ∉ origin.defaulted)
      (pending : target ∉ origin.cut.completed) (done : target ∈ final.cut.completed) :
      ∃ (ready : (closure R who origin).cut.Ready target) (action : G.Action target)
        (value : (G.outputLayout target).Value),
        (closure R who origin).complete target ready action value ∈
          ((closure R who origin).step target ready action).support ∧
        observedAction target (G.normalizeObservation who (G.playerObserve who final)) =
          some action ∧
        runKey (closure R who final) = runKey (closure R who
          ((closure R who origin).complete target ready action value)) := by
    obtain ⟨ready, action, value, supported, recorded, key⟩ :=
      (run_path_closure base decides independent who sound target targetOwned
        (fun event different fresh mine => decided event different fresh mine) active pending
        final path .refl).2 done
    exact ⟨ready, action, value, supported, observedAction_of_record targetOwned recorded, key⟩
  have inactiveObserved {origin final : G.Config}
      (path : Relation.ReflTransGen Config.Step origin final) (inactive : who ∈ origin.defaulted)
      (silent : ∀ record, completionOf origin target = some record → record.decision = none) :
      observedAction target (G.normalizeObservation who (G.playerObserve who final)) = none := by
    apply observedAction_eq_none_of_silent
    intro record found
    by_cases old : target ∈ origin.cut.completed
    · obtain ⟨previous, previousFound⟩ := Option.isSome_iff_exists.mp
        ((completionOf_isSome_iff origin target).mpr old)
      rw [Config.Step.path_completionOf_of_some path target previous previousFound] at found
      cases found
      exact silent _ previousFound
    · exact record_silent_of_defaulted path inactive targetOwned old found
  have inactiveKey {origin final : G.Config}
      (path : Relation.ReflTransGen Config.Step origin final)
      (sound : BlockRecordsSound who start finish origin final)
      (decided : DecidesOnly who origin (· = target) final)
      (earlier : ∀ event : G.EventId, event.val < start → event ∈ origin.cut.completed)
      (before : ∀ event : G.EventId, start ≤ event.val → event.val < target.val →
        G.actor? event = some who → event ∈ origin.cut.completed)
      (pending : who ∉ origin.defaulted → target ∉ origin.cut.completed)
      (done : target ∈ final.cut.completed) (inactive : who ∈ origin.defaulted) :
      runKey (closure R who final) = runKey (closure R who origin) := by
    rw [targetStep_end base decides independent who run path sound target targetOwned decided
      earlier targetLate before pending done]
    exact closureAdvance_of_defaulted base decides who run earlier inactive target targetOwned
      targetLate _
  by_cases leftActive : who ∉ leftOrigin.defaulted <;>
    by_cases rightActive : who ∉ rightOrigin.defaulted
  · have leftPend := leftPending leftActive
    have rightPend := rightPending rightActive
    obtain ⟨leftReady, leftAction, leftValue, leftSupported, _, leftKey⟩ :=
      activeObserved leftPath leftSound leftDecided leftActive leftPend leftDone
    obtain ⟨rightReady, rightAction, rightValue, rightSupported, _, rightKey⟩ :=
      activeObserved rightPath rightSound rightDecided rightActive rightPend rightDone
    have sets : (closure R who rightOrigin).cut.completed =
        (closure R who leftOrigin).cut.completed := by
      ext event
      rw [closure_completed_iff_target base decides who relaxed run rightEarlier target
          targetOwned targetLate rightBefore rightActive rightPend event,
        closure_completed_iff_target base decides who relaxed run leftEarlier target
          targetOwned targetLate leftBefore leftActive leftPend event]
    have pathOf (origin : G.Config) (ready : (closure R who origin).cut.Ready target)
        (action : G.Action target) (value : (G.outputLayout target).Value)
        (supported : (closure R who origin).complete target ready action value ∈
          ((closure R who origin).step target ready action).support) :
        Relation.ReflTransGen Config.Step (closure R who origin)
          (closure R who ((closure R who origin).complete target ready action value)) :=
      Relation.ReflTransGen.head ⟨target, ready, action, supported⟩ (closure_path R who _)
    have restrictedLeft := Config.restrictionOf_of_completed rfl
      (pathOf leftOrigin leftReady leftAction leftValue leftSupported)
    have restrictedRight := Config.restrictionOf_of_completed sets
      (pathOf rightOrigin rightReady rightAction rightValue rightSupported)
    have ends : G.normalizeObservation who (G.playerObserve who (closure R who
        ((closure R who leftOrigin).complete target leftReady leftAction leftValue))) =
        G.normalizeObservation who (G.playerObserve who (closure R who
          ((closure R who rightOrigin).complete target rightReady rightAction rightValue))) := by
      have endViews := views
      rw [leftKey, rightKey, keyView_runKey, keyView_runKey] at endViews
      exact Option.some.inj endViews
    rw [keyView_runKey, keyView_runKey, normalizeObservation_playerObserve_restrict who _
      restrictedLeft restrictedRight ends]
  · push Not at rightActive
    obtain ⟨_, leftAction, _, _, leftObserved, _⟩ :=
      activeObserved leftPath leftSound leftDecided leftActive (leftPending leftActive) leftDone
    rw [leftObserved, inactiveObserved rightPath rightActive rightSilent] at observed
    cases observed
  · push Not at leftActive
    obtain ⟨_, rightAction, _, _, rightObserved, _⟩ := activeObserved rightPath rightSound
      rightDecided rightActive (rightPending rightActive) rightDone
    rw [rightObserved, inactiveObserved leftPath leftActive leftSilent] at observed
    cases observed
  · push Not at leftActive rightActive
    rw [← inactiveKey leftPath leftSound leftDecided leftEarlier leftBefore leftPending leftDone
        leftActive,
      ← inactiveKey rightPath rightSound rightDecided rightEarlier rightBefore rightPending
        rightDone rightActive]
    exact views

end Vegas
