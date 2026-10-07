/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceBlockCongruence
import Vegas.Compile.EventGraphStep
import Mathlib.Logic.Relation

/-! # What a block run leaves behind

A run of rounds changes the configuration only by completing ready events, one
at a time (`Vegas.ConfigReaches`). Along such a run the history only grows, a
completed event keeps its output, and a completed binding stores exactly the
value its action binds (`Vegas.ConfigReaches.binding_output`). On a
reveal-relaxed graph one owner's bindings complete in source order
(`Vegas.ConfigReaches.binding_order`), and while one of its bindings is ready
exactly its earlier bindings have completed (`Vegas.binding_completed_iff`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}

/-- A configuration reached from another by completing ready events, one at a
time. -/
def ConfigReaches (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    (before after : (serviceGraph setup mode).Config) : Prop :=
  Relation.ReflTransGen (ConfigStep setup) before after

/-- Stopped rounds reach their stopping configuration. -/
theorem runUntil_configReaches {deadline : (serviceGraph setup mode).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy)
    (stop : (serviceApplication setup mode deadline leaks).Execution → Prop) [DecidablePred stop] :
    ∀ (count : Nat) (execution stopped : (serviceApplication setup mode deadline leaks).Execution),
      stopped ∈ ((serviceApplication setup mode deadline leaks).runUntil scheduler players stop
        count execution).support →
      ConfigReaches setup execution.application.config stopped.application.config := by
  intro count
  induction count with
  | zero =>
      intro execution stopped reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact Relation.ReflTransGen.refl
  | succ count ih =>
      intro execution stopped reached
      by_cases halt : stop execution
      · rw [ReactiveApplication.runUntil_of_stop _ _ _ _ _ execution halt] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact Relation.ReflTransGen.refl
      · simp only [ReactiveApplication.runUntil, halt, ↓reduceIte] at reached
        obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
        exact Relation.ReflTransGen.head
          (round_configStep setup leaks scheduler players execution middle moved)
          (ih middle stopped rest)

/-- A configuration step completes its event with some output. -/
theorem step_complete_of_mem {config next : (serviceGraph setup mode).Config}
    {event : (serviceGraph setup mode).EventId} {ready : config.cut.Ready event}
    {action : (serviceGraph setup mode).Action event}
    (member : next ∈ (config.step event ready action).support) :
    ∃ value, next = config.complete event ready action value := by
  unfold EventGraph.Config.step at member
  rw [PMF.support_map] at member
  obtain ⟨value, _, rfl⟩ := member
  exact ⟨value, rfl⟩

/-- A configuration step of a binding stores the value its action binds. -/
theorem step_binding_output {config next : (serviceGraph setup mode).Config}
    {event : (serviceGraph setup mode).EventId} {ready : config.cut.Ready event}
    {action : (serviceGraph setup mode).Action event} {owner : Player} {payload : L.Ty}
    {outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .bind owner payload}
    (member : next ∈ (config.step event ready action).support) :
    next.outputs event = some (cast (congrArg EventGraph.EventField.Value outputEq.symm)
      (cast (congrArg EventGraph.EventField.Action outputEq) action)) := by
  have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
      (cast (congrArg EventGraph.EventField.Action outputEq) action) := by
    simp only [cast_cast, cast_eq]
  rw [actionEq, commit_step config event ready outputEq codeEq _,
    PMF.mem_support_pure_iff] at member
  rw [member]
  exact EventGraph.Config.complete_output_same _ _ _ _ _

namespace ConfigReaches

variable {before after : (serviceGraph setup mode).Config}

/-- The history only grows. -/
theorem history_prefix (reach : ConfigReaches setup before after) :
    before.history <+: after.history := by
  induction reach with
  | refl => exact List.prefix_refl _
  | tail _ step ih =>
      rcases step with same | ⟨event, ready, action, member⟩
      · rw [same]
        exact ih
      · rw [EventGraph.Config.step_history _ event ready action _ member]
        exact ih.trans (List.prefix_append _ _)

/-- A completed event stays completed and keeps its output. -/
theorem output_completed (reach : ConfigReaches setup before after)
    {event : (serviceGraph setup mode).EventId} (done : event ∈ before.cut.completed) :
    event ∈ after.cut.completed ∧ after.outputs event = before.outputs event := by
  induction reach with
  | refl => exact ⟨done, rfl⟩
  | tail _ step ih =>
      obtain ⟨middleDone, middleOutput⟩ := ih
      rcases step with same | ⟨other, ready, action, member⟩
      · rw [same]
        exact ⟨middleDone, middleOutput⟩
      · obtain ⟨value, rfl⟩ := step_complete_of_mem member
        have different : event ≠ other := fun equal => ready.1 (equal ▸ middleDone)
        refine ⟨?_, ?_⟩
        · rw [EventGraph.Config.complete_cut, EventOrder.Cut.mem_complete]
          exact Or.inr middleDone
        · rw [EventGraph.Config.complete_output_of_ne _ _ _ _ _ _ different]
          exact middleOutput

/-- A binding completed along the run stores the value its action binds. -/
theorem binding_output (reach : ConfigReaches setup before after)
    {completion : (serviceGraph setup mode).Completion}
    (member : completion ∈ after.history) (fresh : completion ∉ before.history)
    {owner : Player} {payload : L.Ty}
    (outputEq : (serviceGraph setup mode).outputLayout completion.event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes completion.event) = .bind owner payload) :
    after.outputs completion.event = some (cast (congrArg EventGraph.EventField.Value
      outputEq.symm)
          (cast (congrArg EventGraph.EventField.Action outputEq) completion.action)) := by
  induction reach with
  | refl => exact (fresh member).elim
  | tail earlier step ih =>
      rename_i middle current
      rcases step with same | ⟨other, ready, action, stepped⟩
      · subst same
        exact ih member
      · rw [EventGraph.Config.step_history _ other ready action _ stepped] at member
        rcases List.mem_append.mp member with old | new
        · have done : completion.event ∈ middle.cut.completed :=
            (middle.history_exact completion.event).mp (List.mem_map_of_mem old)
          have kept := ConfigReaches.output_completed
            (Relation.ReflTransGen.single (Or.inr ⟨other, ready, action, stepped⟩) :
              ConfigReaches setup middle current) done
          rw [kept.2]
          exact ih old
        · rw [List.mem_singleton] at new
          subst new
          exact step_binding_output (outputEq := outputEq) (codeEq := codeEq) stepped

end ConfigReaches

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem sameBindingOwner_symm {left right : EventGraph.EventField Player L}
    (same : left.SameBindingOwner right) : right.SameBindingOwner left := by
  cases left <;> cases right <;> simp_all [EventGraph.EventField.SameBindingOwner]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A field sharing a binding owner is a binding, not a publication. -/
theorem not_publication_of_sameBindingOwner {left right : EventGraph.EventField Player L}
    (same : left.SameBindingOwner right) : ¬ left.IsPublication := by
  cases left <;> cases right <;> simp_all [EventGraph.EventField.SameBindingOwner,
    EventGraph.EventField.IsPublication]

/-- A run of rounds followed by one more step. -/
theorem ConfigReaches.trans_single {before middle after : (serviceGraph setup mode).Config}
    (reach : ConfigReaches setup before middle) (step : ConfigStep setup middle after) :
    ConfigReaches setup before after :=
  Relation.ReflTransGen.tail reach step

/-- **One owner's bindings complete in source order.** On a reveal-relaxed
graph, among the completions a run appends, a binding precedes every later
binding of the same owner in rank. -/
theorem ConfigReaches.binding_order (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {before after : (serviceGraph setup mode).Config} (reach : ConfigReaches setup before after) :
    (after.history.drop before.history.length).Pairwise fun first second =>
      ((serviceGraph setup mode).outputLayout first.event).SameBindingOwner
        ((serviceGraph setup mode).outputLayout second.event) →
        first.event.val < second.event.val := by
  induction reach with
  | refl => simp
  | tail earlier step ih =>
      rename_i middle current
      have prefixed := ConfigReaches.history_prefix earlier
      rcases step with same | ⟨event, ready, action, stepped⟩
      · subst same
        exact ih
      · rw [EventGraph.Config.step_history _ event ready action _ stepped,
          List.drop_append_of_le_length prefixed.length_le]
        refine List.pairwise_append.mpr ⟨ih, List.pairwise_singleton _ _, ?_⟩
        intro first firstMember second secondMember sameOwner
        rw [List.mem_singleton] at secondMember
        subst secondMember
        have firstDone : first.event ∈ middle.cut.completed :=
          (middle.history_exact first.event).mp
            (List.mem_map_of_mem (List.mem_of_mem_drop firstMember))
        by_contra notBelow
        change ¬ first.event.val < event.val at notBelow
        have different : first.event ≠ event := fun equal => ready.1 (equal ▸ firstDone)
        have lower : event.val < first.event.val := by
          have : event.val ≠ first.event.val := fun equal => different (Fin.ext equal).symm
          omega
        have barrier := EventGraph.barrierOrder_same_owner (serviceGraph setup mode).outputLayout
          lower (sameBindingOwner_symm sameOwner)
        exact ready.1 (middle.cut.predecessor_closed firstDone
          (relaxed.keeps barrier (Or.inr (not_publication_of_sameBindingOwner sameOwner))))

/-- **While a binding is ready, exactly its owner's earlier bindings have
completed.** On a reveal-relaxed graph, at a cut where a binding of `owner` is
ready, another binding of `owner` has completed exactly when it is earlier. -/
theorem binding_completed_iff (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {cut : (serviceGraph setup mode).order.Cut} {event other : (serviceGraph setup mode).EventId}
    (ready : cut.Ready event) {owner : Player} {payload otherPayload : L.Ty}
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (otherEq : (serviceGraph setup mode).outputLayout other = .binding owner otherPayload) :
    other ∈ cut.completed ↔ other.val < event.val := by
  constructor
  · intro done
    by_contra notBelow
    rcases Nat.lt_or_ge event.val other.val with lower | upper
    · have barrier := EventGraph.barrierOrder_same_owner (serviceGraph setup mode).outputLayout
        lower (by rw [outputEq, otherEq]; rfl)
      exact ready.1 (cut.predecessor_closed done (relaxed.keeps barrier
        (Or.inl (by rw [outputEq]; simp [EventGraph.EventField.IsPublication]))))
    · have same : other = event := Fin.ext (by omega)
      exact ready.1 (same ▸ done)
  · intro lower
    have barrier := EventGraph.barrierOrder_same_owner (serviceGraph setup mode).outputLayout
      lower (by rw [outputEq, otherEq]; rfl)
    exact ready.2 (relaxed.keeps barrier
      (Or.inl (by rw [otherEq]; simp [EventGraph.EventField.IsPublication])))

/-- Two completions of one event in a history are equal. -/
theorem completion_eq_of_event {config : (serviceGraph setup mode).Config}
    {first second : (serviceGraph setup mode).Completion}
    (firstMember : first ∈ config.history) (secondMember : second ∈ config.history)
    (same : first.event = second.event) : first = second :=
  List.inj_on_of_nodup_map config.history_nodup firstMember secondMember same

namespace ConfigReaches

variable {before after : (serviceGraph setup mode).Config}

/-- The inputs never change. -/
theorem inputs (reach : ConfigReaches setup before after) : after.inputs = before.inputs := by
  induction reach with
  | refl => rfl
  | tail _ step ih =>
      rcases step with same | ⟨event, ready, action, member⟩
      · rw [same]
        exact ih
      · obtain ⟨value, rfl⟩ := step_complete_of_mem member
        exact ih

/-- A completion of the later history whose event was not completed before was
appended by the run. -/
theorem mem_drop_iff (reach : ConfigReaches setup before after)
    (completion : (serviceGraph setup mode).Completion) :
    completion ∈ after.history.drop before.history.length ↔
      completion ∈ after.history ∧ completion.event ∉ before.cut.completed := by
  obtain ⟨appended, split⟩ := reach.history_prefix
  have nodup := after.history_nodup
  rw [← split, List.map_append, List.nodup_append] at nodup
  rw [← split, List.drop_left]
  constructor
  · intro member
    refine ⟨List.mem_append_right _ member, fun done => ?_⟩
    have old := (before.history_exact completion.event).mpr done
    exact nodup.2.2 _ old _ (List.mem_map_of_mem member) rfl
  · rintro ⟨member, fresh⟩
    rcases List.mem_append.mp member with old | new
    · exact (fresh ((before.history_exact completion.event).mp (List.mem_map_of_mem old))).elim
    · exact new

end ConfigReaches

/-- **Equal views of one owner after two block runs.** Two runs from one
configuration that complete only bindings, complete the same bindings of
`owner` and agree on the actions of those, leave `owner` the same masked store
and the same own completions. -/
theorem playerView_eq_of_reaches (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {start left right : (serviceGraph setup mode).Config}
    (leftReach : ConfigReaches setup start left) (rightReach : ConfigReaches setup start right)
    (owner : Player)
    (fresh : ∀ event, event ∉ start.cut.completed →
      event ∈ left.cut.completed ∨ event ∈ right.cut.completed →
        ∃ actor payload outputEq codeEq,
          nodeView (serviceGraph setup mode) event = .bind actor payload outputEq codeEq)
    (sameCompleted : ∀ event payload,
      (serviceGraph setup mode).outputLayout event = .binding owner payload →
        (event ∈ left.cut.completed ↔ event ∈ right.cut.completed))
    (sameActions : ∀ completion ∈ left.history, ∀ payload,
      (serviceGraph setup mode).outputLayout completion.event = .binding owner payload →
        completion.event ∉ start.cut.completed → completion ∈ right.history) :
    (serviceGraph setup mode).playerStore owner left.store =
        (serviceGraph setup mode).playerStore owner right.store ∧
      (serviceGraph setup mode).ownCompletions owner left.history =
        (serviceGraph setup mode).ownCompletions owner right.history := by
  -- Every completion of either side's own bindings appended by the run is shared.
  have shared : ∀ completion, completion ∈ left.history →
      completion.event ∉ start.cut.completed →
      (serviceGraph setup mode).actor? completion.event = some owner →
        completion ∈ right.history := by
    intro completion member notStart actor
    have done : completion.event ∈ left.cut.completed :=
      (left.history_exact completion.event).mp (List.mem_map_of_mem member)
    obtain ⟨other, payload, outputEq, codeEq, _⟩ := fresh _ notStart (Or.inl done)
    have otherIs : other = owner := Option.some.inj
      ((nodeView_bind_actor outputEq codeEq).symm.trans actor)
    subst otherIs
    exact sameActions completion member payload outputEq notStart
  have sharedBack : ∀ completion, completion ∈ right.history →
      completion.event ∉ start.cut.completed →
      (serviceGraph setup mode).actor? completion.event = some owner →
        completion ∈ left.history := by
    intro completion member notStart actor
    have done : completion.event ∈ right.cut.completed :=
      (right.history_exact completion.event).mp (List.mem_map_of_mem member)
    obtain ⟨other, payload, outputEq, codeEq, _⟩ := fresh _ notStart (Or.inr done)
    have otherIs : other = owner := Option.some.inj
      ((nodeView_bind_actor outputEq codeEq).symm.trans actor)
    subst otherIs
    have leftDone := (sameCompleted _ payload outputEq).mpr done
    obtain ⟨leftCompletion, leftMember, leftEvent⟩ :=
      List.mem_map.mp ((left.history_exact completion.event).mpr leftDone)
    have moved := sameActions leftCompletion leftMember payload (leftEvent ▸ outputEq)
      (leftEvent ▸ notStart)
    have same := completion_eq_of_event moved member leftEvent
    exact same ▸ leftMember
  refine ⟨?_, ?_⟩
  · funext field
    by_cases visible : (serviceGraph setup mode).fieldVisibleTo owner field
    · rw [EventGraph.playerStore_of_visible _ owner _ field visible,
        EventGraph.playerStore_of_visible _ owner _ field visible]
      cases field with
      | inl input =>
          rw [EventGraph.Config.store_input, EventGraph.Config.store_input, leftReach.inputs,
            rightReach.inputs]
      | inr event =>
          rw [EventGraph.Config.store_output, EventGraph.Config.store_output]
          by_cases old : event ∈ start.cut.completed
          · rw [(leftReach.output_completed old).2, (rightReach.output_completed old).2]
          · by_cases anyDone : event ∈ left.cut.completed ∨ event ∈ right.cut.completed
            · obtain ⟨other, payload, outputEq, codeEq, node⟩ := fresh event old anyDone
              have otherIs : other = owner := by
                change ((serviceGraph setup mode).outputLayout event).VisibleTo owner at visible
                rw [outputEq] at visible
                exact visible
              subst otherIs
              have bothDone : event ∈ left.cut.completed ∧ event ∈ right.cut.completed := by
                rcases anyDone with leftDone | rightDone
                · exact ⟨leftDone, (sameCompleted event payload outputEq).mp leftDone⟩
                · exact ⟨(sameCompleted event payload outputEq).mpr rightDone, rightDone⟩
              obtain ⟨completion, member, eventEq⟩ :=
                List.mem_map.mp ((left.history_exact event).mpr bothDone.1)
              subst eventEq
              have rightMember := sameActions completion member payload outputEq old
              have leftFresh : completion ∉ start.history := fun inStart =>
                old ((start.history_exact _).mp (List.mem_map_of_mem inStart))
              rw [leftReach.binding_output member leftFresh outputEq codeEq,
                rightReach.binding_output rightMember leftFresh outputEq codeEq]
            · have leftNone : left.outputs event = none := by
                cases output : left.outputs event with
                | none => rfl
                | some value =>
                    exact (anyDone (Or.inl ((left.output_available event).mp
                      (by rw [output]; rfl)))).elim
              have rightNone : right.outputs event = none := by
                cases output : right.outputs event with
                | none => rfl
                | some value =>
                    exact (anyDone (Or.inr ((right.output_available event).mp
                      (by rw [output]; rfl)))).elim
              rw [leftNone, rightNone]
    · rw [EventGraph.playerStore_of_hidden _ owner _ field visible,
        EventGraph.playerStore_of_hidden _ owner _ field visible]
  · obtain ⟨leftAppended, leftSplit⟩ := leftReach.history_prefix
    obtain ⟨rightAppended, rightSplit⟩ := rightReach.history_prefix
    have leftDrop : left.history.drop start.history.length = leftAppended := by
      rw [← leftSplit, List.drop_left]
    have rightDrop : right.history.drop start.history.length = rightAppended := by
      rw [← rightSplit, List.drop_left]
    unfold EventGraph.ownCompletions
    rw [← leftSplit, ← rightSplit, List.filter_append, List.filter_append]
    congr 1
    let ownOf := fun completion : (serviceGraph setup mode).Completion =>
      decide ((serviceGraph setup mode).actor? completion.event = some owner)
    have sorted (reached : (serviceGraph setup mode).Config)
        (reach : ConfigReaches setup start reached) (appended)
        (split : reached.history = start.history ++ appended)
        (freshHere : ∀ event, event ∉ start.cut.completed → event ∈ reached.cut.completed →
          ∃ actor payload outputEq codeEq,
            nodeView (serviceGraph setup mode) event = .bind actor payload outputEq codeEq) :
        (appended.filter ownOf).Pairwise fun first second =>
          first.event.val < second.event.val := by
      have order := reach.binding_order relaxed
      rw [split, List.drop_left] at order
      refine (order.filter ownOf).imp_of_mem ?_
      intro first second firstMember secondMember before
      have firstOld := (reach.mem_drop_iff first).mp
        (by rw [split, List.drop_left]; exact (List.mem_filter.mp firstMember).1)
      have secondOld := (reach.mem_drop_iff second).mp
        (by rw [split, List.drop_left]; exact (List.mem_filter.mp secondMember).1)
      obtain ⟨firstActor, firstPayload, firstEq, firstCode, _⟩ := freshHere first.event firstOld.2
        ((reached.history_exact _).mp (List.mem_map_of_mem firstOld.1))
      obtain ⟨secondActor, secondPayload, secondEq, secondCode, _⟩ := freshHere second.event
        secondOld.2 ((reached.history_exact _).mp (List.mem_map_of_mem secondOld.1))
      have firstOwner : firstActor = owner := Option.some.inj
        ((nodeView_bind_actor firstEq firstCode).symm.trans
          (of_decide_eq_true (List.mem_filter.mp firstMember).2))
      have secondOwner : secondActor = owner := Option.some.inj
        ((nodeView_bind_actor secondEq secondCode).symm.trans
          (of_decide_eq_true (List.mem_filter.mp secondMember).2))
      apply before
      rw [firstEq, secondEq, firstOwner, secondOwner]
      rfl
    have leftSorted := sorted left leftReach leftAppended leftSplit.symm
      (fun event old done => fresh event old (Or.inl done))
    have rightSorted := sorted right rightReach rightAppended rightSplit.symm
      (fun event old done => fresh event old (Or.inr done))
    apply List.Perm.eq_of_pairwise
      (fun first second _ _ forward backward => absurd (forward.trans backward) (lt_irrefl _))
      leftSorted rightSorted
    have leftNodup : (leftAppended.filter ownOf).Nodup :=
      leftSorted.imp fun below same => by subst same; exact lt_irrefl _ below
    have rightNodup : (rightAppended.filter ownOf).Nodup :=
      rightSorted.imp fun below same => by subst same; exact lt_irrefl _ below
    apply (List.perm_ext_iff_of_nodup leftNodup rightNodup).mpr
    intro completion
    simp only [List.mem_filter]
    constructor
    · rintro ⟨member, own⟩
      have parts := (leftReach.mem_drop_iff completion).mp (by rw [leftDrop]; exact member)
      have rightMember := shared completion parts.1 parts.2 (of_decide_eq_true own)
      refine ⟨?_, own⟩
      rw [← rightDrop]
      exact (rightReach.mem_drop_iff completion).mpr ⟨rightMember, parts.2⟩
    · rintro ⟨member, own⟩
      have parts := (rightReach.mem_drop_iff completion).mp (by rw [rightDrop]; exact member)
      have leftMember := sharedBack completion parts.1 parts.2 (of_decide_eq_true own)
      refine ⟨?_, own⟩
      rw [← leftDrop]
      exact (leftReach.mem_drop_iff completion).mpr ⟨leftMember, parts.2⟩

end Vegas
