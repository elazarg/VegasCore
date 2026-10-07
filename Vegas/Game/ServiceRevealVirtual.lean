/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRevealDecode

/-! # Opened disclosures agree with the opened block

From the start of a block of disclosures, completing every disclosure of the
block in rank order with the decision to disclose exactly when its opening is
effective reaches a configuration (`Vegas.exists_openedVirtual`). Along any run
in which every completed disclosure of the block was so decided, each completed
disclosure has exactly the output it has there (`Vegas.outputs_eq_of_opened`): a
disclosure reads only fields of its predecessors, which by induction on rank
agree, so both make the same decision and publish the same result.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}

namespace ConfigReaches

variable {before after : (serviceGraph setup mode).Config}

/-- A run keeps the fields an event reads once its predecessors have
completed. -/
theorem readFields_agree (reach : ConfigReaches setup before after)
    {event : (serviceGraph setup mode).EventId}
    (preds : ∀ prior ∈ (serviceGraph setup mode).order.predecessors event,
      prior ∈ before.cut.completed) :
    EventGraph.Store.AgreeOn before.store after.store
      ((serviceGraph setup mode).nodes event).readFields := by
  induction reach with
  | refl => intro _ _; rfl
  | tail earlier step ih =>
      rename_i middle current
      have middlePreds : ∀ prior ∈ (serviceGraph setup mode).order.predecessors event,
          prior ∈ middle.cut.completed := fun prior member =>
        (ConfigReaches.output_completed earlier (preds prior member)).1
      intro field read
      exact (ih field read).trans (readFields_kept middlePreds step field read)

/-- The completion of an event completed before a run is kept by the run. -/
theorem completion_kept (reach : ConfigReaches setup before after)
    {completion : (serviceGraph setup mode).Completion}
    (done : completion.event ∈ before.cut.completed)
    (member : completion ∈ after.history) : completion ∈ before.history := by
  obtain ⟨old, oldMember, oldEvent⟩ :=
    List.mem_map.mp ((before.history_exact completion.event).mpr done)
  have same := completion_eq_of_event (reach.history_prefix.subset oldMember) member oldEvent
  rw [← same]
  exact oldMember

end ConfigReaches

/-- A disclosure opened at a configuration stays opened along every run. -/
theorem OpenedAt.reaches {before after : (serviceGraph setup mode).Config}
    (reach : ConfigReaches setup before after) {event : (serviceGraph setup mode).EventId}
    (done : event ∈ before.cut.completed) (opened : OpenedAt before event) :
    OpenedAt after event := by
  unfold OpenedAt at opened ⊢
  cases node : nodeView (serviceGraph setup mode) event with
  | bind => trivial
  | sample => trivial
  | resolve owner payload binding checks outputEq codeEq =>
      rw [node] at opened
      dsimp only at opened ⊢
      intro action member
      have kept := reach.completion_kept (completion := ⟨event, action⟩) done member
      refine (opened action kept).trans ?_
      have reads : ((serviceGraph setup mode).nodes event).readFields =
          insert binding.field (EventGraph.GuardCheck.listReadFields checks) :=
        (EventGraph.EventCode.readFields_cast outputEq
          ((serviceGraph setup mode).nodes event)).symm.trans
          (congrArg EventGraph.EventCode.readFields codeEq)
      have agree := reach.readFields_agree (fun prior pred =>
        before.cut.predecessor_closed done pred)
      rw [reads] at agree
      rw [EventGraph.EventCode.resolveOutput?_congr binding checks true _ _ agree]

/-- An event producing a publication is a resolution. -/
theorem nodeView_resolve_of_publication {event : (serviceGraph setup mode).EventId}
    (publication : ((serviceGraph setup mode).outputLayout event).IsPublication) :
    ∃ owner payload binding checks outputEq codeEq,
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq := by
  cases node : nodeView (serviceGraph setup mode) event with
  | resolve owner payload binding checks outputEq codeEq =>
      exact ⟨owner, payload, binding, checks, outputEq, codeEq, rfl⟩
  | bind _ _ outputEq _ =>
      rw [outputEq] at publication
      exact publication.elim
  | sample _ _ outputEq _ =>
      rw [outputEq] at publication
      exact publication.elim

/-- **The opened block.** From a configuration that has completed exactly the
events below `low`, the block of publications up to `high` can be completed in
rank order, each with the decision to disclose exactly when its opening is
effective. -/
theorem exists_openedVirtual {low : Nat} (start : (serviceGraph setup mode).Config)
    (startPrefix : start.cut.IsPrefix low) :
    ∀ (count : Nat), low + count ≤ (serviceGraph setup mode).order.eventCount →
      (∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
        event.val < low + count →
        ((serviceGraph setup mode).outputLayout event).IsPublication) →
      ∃ virtual, ConfigReaches setup start virtual ∧ virtual.cut.IsPrefix (low + count) ∧
        ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
          event.val < low + count → OpenedAt virtual event := by
  intro count
  induction count with
  | zero =>
      intro _ _
      exact ⟨start, Relation.ReflTransGen.refl, startPrefix, fun event lower upper => by omega⟩
  | succ count ih =>
      intro bounded publications
      obtain ⟨virtual, reach, ordered, opened⟩ := ih (by omega)
        (fun event lower upper => publications event lower (by omega))
      have active : low + count < (serviceGraph setup mode).order.eventCount := by omega
      let event : (serviceGraph setup mode).EventId := ⟨low + count, active⟩
      have ready : virtual.cut.Ready event := ordered.ready active
      obtain ⟨owner, payload, binding, checks, outputEq, codeEq, node⟩ :=
        nodeView_resolve_of_publication (publications event (by simp [event])
          (by simp [event]))
      classical
      let disclose : Bool := decide (∃ value, EventGraph.EventCode.resolveOutput? binding
        checks true virtual.store = some (.success value))
      let action : (serviceGraph setup mode).Action event :=
        cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose
      obtain ⟨next, stepped⟩ := (virtual.step event ready action).support_nonempty
      have step : ConfigStep setup virtual next := Or.inr ⟨event, ready, action, stepped⟩
      have nextReach := reach.trans_single step
      have nextOrdered : next.cut.IsPrefix (low + (count + 1)) := by
        rw [virtual.step_cut event ready action next stepped]
        exact ordered.complete_at event ready rfl
      refine ⟨next, nextReach, nextOrdered, fun other lower upper => ?_⟩
      by_cases same : other.val = low + count
      · have otherIs : other = event := Fin.ext same
        subst otherIs
        unfold OpenedAt
        rw [node]
        intro completed member
        have mine : (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈ next.history := by
          rw [virtual.step_history event ready action next stepped]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        have equal := completion_eq_of_event member mine rfl
        simp only [EventGraph.Completion.mk.injEq, heq_eq_eq, true_and] at equal
        subst equal
        have agree := readFields_kept (fun prior pred => ready.2 pred) step
        have reads : ((serviceGraph setup mode).nodes event).readFields =
            insert binding.field (EventGraph.GuardCheck.listReadFields checks) :=
          (EventGraph.EventCode.readFields_cast outputEq
            ((serviceGraph setup mode).nodes event)).symm.trans
            (congrArg EventGraph.EventCode.readFields codeEq)
        rw [reads] at agree
        rw [← EventGraph.EventCode.resolveOutput?_congr binding checks true _ _ agree]
        simp only [action, disclose, cast_cast, cast_eq, decide_eq_true_eq]
      · have earlier : other.val < low + count := by omega
        have done : other ∈ virtual.cut.completed := (ordered.2 other).mpr earlier
        exact (opened other lower earlier).reaches (Relation.ReflTransGen.single step) done

/-- **Opened runs agree with the opened block.** Two runs from one
configuration that complete only publications at or after `low`, of which the
second completes every one of them below `high`, and along which every
completed one was decided to disclose exactly when its opening is effective,
give every event completed by the first the output the second gives it. -/
theorem outputs_eq_of_opened {low high : Nat} {start current virtual :
      (serviceGraph setup mode).Config}
    (currentReach : ConfigReaches setup start current)
    (virtualReach : ConfigReaches setup start virtual)
    (startPrefix : start.cut.IsPrefix low)
    (currentWithin : ∀ event ∈ current.cut.completed, event.val < high)
    (virtualPrefix : virtual.cut.IsPrefix high)
    (publications : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → ((serviceGraph setup mode).outputLayout event).IsPublication)
    (currentOpened : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event ∈ current.cut.completed → OpenedAt current event)
    (virtualOpened : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → OpenedAt virtual event) :
    ∀ event ∈ current.cut.completed, current.outputs event = virtual.outputs event := by
  suffices all : ∀ n, ∀ event : (serviceGraph setup mode).EventId, event.val = n →
      event ∈ current.cut.completed → current.outputs event = virtual.outputs event from
    fun event done => all event.val event rfl done
  intro n
  induction n using Nat.strong_induction_on with
  | _ n hn =>
  intro event rank done
  have ih : ∀ other : (serviceGraph setup mode).EventId, other.val < event.val →
      other ∈ current.cut.completed → current.outputs other = virtual.outputs other :=
    fun other below => hn other.val (rank ▸ below) other rfl
  by_cases old : event ∈ start.cut.completed
  · rw [(currentReach.output_completed old).2, (virtualReach.output_completed old).2]
  · have lower : low ≤ event.val :=
      Nat.le_of_not_gt fun below => old ((startPrefix.2 event).mpr below)
    have upper := currentWithin event done
    have virtualDone : event ∈ virtual.cut.completed := (virtualPrefix.2 event).mpr upper
    obtain ⟨⟨_, action⟩, member, rfl⟩ :=
      List.mem_map.mp ((current.history_exact event).mpr done)
    obtain ⟨⟨_, other⟩, otherMember, otherEvent⟩ :=
      List.mem_map.mp ((virtual.history_exact _).mpr virtualDone)
    change _ = _ at otherEvent
    subst otherEvent
    have currentOpen := currentOpened _ lower done
    have virtualOpen := virtualOpened _ lower upper
    unfold OpenedAt at currentOpen virtualOpen
    cases node : nodeView (serviceGraph setup mode) _ with
    | bind _ _ outputEq _ =>
        have publication := publications _ lower upper
        rw [outputEq] at publication
        exact publication.elim
    | sample _ _ outputEq _ =>
        have publication := publications _ lower upper
        rw [outputEq] at publication
        exact publication.elim
    | resolve owner payload binding checks outputEq codeEq =>
        rw [node] at currentOpen virtualOpen
        have reads : ((serviceGraph setup mode).nodes _).readFields =
            insert binding.field (EventGraph.GuardCheck.listReadFields checks) :=
          (EventGraph.EventCode.readFields_cast outputEq
            ((serviceGraph setup mode).nodes _)).symm.trans
            (congrArg EventGraph.EventCode.readFields codeEq)
        have agree : EventGraph.Store.AgreeOn current.store virtual.store
            (insert binding.field (EventGraph.GuardCheck.listReadFields checks)) := by
          intro field read
          rw [← reads] at read
          have available := (serviceGraph setup mode).reads_available _ field read
          cases field with
          | inl input =>
              rw [EventGraph.Config.store_input, EventGraph.Config.store_input,
                currentReach.inputs, virtualReach.inputs]
          | inr producer =>
              rw [EventGraph.Config.store_output, EventGraph.Config.store_output]
              exact ih producer ((serviceGraph setup mode).order.predecessor_lt available)
                (current.cut.predecessor_closed done available)
        have sameResolve := EventGraph.EventCode.resolveOutput?_congr binding checks true _ _
          agree
        have decisions : (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) =
            cast (congrArg EventGraph.EventField.Action outputEq) other := by
          rw [Bool.eq_iff_iff, currentOpen action member, virtualOpen other otherMember,
            sameResolve]
        have actionEq : action = other := by
          have := congrArg (cast (congrArg EventGraph.EventField.Action outputEq.symm)) decisions
          simpa only [cast_cast, cast_eq] using this
        rw [← actionEq] at otherMember
        rw [currentReach.resolve_output member old (outputEq := outputEq) (codeEq := codeEq),
          virtualReach.resolve_output otherMember old (outputEq := outputEq) (codeEq := codeEq)]
        have sameAction := EventGraph.EventCode.resolveOutput?_congr binding checks
          (cast (congrArg EventGraph.EventField.Action outputEq) action) _ _ agree
        rw [sameAction]

end Vegas
