/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRevealBlock

/-! # Reading a block's disclosures back into the source

After a run through a block of disclosures, every disclosure of the block has
completed, in whatever order. When each of them was decided to disclose exactly
when its opening is effective (`Vegas.OpenedAt`), the run decodes to the source
configuration in which the leading disclosures open in source order
(`Vegas.revealBlockDecode`): a disclosure's output reads only fields of its
predecessors, which no later completion changes
(`Vegas.ConfigReaches.resolve_output`), and one owner's disclosures complete in
source order (`Vegas.ConfigReaches.publication_order`).
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

/-- **One owner's disclosures complete in source order.** On a reveal-relaxed
graph, among the completions a run appends, a publication precedes every later
publication of the same actor in rank. -/
theorem publication_order (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    (reach : ConfigReaches setup before after) :
    (after.history.drop before.history.length).Pairwise fun first second =>
      ((serviceGraph setup mode).outputLayout first.event).IsPublication →
      (serviceGraph setup mode).actor? first.event =
        (serviceGraph setup mode).actor? second.event →
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
        intro first firstMember second secondMember firstPublication sameActor
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
        have barrier := EventGraph.barrierOrder_public_event
          (serviceGraph setup mode).outputLayout lower firstPublication.isPublic
        exact ready.1 (middle.cut.predecessor_closed firstDone
          (relaxed first.event event barrier
            (EventGraph.IndependentReveals.not_of_actor_eq sameActor.symm)))

/-- A step keeps the output of every event completed before it. -/
private theorem output_step {config next : (serviceGraph setup mode).Config}
    (step : ConfigStep setup config next) {event : (serviceGraph setup mode).EventId}
    (done : event ∈ config.cut.completed) : next.outputs event = config.outputs event :=
  (output_completed (Relation.ReflTransGen.single step) done).2

/-- **A disclosure completed along a run stores its result on the final store.**
The result of a resolution completed by the run reads only fields of its
predecessors, which the rest of the run keeps. -/
theorem resolve_output (reach : ConfigReaches setup before after)
    {event : (serviceGraph setup mode).EventId} {action : (serviceGraph setup mode).Action event}
    (member : (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈ after.history)
    (fresh : event ∉ before.cut.completed) {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks} :
    after.outputs event =
      (EventGraph.EventCode.resolveOutput? binding checks
        (cast (congrArg EventGraph.EventField.Action outputEq) action) after.store).map
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)) := by
  have reads : ((serviceGraph setup mode).nodes event).readFields =
      insert binding.field (EventGraph.GuardCheck.listReadFields checks) :=
    (EventGraph.EventCode.readFields_cast outputEq
      ((serviceGraph setup mode).nodes event)).symm.trans
      (congrArg EventGraph.EventCode.readFields codeEq)
  induction reach with
  | refl =>
      exact (fresh ((before.history_exact event).mp (List.mem_map_of_mem member))).elim
  | tail earlier step ih =>
      rename_i middle current
      by_cases old : event ∈ middle.cut.completed
      · obtain ⟨oldCompletion, oldMember, oldEvent⟩ :=
          List.mem_map.mp ((middle.history_exact event).mpr old)
        have kept : (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈ middle.history := by
          have inCurrent : oldCompletion ∈ current.history :=
            (ConfigReaches.history_prefix (Relation.ReflTransGen.single step)).subset oldMember
          have same := completion_eq_of_event inCurrent member oldEvent
          rw [← same]
          exact oldMember
        have preds : ∀ prior ∈ (serviceGraph setup mode).order.predecessors event,
            prior ∈ middle.cut.completed := fun _ pred =>
          middle.cut.predecessor_closed old pred
        have agree := readFields_kept preds step
        rw [reads] at agree
        rw [output_step step old, ih kept,
          EventGraph.EventCode.resolveOutput?_congr binding checks _ _ _ agree]
      · rcases step with same | ⟨other, ready, otherAction, stepped⟩
        · rw [same] at member
          exact (old ((middle.history_exact event).mp (List.mem_map_of_mem member))).elim
        · rw [EventGraph.Config.step_history _ other ready otherAction _ stepped] at member
          rcases List.mem_append.mp member with inMiddle | new
          · exact (old ((middle.history_exact event).mp (List.mem_map_of_mem inMiddle))).elim
          rw [List.mem_singleton] at new
          cases new
          obtain ⟨result, resolved⟩ : ∃ result,
              EventGraph.EventCode.resolveOutput? binding checks
                (cast (congrArg EventGraph.EventField.Action outputEq) action) middle.store =
                some result := by
            have available := EventGraph.EventCode.resolveOutput?_isSome binding checks
              (cast (congrArg EventGraph.EventField.Action outputEq) action) middle.store
              (fun field read => middle.read_available ready (by rw [reads]; exact read))
            exact Option.isSome_iff_exists.mp available
          have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
              (cast (congrArg EventGraph.EventField.Action outputEq) action) := by
            simp only [cast_cast, cast_eq]
          have stepEq := middle.step_eq_map_of_code event ready outputEq _ codeEq
            (cast (congrArg EventGraph.EventField.Action outputEq) action) (PMF.pure result)
            (by rw [EventGraph.EventCode.resolve_eval?, resolved]; rfl)
          rw [← actionEq, PMF.pure_map] at stepEq
          rw [stepEq, PMF.mem_support_pure_iff] at stepped
          subst stepped
          have preds : ∀ prior ∈ (serviceGraph setup mode).order.predecessors event,
              prior ∈ middle.cut.completed := fun _ pred => ready.2 pred
          have agree := readFields_kept preds (Or.inr ⟨event, ready,
            cast (congrArg EventGraph.EventField.Action outputEq.symm)
              (cast (congrArg EventGraph.EventField.Action outputEq) action), by
              rw [← actionEq, stepEq]; exact (PMF.mem_support_pure_iff _ _).mpr rfl⟩)
          rw [reads] at agree
          rw [EventGraph.Config.complete_output_same,
            ← EventGraph.EventCode.resolveOutput?_congr binding checks _ _ _ agree, resolved]
          rfl

/-- Context references to fields completed at the start keep agreeing along a
run. -/
theorem agrees {Γ : SourceCtx Player L} (reach : ConfigReaches setup before after)
    (refs : ContextRefs (serviceGraph setup mode).layout Γ) (state : State L Γ)
    (agree : refs.Agrees state before.store)
    (done : ∀ {name cell} (ref : HasVar Γ name cell) producer,
      (refs.get ref).field = .inr producer → producer ∈ before.cut.completed) :
    refs.Agrees state after.store := by
  intro name cell ref
  rw [← agree ref]
  apply EventGraph.FieldRef.get?_congr
  cases fieldEq : (refs.get ref).field with
  | inl input =>
      rw [EventGraph.Config.store_input, EventGraph.Config.store_input, reach.inputs]
  | inr producer =>
      rw [EventGraph.Config.store_output, EventGraph.Config.store_output]
      exact (reach.output_completed (done ref producer fieldEq)).2

end ConfigReaches

/-- A disclosure completed, if at all, with the decision to disclose exactly
when its opening is effective at the configuration. -/
def OpenedAt (config : (serviceGraph setup mode).Config)
    (event : (serviceGraph setup mode).EventId) : Prop :=
  match nodeView (serviceGraph setup mode) event with
  | .resolve _ _ binding checks outputEq _ =>
      ∀ action : (serviceGraph setup mode).Action event,
        (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈ config.history →
          ((cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = true ↔
            ∃ value, EventGraph.EventCode.resolveOutput? binding checks true config.store =
              some (.success value))
  | _ => True

/-- A list sorted by rank, filtered below one more than the rank of one of its
members, adds exactly that member to the filter below its rank. -/
private theorem filter_rank_succ {α : Type} (rank : α → Nat) :
    ∀ (items : List α), items.Pairwise (fun first second => rank first < rank second) →
      ∀ item ∈ items,
      items.filter (fun other => decide (rank other < rank item + 1)) =
        items.filter (fun other => decide (rank other < rank item)) ++ [item]
  | [], _, _, member => (List.not_mem_nil member).elim
  | head :: tail, sorted, item, member => by
      obtain ⟨headBelow, tailSorted⟩ := List.pairwise_cons.mp sorted
      rcases List.mem_cons.mp member with same | later
      · subst same
        have tailEmpty : tail.filter (fun other => decide (rank other < rank item + 1)) = [] :=
          List.filter_eq_nil_iff.mpr fun other inTail => by
            have := headBelow other inTail
            simp only [decide_eq_true_eq]
            omega
        have tailEmpty' : tail.filter (fun other => decide (rank other < rank item)) = [] :=
          List.filter_eq_nil_iff.mpr fun other inTail => by
            have := headBelow other inTail
            simp only [decide_eq_true_eq]
            omega
        rw [List.filter_cons, List.filter_cons, tailEmpty, tailEmpty']
        simp
      · have headLess := headBelow item later
        have rest := filter_rank_succ rank tail tailSorted item later
        rw [List.filter_cons, List.filter_cons, rest]
        simp [headLess, show rank head < rank item + 1 by omega]

/-- **One owner's completions after a block are the accumulated ones.** Two
lists of completions of block disclosures with the same members, one sorted by
rank and the other appended by a run, have the same completions of every
owner. -/
private theorem ownCompletions_eq_of_sorted
    (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {low high : Nat} {start final : (serviceGraph setup mode).Config}
    (finalReach : ConfigReaches setup start final)
    (startPrefix : start.cut.IsPrefix low) (finalPrefix : final.cut.IsPrefix high)
    (publications : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → ((serviceGraph setup mode).outputLayout event).IsPublication)
    (acc : List (serviceGraph setup mode).Completion)
    (members : ∀ completion, completion ∈ acc ↔ completion ∈ final.history ∧
      low ≤ completion.event.val ∧ completion.event.val < high)
    (sorted : acc.Pairwise fun first second => first.event.val < second.event.val)
    (owner : Player) :
    (serviceGraph setup mode).ownCompletions owner final.history =
      (serviceGraph setup mode).ownCompletions owner (start.history ++ acc) := by
  obtain ⟨appended, split⟩ := finalReach.history_prefix
  have dropEq : final.history.drop start.history.length = appended := by
    rw [← split, List.drop_left]
  unfold EventGraph.ownCompletions
  rw [← split, List.filter_append, List.filter_append]
  congr 1
  let ownOf := fun completion : (serviceGraph setup mode).Completion =>
    decide ((serviceGraph setup mode).actor? completion.event = some owner)
  have appendedIff : ∀ completion, completion ∈ appended ↔ completion ∈ final.history ∧
      low ≤ completion.event.val ∧ completion.event.val < high := by
    intro completion
    rw [← dropEq, finalReach.mem_drop_iff]
    constructor
    · rintro ⟨member, fresh⟩
      refine ⟨member, Nat.le_of_not_gt fun below => fresh ((startPrefix.2 _).mpr below), ?_⟩
      exact (finalPrefix.2 _).mp ((final.history_exact _).mp (List.mem_map_of_mem member))
    · rintro ⟨member, lower, _⟩
      refine ⟨member, fun done => ?_⟩
      have := (startPrefix.2 _).mp done
      omega
  have appendedSorted : (appended.filter ownOf).Pairwise fun first second =>
      first.event.val < second.event.val := by
    have order := finalReach.publication_order relaxed
    rw [dropEq] at order
    refine (order.filter ownOf).imp_of_mem ?_
    intro first second firstMember secondMember before
    have firstIn := (appendedIff first).mp (List.mem_filter.mp firstMember).1
    apply before (publications first.event firstIn.2.1 firstIn.2.2)
    rw [of_decide_eq_true (List.mem_filter.mp firstMember).2,
      of_decide_eq_true (List.mem_filter.mp secondMember).2]
  have accSorted : (acc.filter ownOf).Pairwise fun first second =>
      first.event.val < second.event.val := sorted.filter ownOf
  symm
  apply List.Perm.eq_of_pairwise
    (fun first second _ _ forward backward => absurd (forward.trans backward) (lt_irrefl _))
    accSorted appendedSorted
  have accNodup : (acc.filter ownOf).Nodup :=
    accSorted.imp fun below same => by subst same; exact lt_irrefl _ below
  have appendedNodup : (appended.filter ownOf).Nodup :=
    appendedSorted.imp fun below same => by subst same; exact lt_irrefl _ below
  apply (List.perm_ext_iff_of_nodup accNodup appendedNodup).mpr
  intro completion
  simp only [List.mem_filter, members, appendedIff]

/-- **The block decodes to its opened source configuration.** On a
reveal-relaxed graph, a run from the start of a block of disclosures that has
completed exactly the block, every disclosure of which was decided to disclose
exactly when its opening is effective, decodes through the leading
disclosures to the source configuration in which they open in source order.
The induction follows the source configuration reached so far together with the
run's completions of the disclosures already read, sorted by rank. -/
theorem revealBlockDecode (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {low high : Nat} (wholeProfile : BehavioralProfile setup.program)
    (start final : (serviceGraph setup mode).Config)
    (finalReach : ConfigReaches setup start final)
    (startPrefix : start.cut.IsPrefix low) (finalPrefix : final.cut.IsPrefix high)
    (publications : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → ((serviceGraph setup mode).outputLayout event).IsPublication)
    (opened : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → OpenedAt final event) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (prefixed : RevealPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program)
      (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
      (source : Config Player L Γ),
      CompiledPolicySuffix setup.program wholeProfile program profile refs source.revelations
        source.registry embedding refsBefore offset →
      refs.Agrees source.state final.store →
      ∀ acc : List (serviceGraph setup mode).Completion,
      decodeHistory setup.program ((start.history ++ acc).map
        (setup.eventGraph.fromModeCompletion mode)) = source.history →
      (∀ completion, completion ∈ acc ↔ completion ∈ final.history ∧
        low ≤ completion.event.val ∧ completion.event.val < offset) →
      acc.Pairwise (fun first second => first.event.val < second.event.val) →
      low ≤ offset → offset + count = high →
      decodeSourcePrefix? program refs source.registry source.revelations embedding.ref count
          final.store (decodeHistory setup.program
            (final.history.map (setup.eventGraph.fromModeCompletion mode))) =
        some ((revealTail count program prefixed).lift (ProtocolState.entry _
          (openChain count program prefixed source))) := by
  intro count
  induction count with
  | zero =>
      intro Γ names program profile prefixed refs embedding refsBefore offset source _ agree acc
        accHistory members sorted _ offsetEnd
      simp only [Nat.add_zero] at offsetEnd
      subst offsetEnd
      have history : decodeHistory setup.program (final.history.map
          (setup.eventGraph.fromModeCompletion mode)) = source.history := by
        rw [← accHistory]
        funext owner
        change decodeCompletions setup.program (setup.eventGraph.ownCompletions owner
            (final.history.map (setup.eventGraph.fromModeCompletion mode))) =
          decodeCompletions setup.program (setup.eventGraph.ownCompletions owner
            ((start.history ++ acc).map (setup.eventGraph.fromModeCompletion mode)))
        rw [← ownCompletions_fromModeCompletion, ← ownCompletions_fromModeCompletion,
          ownCompletions_eq_of_sorted relaxed finalReach startPrefix finalPrefix publications acc
            members sorted owner]
      exact (SourceCheckpoint.decode (setup := setup) program
        ⟨agree, history, finalPrefix⟩ embedding.ref)
  | succ count ih =>
      intro Γ names program profile prefixed refs embedding refsBefore offset source aligned
        agree acc accHistory members sorted lowOffset offsetEnd
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | @reveal Γ names published owner name payload fresh selected unresolved next =>
          let index : Fin (eventCount (.reveal published owner name fresh selected unresolved
            next)) := ⟨0, by simp [eventCount]⟩
          let event : (serviceGraph setup mode).EventId := embedding.event index
          have eventRank : event.val = offset := by
            simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
          have outputEq : (serviceGraph setup mode).outputLayout event = .publication payload :=
            reveal_head_layout embedding
          have codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout)
              outputEq) ((serviceGraph setup mode).nodes event) = .resolve owner payload
                (refs.get selected) (compileChecks (published := published) refs source.registry
                  source.revelations selected) := by
            change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
              ((toEventGraph setup.program).nodes event) = _
            simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
          have node := EventGraphRuntime.nodeView_eq_resolve (graph := serviceGraph setup mode)
            outputEq codeEq
          have decodedAction (disclose : Bool) : decodeEventAction setup.program event
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose) =
                some (.reveal owner name disclose) := by
            have lookup := aligned.actionEq index
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose)
            simpa [event, index, outputEq, decodeEventAction] using lookup
          have done : event ∈ final.cut.completed := (finalPrefix.2 event).mpr (by omega)
          obtain ⟨⟨completed, action⟩, member, completedIs⟩ :=
            List.mem_map.mp ((final.history_exact event).mpr done)
          change completed = event at completedIs
          subst completedIs
          have notStart : event ∉ start.cut.completed := fun inStart => by
            have := (startPrefix.2 _).mp inStart
            omega
          let disclose : Bool := cast (congrArg EventGraph.EventField.Action outputEq) action
          have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
              disclose := by
            simp only [disclose, cast_cast, cast_eq]
          have output := finalReach.resolve_output member notStart (outputEq := outputEq)
            (codeEq := codeEq)
          have resolved (choice : Bool) := compiled_disclosure_result
            (graph := serviceGraph setup mode) published selected source refs final.store agree
            choice
          simp only [EventGraph.EventCode.resolveOutput?_playerStore] at resolved
          rw [resolved disclose, Option.map_some] at output
          -- The decision is the effective one.
          have openedHere := opened event (by omega) (by omega)
          unfold OpenedAt at openedHere
          rw [node] at openedHere
          have iff := openedHere action member
          change disclose = true ↔ _ at iff
          rw [resolved true] at iff
          have discloseEq : disclose = effectiveDisclosure published selected source true := by
            unfold effectiveDisclosure
            cases result : disclosureResult published selected source true with
            | failure =>
                rw [result] at iff
                cases discloseCase : disclose
                · rfl
                · exact absurd (iff.mp discloseCase) (by simp)
            | success value =>
                rw [result] at iff
                exact iff.mpr ⟨value, rfl⟩
          rw [discloseEq] at output
          let nextSource := revealSuccessor published selected source
            (effectiveDisclosure published selected source true)
          let tailRefs : ContextRefs (graphLayout setup.program)
              ((published, .publication payload) :: Γ) := refs.cons ⟨.inr event, outputEq⟩
          have nextAgree : tailRefs.Agrees nextSource.state final.store := by
            apply ContextRefs.Agrees.cons
            · exact agree
            · simp only [EventGraph.FieldRef.get?]
              change cast _ (final.outputs event) = _
              rw [output]
              have castSome {A B : Type} (same : A = B) (value : A) :
                  cast (congrArg Option same) (some value) = some (cast same value) := by
                cases same
                rfl
              rw [castSome (congrArg EventGraph.EventField.Value outputEq)]
              have castInverse {A B : Type} (same : A = B) (value : B) :
                  cast same (cast same.symm value) = value := by
                cases same
                rfl
              exact congrArg some (castInverse (congrArg EventGraph.EventField.Value outputEq) _)
          let added : (serviceGraph setup mode).Completion := ⟨event, action⟩
          have nextHistory : decodeHistory setup.program ((start.history ++
              (acc ++ [added])).map (setup.eventGraph.fromModeCompletion mode)) =
              nextSource.history := by
            rw [← List.append_assoc, List.map_append, List.map_singleton]
            refine (decodeHistory_append_completion setup.program _ event action).trans ?_
            have decodedHere : decodeEventAction setup.program event action =
                some (.reveal owner name (effectiveDisclosure published selected source true)) := by
              rw [actionEq, ← discloseEq]
              exact decodedAction disclose
            rw [decodedHere, accHistory]
            rfl
          have nextMembers : ∀ completion, completion ∈ acc ++ [added] ↔
              completion ∈ final.history ∧ low ≤ completion.event.val ∧
                completion.event.val < offset + 1 := by
            intro completion
            rw [List.mem_append, List.mem_singleton, members]
            constructor
            · rintro (⟨inFinal, lower, upper⟩ | rfl)
              · exact ⟨inFinal, lower, by omega⟩
              · exact ⟨member, (by rw [eventRank]; omega : low ≤ event.val),
                  (by rw [eventRank]; omega : event.val < offset + 1)⟩
            · rintro ⟨inFinal, lower, upper⟩
              by_cases same : completion.event.val = offset
              · right
                exact completion_eq_of_event inFinal member (Fin.ext (same.trans eventRank.symm))
              · exact Or.inl ⟨inFinal, lower, by omega⟩
          have nextSorted : (acc ++ [added]).Pairwise
              (fun first second : (serviceGraph setup mode).Completion =>
                first.event.val < second.event.val) := by
            refine List.pairwise_append.mpr ⟨sorted, List.pairwise_singleton _ _, ?_⟩
            intro first firstMember second secondMember
            rw [List.mem_singleton] at secondMember
            subst secondMember
            have := ((members first).mp firstMember).2.2
            change first.event.val < event.val
            omega
          have tailBefore : ContextRefsBefore tailRefs (embedding.tail next
              (by simp [eventCount]) (fun _ => rfl)) := by
            intro readName cell ref remaining
            cases ref with
            | here =>
                change (embedding.event index).val < (embedding.event (Fin.succ remaining)).val
                exact embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
            | there ref => exact refsBefore ref (Fin.succ remaining)
          have tailAligned := aligned.revealTail setup.program wholeProfile fresh selected
            unresolved next profile refs source.revelations source.registry embedding refsBefore
            offset
          have step := ih next (afterReveal profile) prefixed _
            (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) tailBefore (offset + 1)
            nextSource
            (by simpa only [nextSource, revealSuccessor, tailRefs, OutputEmbedding.ref] using
              tailAligned)
            nextAgree _ nextHistory nextMembers nextSorted (by omega) (by omega)
          rw [decodeSourcePrefix?_reveal]
          change Option.map Sum.inr (decodeSourcePrefix? next _ _ _ _ count final.store _) = _
          exact congrArg (Option.map Sum.inr) step

end Vegas
