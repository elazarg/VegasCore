/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceBlockPredraw

/-! # Reading a block's commitments back into the source

After a block of bindings, the source configuration reached is the one in which
the leading commitments take, in source order, the drawn actions of the drawn
owners and the other owners' completed choices (`Vegas.assembleChain`). Drawing
the drawn owners' commitments in advance with the other commitments read as
failures (`Vegas.assignChain`) and then reading the other owners' actual choices
gives the source law of the leading commitments with those choices supplied
(`Vegas.assignChain_assemble`): no drawn owner sees another owner's
commitment.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [IExpr.ResultTypes L] in
/-- A commitment changes a player's view only through the committed value, and
only when that player owns it. -/
theorem commitSuccessor_view_eq {Γ : SourceCtx Player L} {owner who : Player} {name : VarId}
    {payload : L.Ty} (guard : SourceGuard L Γ owner name payload) {first second : Config Player L Γ}
    {firstChoice secondChoice : PublicationResult (L.Val payload)}
    (same : first.view who = second.view who)
    (choices : owner = who → firstChoice = secondChoice) :
    (commitSuccessor name guard first firstChoice).view who =
      (commitSuccessor name guard second secondChoice).view who := by
  have states : sourceObserve who first.state = sourceObserve who second.state :=
    congrArg Prod.fst same
  have histories : first.history who = second.history who := congrArg Prod.snd same
  refine Prod.ext ?_ ?_
  · change sourceObserve who (commitSuccessor name guard first firstChoice).state =
      sourceObserve who (commitSuccessor name guard second secondChoice).state
    refine congrArg SourceObservation.mk ?_
    funext readName cell source
    cases source with
    | here =>
        by_cases own : owner = who
        · subst own
          simp only [↓reduceIte, choices rfl]
          rfl
        · simp only [own, ↓reduceIte]
    | there source =>
        have cellEq := congrArg (fun observation : SourceObservation L who Γ =>
          observation.cells readName cell source) states
        cases cell <;> exact cellEq
  · change Function.update first.history owner _ who = Function.update second.history owner _ who
    by_cases own : owner = who
    · subst own
      simp only [Function.update_self, histories, choices rfl]
    · simp only [Function.update_of_ne (Ne.symm own), histories]

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}

/-- The source choice an assignment makes at an embedded commitment; failure
when it makes none. -/
def assignedChoice {owner : Player} {payload : L.Ty} (assignment : Assignment setup mode)
    (event : (serviceGraph setup mode).EventId)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload) :
    PublicationResult (L.Val payload) :=
  match assignment event with
  | some action => cast (congrArg EventGraph.EventField.Action outputEq) action
  | none => .failure

variable (setup mode) in
/-- **The block's source configuration.** The configuration after the leading
commitments when every owner satisfying `drawn` takes its assigned choice and
the other owners take their successive choices from a list. -/
def assembleChain (drawn : Player → Prop) [DecidablePred drawn] : (count : Nat) →
    {Γ : SourceCtx Player L} →
    {names : Finset VarId} → (program : SourceProgram Player L Γ names) →
    (prefixed : CommitPrefix program count) →
    OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program →
    Config Player L Γ → Assignment setup mode → List (OwnAction Player L) →
      Config Player L (commitTail count program prefixed).context
  | 0, _, _, _, _, _, config, _, _ => config
  | count + 1, _, _, .commit (payload := payload) name owner _ guard next, prefixed, embedding,
      config, assignment, choices =>
      if drawn owner then
        assembleChain drawn count next prefixed
          (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
          (commitSuccessor name guard config (assignedChoice assignment
            (embedding.event ⟨0, by simp [eventCount]⟩) (commit_headLayout embedding)))
          assignment choices
      else
        assembleChain drawn count next prefixed
          (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
          (commitSuccessor name guard config (OwnAction.binding owner name payload choices.head?))
          assignment choices.tail
  | _ + 1, _, _, .ret _, prefixed, _, _, _, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _, _, _, _ => prefixed.elim
  | _ + 1, _, _, .reveal _ _ _ _ _ _ _, prefixed, _, _, _, _ => prefixed.elim

/-- With every owner drawn, the block's source configuration ignores the list of
other choices. -/
theorem assembleChain_all {setup : Setup (Player := Player) (L := L)}
    {mode : EventGraph.ExecutionMode} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : CommitPrefix program count)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (config : Config Player L Γ) (assignment : Assignment setup mode)
      (choices : List (OwnAction Player L)),
      assembleChain setup mode (fun _ => True) count program prefixed embedding config assignment
          choices =
        assembleChain setup mode (fun _ => True) count program prefixed embedding config
          assignment [] := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed embedding config assignment choices; rfl
  | succ count ih =>
      intro Γ names program prefixed embedding config assignment choices
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | commit name owner fresh guard next =>
          simp only [assembleChain, ↓reduceIte]
          exact ih next prefixed _ _ assignment choices

/-- The draws only assign the embedded commitments. -/
theorem assignChain_support_other (drawn : Player → Prop) [DecidablePred drawn] :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (prefixed : CommitPrefix program count)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (config : Config Player L Γ) (assignment : Assignment setup mode)
      (picked : Assignment setup mode),
      picked ∈ (assignChain setup mode drawn count program profile prefixed embedding config
        assignment).support →
      ∀ event : (serviceGraph setup mode).EventId,
        (∀ index, embedding.event index ≠ event) → picked event = assignment event := by
  intro count
  induction count with
  | zero =>
      intro Γ names program profile prefixed embedding config assignment picked member event _
      simp only [assignChain, PMF.mem_support_pure_iff] at member
      rw [member]
  | succ count ih =>
      intro Γ names program profile prefixed embedding config assignment picked member event
        outside
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | @commit Γ names name owner payload fresh guard next =>
          have tailOutside : ∀ index,
              (embedding.tail next (by simp [eventCount]) (fun _ => rfl)).event index ≠ event :=
            fun index => outside _
          by_cases own : drawn owner
          · simp only [assignChain, own, ↓reduceIte, PMF.mem_support_bind_iff] at member
            obtain ⟨choice, _, member⟩ := member
            rw [ih next _ prefixed _ _ _ picked member event tailOutside,
              Function.update_of_ne (Ne.symm (outside _))]
          · simp only [assignChain, own, ↓reduceIte] at member
            exact ih next _ prefixed _ _ assignment picked member event tailOutside

/-- The draws assign every embedded commitment of a drawn owner. -/
theorem assignChain_support_assigns (drawn : Player → Prop) [DecidablePred drawn] :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (prefixed : CommitPrefix program count)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (config : Config Player L Γ) (assignment : Assignment setup mode)
      (picked : Assignment setup mode),
      picked ∈ (assignChain setup mode drawn count program profile prefixed embedding config
        assignment).support →
      ∀ (index : Fin (eventCount program)) (owner : Player), index.val < count →
        (serviceGraph setup mode).actor? (embedding.event index) = some owner → drawn owner →
          ∃ action, picked (embedding.event index) = some action := by
  intro count
  induction count with
  | zero =>
      intro Γ names program profile prefixed embedding config assignment picked _ index owner
        below
      exact (Nat.not_lt_zero _ below).elim
  | succ count ih =>
      intro Γ names program profile prefixed embedding config assignment picked member index
        owner below owned honest
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | @commit Γ names name commitOwner payload fresh guard next =>
          let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
          have headOwned : (serviceGraph setup mode).actor?
              (embedding.event ⟨0, by simp [eventCount]⟩) = some commitOwner :=
            (serviceGraph setup mode).actor?_of_outputLayout_binding (commit_headLayout embedding)
          by_cases head : index.val = 0
          · have indexIs : index = ⟨0, by simp [eventCount]⟩ := Fin.ext head
            subst indexIs
            have ownerIs : owner = commitOwner := Option.some.inj (owned.symm.trans headOwned)
            subst ownerIs
            simp only [assignChain, honest, ↓reduceIte, PMF.mem_support_bind_iff] at member
            obtain ⟨choice, _, member⟩ := member
            refine ⟨cast (congrArg EventGraph.EventField.Action (commit_headLayout embedding).symm)
              choice, ?_⟩
            rw [assignChain_support_other drawn count next _ prefixed tailEmbedding _ _ picked
              member _ (fun tailIndex same => by
                have below : (embedding.event ⟨0, by simp [eventCount]⟩).val <
                    (tailEmbedding.event tailIndex).val :=
                  embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
                rw [same] at below
                exact Nat.lt_irrefl _ below), Function.update_self]
          · have tailIndex : (index.val - 1) < eventCount next := by
              have := index.isLt
              simp only [eventCount] at this
              omega
            have eventEq : embedding.event index =
                tailEmbedding.event ⟨index.val - 1, tailIndex⟩ := by
              congr 1
              apply Fin.ext
              simp only [Fin.val_cast, Fin.val_succ]
              omega
            rw [eventEq] at owned ⊢
            by_cases own : drawn commitOwner
            · simp only [assignChain, own, ↓reduceIte, PMF.mem_support_bind_iff] at member
              obtain ⟨choice, _, member⟩ := member
              exact ih next _ prefixed tailEmbedding _ _ picked member _ owner (by
                simp only; omega) owned honest
            · simp only [assignChain, own, ↓reduceIte] at member
              exact ih next _ prefixed tailEmbedding _ _ picked member _ owner (by
                simp only; omega) owned honest

/-- **Drawing in advance, then reading the others.** Draws of the drawn owners
at configurations whose views of every drawn player agree with the real ones,
followed by the source configuration with the other owners' choices supplied,
have the law of the leading commitments with those choices supplied. -/
theorem assignChain_assemble (drawn : Player → Prop) [DecidablePred drawn] :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (prefixed : CommitPrefix program count)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (drawConfig realConfig : Config Player L Γ) (assignment : Assignment setup mode)
      (choices : List (OwnAction Player L)),
      (∀ player, drawn player → drawConfig.view player = realConfig.view player) →
      (assignChain setup mode drawn count program profile prefixed embedding drawConfig
        assignment).map (fun picked => assembleChain setup mode drawn count program prefixed
          embedding realConfig picked choices) =
        listChain drawn count program profile prefixed realConfig choices := by
  intro count
  induction count with
  | zero =>
      intro Γ names program profile prefixed embedding drawConfig realConfig assignment choices _
      simp only [assignChain, assembleChain, listChain, PMF.pure_map]
  | succ count ih =>
      intro Γ names program profile prefixed embedding drawConfig realConfig assignment choices
        views
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | @commit Γ names name owner payload fresh guard next =>
          by_cases own : drawn owner
          · simp only [assignChain, assembleChain, listChain, own, ↓reduceIte, PMF.map_bind]
            rw [show drawConfig.view owner = realConfig.view owner from views owner own]
            apply bind_congr_on_support _
            intro choice _
            let event := embedding.event ⟨0, by simp [eventCount]⟩
            let updated := Function.update assignment event
              (some (cast (congrArg EventGraph.EventField.Action
                (commit_headLayout embedding).symm) choice))
            have kept : ∀ picked ∈ (assignChain setup mode drawn count next (afterCommit profile)
                prefixed (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
                (commitSuccessor name guard drawConfig choice) updated).support,
                assignedChoice picked event (commit_headLayout embedding) = choice := by
              intro picked member
              have same := assignChain_support_other drawn count next _ prefixed _ _ updated
                picked member event (fun index equal => by
                  have below : (embedding.event ⟨0, by simp [eventCount]⟩).val <
                      ((embedding.tail next (by simp [eventCount]) (fun _ => rfl)).event
                        index).val :=
                    embedding.strictMono (Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _))
                  rw [equal] at below
                  exact Nat.lt_irrefl _ below)
              simp only [assignedChoice, same, updated, Function.update_self, cast_cast, cast_eq]
            rw [← ih next _ prefixed _ (commitSuccessor name guard drawConfig choice)
              (commitSuccessor name guard realConfig choice) updated choices
              fun player honest => commitSuccessor_view_eq guard (views player honest)
                fun _ => rfl]
            apply map_congr_on_support _
            intro picked member
            rw [kept picked member]
          · simp only [assignChain, assembleChain, listChain, own, ↓reduceIte]
            exact ih next _ prefixed _ _ _ assignment choices.tail fun player honest =>
              commitSuccessor_view_eq guard (views player honest)
                fun same => (own (by rw [same]; exact honest)).elim

/-- **Equal configurations after two block runs.** Two runs from one
configuration that complete only bindings, complete the same events and agree
on their actions, leave the same store and the same own completions of every
player. -/
theorem config_eq_of_reaches (ordered : (serviceGraph setup mode).BarrierOrdered)
    {start left right : (serviceGraph setup mode).Config}
    (leftReach : ConfigReaches setup start left) (rightReach : ConfigReaches setup start right)
    (fresh : ∀ event, event ∉ start.cut.completed →
      event ∈ left.cut.completed ∨ event ∈ right.cut.completed →
        ∃ actor payload outputEq codeEq,
          nodeView (serviceGraph setup mode) event = .bind actor payload outputEq codeEq)
    (sameCompleted : ∀ event, event ∈ left.cut.completed ↔ event ∈ right.cut.completed)
    (sameActions : ∀ completion ∈ left.history, completion.event ∉ start.cut.completed →
      completion ∈ right.history) :
    left.store = right.store ∧ ∀ owner,
      (serviceGraph setup mode).ownCompletions owner left.history =
        (serviceGraph setup mode).ownCompletions owner right.history := by
  have view (owner : Player) := playerView_eq_of_reaches ordered leftReach rightReach owner fresh
    (fun event _ _ => sameCompleted event)
    (fun completion member _ _ notStart => sameActions completion member notStart)
  refine ⟨?_, fun owner => (view owner).2⟩
  funext field
  cases field with
  | inl input =>
      rw [EventGraph.Config.store_input, EventGraph.Config.store_input, leftReach.inputs,
        rightReach.inputs]
  | inr event =>
      rw [EventGraph.Config.store_output, EventGraph.Config.store_output]
      by_cases old : event ∈ start.cut.completed
      · rw [(leftReach.output_completed old).2, (rightReach.output_completed old).2]
      · by_cases anyDone : event ∈ left.cut.completed ∨ event ∈ right.cut.completed
        · obtain ⟨owner, payload, outputEq, codeEq, _⟩ := fresh event old anyDone
          have visible : (serviceGraph setup mode).fieldVisibleTo owner (.inr event) := by
            change ((serviceGraph setup mode).outputLayout event).VisibleTo owner
            rw [outputEq]
            rfl
          have stores := congrFun (view owner).1 (.inr event)
          rwa [EventGraph.playerStore_of_visible _ owner _ _ visible,
            EventGraph.playerStore_of_visible _ owner _ _ visible] at stores
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

/-- A checkpoint carries over to a configuration with the same store, the same
own completions and the same completed prefix. -/
theorem SourceCheckpoint.of_config_eq {Γ : SourceCtx Player L} {source : Config Player L Γ}
    {refs : ContextRefs (serviceGraph setup mode).layout Γ} {rank : Nat}
    {left right : (serviceGraph setup mode).Config}
    (checkpoint : SourceCheckpoint setup source refs rank left)
    (store : right.store = left.store)
    (own : ∀ owner, (serviceGraph setup mode).ownCompletions owner right.history =
      (serviceGraph setup mode).ownCompletions owner left.history)
    (ordered : right.cut.IsPrefix rank) :
    SourceCheckpoint setup source refs rank right := by
  refine ⟨by rw [store]; exact checkpoint.agrees, ?_, ordered⟩
  rw [← checkpoint.history]
  funext owner
  change decodeCompletions setup.program (setup.eventGraph.ownCompletions owner
      (right.history.map (setup.eventGraph.fromModeCompletion mode))) =
    decodeCompletions setup.program (setup.eventGraph.ownCompletions owner
      (left.history.map (setup.eventGraph.fromModeCompletion mode)))
  rw [← ownCompletions_fromModeCompletion, ← ownCompletions_fromModeCompletion, own owner]

/-- The source choice a store holds at an embedded commitment; failure when it
holds none. -/
def storedChoice {owner : Player} {payload : L.Ty}
    (store : EventGraph.Store (serviceGraph setup mode).layout)
    (event : (serviceGraph setup mode).EventId)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload) :
    PublicationResult (L.Val payload) :=
  match store (.inr event) with
  | some value => cast (congrArg EventGraph.EventField.Value outputEq) value
  | none => .failure

variable (setup mode) in
/-- The choices at the leading commitments of the owners not drawn, read from
`who`'s store. -/
def deviatorChoices (drawn : Player → Prop) [DecidablePred drawn] (who : Player) :
    (count : Nat) → {Γ : SourceCtx Player L} →
    {names : Finset VarId} → (program : SourceProgram Player L Γ names) →
    (prefixed : CommitPrefix program count) →
    OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program →
    EventGraph.Store (serviceGraph setup mode).layout → List (OwnAction Player L)
  | 0, _, _, _, _, _, _ => []
  | count + 1, _, _, .commit (payload := payload) name owner _ _ next, prefixed, embedding,
      store =>
      let rest := deviatorChoices drawn who count next prefixed
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) store
      if drawn owner then rest
      else
        .commit owner name payload (storedChoice store (embedding.event ⟨0, by simp [eventCount]⟩)
          (commit_headLayout embedding)) :: rest
  | _ + 1, _, _, .ret _, prefixed, _, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _, _ => prefixed.elim
  | _ + 1, _, _, .reveal _ _ _ _ _ _ _, prefixed, _, _ => prefixed.elim

/-- **The block decodes to its source configuration.** On a barrier-ordered
graph, a run from the start of a block of bindings that has completed exactly
the block, every drawn owner with its assigned action, decodes through the
leading commitments to the source configuration in which every drawn owner
takes its assigned choice and every other owner, which is `who`, its choices
read from `who`'s masked store.
The induction follows a configuration `virtual` that completes the block's
events below the current rank in source order with the run's actions. -/
theorem blockDecode (ordered : (serviceGraph setup mode).BarrierOrdered) {low high : Nat}
    (drawn : Player → Prop) [DecidablePred drawn] (who : Player)
    (undrawn : ∀ player, ¬ drawn player → player = who)
    (wholeProfile : BehavioralProfile setup.program)
    (start final : (serviceGraph setup mode).Config)
    (finalReach : ConfigReaches setup start final)
    (startPrefix : start.cut.IsPrefix low) (finalPrefix : final.cut.IsPrefix high)
    (bindings : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val → event.val < high →
      ∃ owner payload outputEq codeEq,
        nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    (assignment : Assignment setup mode)
    (assigned : ∀ event owner, low ≤ event.val → event.val < high →
      (serviceGraph setup mode).actor? event = some owner → drawn owner →
        ∃ action, assignment event = some action ∧
          (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈ final.history) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (prefixed : CommitPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program)
      (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
      (source : Config Player L Γ),
      CompiledPolicySuffix setup.program wholeProfile program profile refs source.revelations
        source.registry embedding refsBefore offset →
      ∀ virtual : (serviceGraph setup mode).Config,
      SourceCheckpoint setup source refs offset virtual →
      ConfigReaches setup start virtual →
      (∀ completion ∈ virtual.history, completion.event ∉ start.cut.completed →
        completion ∈ final.history) →
      low ≤ offset → offset + count = high →
      decodeSourcePrefix? program refs source.registry source.revelations embedding.ref count
          final.store (decodeHistory setup.program
            (final.history.map (setup.eventGraph.fromModeCompletion mode))) =
        some ((commitTail count program prefixed).lift (ProtocolState.entry _
          (assembleChain setup mode drawn count program prefixed embedding source assignment
            (deviatorChoices setup mode drawn who count program prefixed embedding
              ((serviceGraph setup mode).playerStore who final.store))))) := by
  intro count
  induction count with
  | zero =>
      intro Γ names program profile prefixed refs embedding refsBefore offset source _ virtual
        checkpoint virtualReach virtualFinal lowOffset offsetEnd
      simp only [Nat.add_zero] at offsetEnd
      subst offsetEnd
      have same := config_eq_of_reaches ordered virtualReach finalReach
        (fun event notStart done => by
          have lower : low ≤ event.val :=
            Nat.le_of_not_gt fun below => notStart ((startPrefix.2 event).mpr below)
          have upper : event.val < offset := by
            rcases done with inVirtual | inFinal
            · exact (checkpoint.ordered.2 event).mp inVirtual
            · exact (finalPrefix.2 event).mp inFinal
          exact bindings event lower upper)
        (fun event => by rw [checkpoint.ordered.2, finalPrefix.2])
        virtualFinal
      have finalCheckpoint := checkpoint.of_config_eq same.1.symm (fun owner => (same.2 owner).symm)
        finalPrefix
      rw [finalCheckpoint.decode program embedding.ref]
      rfl
  | succ count ih =>
      intro Γ names program profile prefixed refs embedding refsBefore offset source aligned
        virtual checkpoint virtualReach virtualFinal lowOffset offsetEnd
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | @commit Γ names name owner payload fresh guard next =>
          let index : Fin (eventCount (.commit name owner fresh guard next)) :=
            ⟨0, by simp [eventCount]⟩
          let event : (serviceGraph setup mode).EventId := embedding.event index
          have eventRank : event.val = offset := by
            simpa only [event, index, Nat.add_zero] using aligned.graphSuffix.rankEq index
          have outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload :=
            commit_headLayout embedding
          have codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout)
              outputEq) ((serviceGraph setup mode).nodes event) = .bind owner payload := by
            change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
              ((toEventGraph setup.program).nodes event) = _
            simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
          have owned : (serviceGraph setup mode).actor? event = some owner :=
            (serviceGraph setup mode).actor?_of_outputLayout_binding outputEq
          have decodedAction (choice : PublicationResult (L.Val payload)) :
              decodeEventAction setup.program event
                (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
                  some (.commit owner name payload choice) := by
            have lookup := aligned.actionEq index
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
            simpa [event, index, outputEq, decodeEventAction] using lookup
          have ready : virtual.cut.Ready event := by
            have active : offset < (serviceGraph setup mode).order.eventCount := by
              rw [← eventRank]
              exact event.isLt
            have prefixReady := checkpoint.ordered.ready active
            rwa [show (⟨offset, active⟩ : (serviceGraph setup mode).EventId) = event from
              Fin.ext eventRank.symm] at prefixReady
          have finalDone : event ∈ final.cut.completed := (finalPrefix.2 event).mpr (by omega)
          obtain ⟨⟨finalEventId, finalAction⟩, finalMember, finalEvent⟩ :=
            List.mem_map.mp ((final.history_exact event).mpr finalDone)
          change finalEventId = event at finalEvent
          subst finalEvent
          have notStart : event ∉ start.cut.completed := fun done => by
            have := (startPrefix.2 event).mp done
            omega
          -- The run's choice at the commitment.
          let choice : PublicationResult (L.Val payload) :=
            if drawn owner then assignedChoice assignment event outputEq
            else
              storedChoice ((serviceGraph setup mode).playerStore who final.store) event outputEq
          have choiceInFinal : (⟨event, cast (congrArg EventGraph.EventField.Action
              outputEq.symm) choice⟩ : (serviceGraph setup mode).Completion) ∈ final.history := by
            by_cases own : drawn owner
            · obtain ⟨action, assignedEq, member⟩ := assigned event owner (by omega) (by omega)
                owned own
              have choiceEq : choice = cast (congrArg EventGraph.EventField.Action outputEq)
                  action := by
                simp only [choice, own, ↓reduceIte, assignedChoice, assignedEq]
              rw [choiceEq, cast_cast, cast_eq]
              exact member
            · have isWho := undrawn owner own
              subst isWho
              have stored : final.outputs event = some (cast (congrArg EventGraph.EventField.Value
                  outputEq.symm) (cast (congrArg EventGraph.EventField.Action outputEq)
                    finalAction)) :=
                finalReach.binding_output finalMember
                  (fun inStart => notStart ((start.history_exact _).mp
                    (List.mem_map_of_mem inStart))) outputEq codeEq
              have visible : (serviceGraph setup mode).fieldVisibleTo owner (.inr event) := by
                change ((serviceGraph setup mode).outputLayout event).VisibleTo owner
                rw [outputEq]
                rfl
              have choiceEq : choice = cast (congrArg EventGraph.EventField.Action outputEq)
                  finalAction := by
                simp only [choice, own, ↓reduceIte, storedChoice,
                  EventGraph.playerStore_of_visible _ owner _ _ visible,
                  EventGraph.Config.store_output, stored, cast_cast]
              rw [choiceEq, cast_cast, cast_eq]
              exact finalMember
          have nextCheckpoint := checkpoint.commit_config name guard event eventRank ready outputEq
            (fun ref => refsBefore ref index) choice (decodedAction choice)
          have nextReach : ConfigReaches setup start (virtual.complete event ready
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
              (cast (congrArg EventGraph.EventField.Value outputEq.symm) choice)) :=
            virtualReach.trans_single (Or.inr ⟨event, ready,
              cast (congrArg EventGraph.EventField.Action outputEq.symm) choice, by
                rw [commit_step virtual event ready outputEq codeEq choice]
                exact (PMF.mem_support_pure_iff _ _).mpr rfl⟩)
          have nextFinal : ∀ completion ∈ (virtual.complete event ready
              (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice)
              (cast (congrArg EventGraph.EventField.Value outputEq.symm) choice)).history,
              completion.event ∉ start.cut.completed → completion ∈ final.history := by
            intro completion member notStart'
            rw [EventGraph.Config.complete_history] at member
            rcases List.mem_append.mp member with old | new
            · exact virtualFinal completion old notStart'
            · rw [List.mem_singleton] at new
              subst new
              exact choiceInFinal
          have step := ih next (afterCommit profile) prefixed _
            (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) _ (offset + 1)
            (commitSuccessor name guard source choice)
            (aligned.commitTail setup.program wholeProfile fresh guard next profile refs
              source.revelations source.registry embedding refsBefore offset) _ nextCheckpoint
            nextReach nextFinal (by omega) (by omega)
          rw [decodeSourcePrefix?_commit]
          change Option.map Sum.inr (decodeSourcePrefix? next _ _ _ _ count final.store _) = _
          by_cases own : drawn owner
          · simp only [choice, own, ↓reduceIte] at step
            simp only [assembleChain, deviatorChoices, own, ↓reduceIte]
            exact congrArg (Option.map Sum.inr) step
          · have isWho := undrawn owner own
            subst isWho
            simp only [choice, own, ↓reduceIte] at step
            simp only [assembleChain, deviatorChoices, own, ↓reduceIte, List.head?_cons,
              List.tail_cons, OwnAction.binding_commit]
            exact congrArg (Option.map Sum.inr) step

end Vegas
