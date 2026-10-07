/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceBlockPredraw
import Vegas.Game.ServiceOpeningClient
import Vegas.Game.ServiceRevealTail

/-! # A block of disclosures whose owners open

On a reveal-relaxed graph a maximal run of disclosures is a block: once the
events before it have completed, only its events can become ready until all of
them have completed (`Vegas.RevealBlockEnd.sealed`). When the owners of the
block's disclosures follow first-turn clients of a profile that opens
effectively, each of them decides to disclose at its first turn there, whatever
else of the block is still pending: the block's players run exactly as the
players whose clients are assigned the opening at every such disclosure
(`Vegas.drawnPlayers_runUntil_open`). The other players' policies are
arbitrary.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

variable (setup mode) in
/-- **The block's openings.** The assignment that, along the leading
disclosures, decides the opening at every disclosure of an owner satisfying
`drawn`. -/
def openAssignment (drawn : Player → Prop) [DecidablePred drawn] : (count : Nat) →
    {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) → (prefixed : RevealPrefix program count) →
    OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program →
    Assignment setup mode → Assignment setup mode
  | 0, _, _, _, _, _, assignment => assignment
  | count + 1, _, _, .reveal _ owner _ _ _ _ next, prefixed, embedding, assignment =>
      openAssignment drawn count next prefixed
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
        (if drawn owner then
          Function.update assignment (embedding.event ⟨0, by simp [eventCount]⟩)
            (some (cast (congrArg EventGraph.EventField.Action
              (reveal_head_layout embedding).symm) true))
        else assignment)
  | _ + 1, _, _, .ret _, prefixed, _, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _, _ => prefixed.elim
  | _ + 1, _, _, .commit _ _ _ _ _, prefixed, _, _ => prefixed.elim

/-- **Referenced fields other than publications are present.** At a
configuration that has completed every event below `low`, when the events from
`low` up to the residual's first event are publications, every field the
residual's context references, other than a publication, is present. -/
theorem refs_available_of_completed {Γ : SourceCtx Player L} {names : Finset VarId}
    {program : SourceProgram Player L Γ names}
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      program) (refsBefore : ContextRefsBefore refs embedding) (index : Fin (eventCount program))
    {low : Nat}
    (publications : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < (embedding.event index).val →
      ((serviceGraph setup mode).outputLayout event).IsPublication)
    (config : (serviceGraph setup mode).Config)
    (done : ∀ event : (serviceGraph setup mode).EventId, event.val < low →
      event ∈ config.cut.completed) :
    ∀ {readName : VarId} {cell : CellTy Player L} (ref : HasVar Γ readName cell),
      (∀ other, cell ≠ .publication other) → ((refs.get ref).get? config.store).isSome := by
  intro readName cell ref plain
  apply EventGraph.FieldRef.get?_isSome
  have before := refsBefore ref index
  have layoutEq := (refs.get ref).layout_eq
  generalize (refs.get ref).field = field at before layoutEq ⊢
  cases field with
  | inl input => simp [EventGraph.Config.store]
  | inr producer =>
      change producer.val < (embedding.event index).val at before
      have below : producer.val < low := by
        by_contra notBelow
        have publication := publications producer (Nat.le_of_not_gt notBelow) before
        change (outputLayout setup.program producer).IsPublication at publication
        change outputLayout setup.program producer = cellField cell at layoutEq
        rw [layoutEq] at publication
        cases cell with
        | publication other => exact plain other rfl
        | publicData _ => exact publication
        | privateInput _ _ => exact publication
        | commitment _ _ => exact publication
      rw [EventGraph.Config.store_output, config.output_available]
      exact done producer below

/-- **Opening a block of disclosures.** From the start of a block of
disclosures on a reveal-relaxed graph, the block's players with some
disclosures already assigned run, until the block is done, as the block's
players with the opening assigned at every remaining disclosure of an owner
satisfying `drawn`, when those owners follow first-turn clients of a profile
that opens effectively there. The policies of the players not drawn are
arbitrary. The induction follows the leading disclosures of a residual program
at the block's current rank `offset`. -/
theorem drawnPlayers_runUntil_open (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {low high : Nat} (wall : RevealBlockEnd setup mode high) {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (drawn : Player → Prop)
    [DecidablePred drawn] (others : Player → (serviceApplication setup mode deadline leaks).Policy)
    (start : (serviceApplication setup mode deadline leaks).Execution)
    (startPrefix : start.application.config.cut.IsPrefix low)
    (startUntouched : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      Untouched setup leaks event start)
    (publications : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      event.val < high → ((serviceGraph setup mode).outputLayout event).IsPublication) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (prefixed : RevealPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ) (registry : Registry Γ)
      (revelations : Revelations Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program)
      (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix setup.program wholeProfile program profile refs revelations
        registry embedding refsBefore offset →
      (∀ player, drawn player →
        OpensThrough count program prefixed registry revelations (profile player)) →
      low ≤ offset → offset + count = high →
      ∀ assignment : Assignment setup mode,
      (∀ event action, assignment event = some action → low ≤ event.val ∧ event.val < offset) →
      ∀ (rounds remaining : Nat),
      ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
        horizon scheduler).Trace (some ⟨remaining + rounds, none, start⟩) →
      (serviceApplication setup mode deadline leaks).runUntil scheduler
          (drawnPlayers bound turns wholeProfile drawn others assignment) (BlockDone high)
          rounds start =
        (serviceApplication setup mode deadline leaks).runUntil scheduler
          (drawnPlayers bound turns wholeProfile drawn others
            (openAssignment setup mode drawn count program prefixed embedding assignment))
          (BlockDone high) rounds start := by
  let app := serviceApplication setup mode deadline leaks
  have lowHigh (offset count : Nat) (lowOffset : low ≤ offset) (offsetEnd : offset + count = high) :
      low ≤ high := by omega
  have sealed := RevealBlockEnd.sealed relaxed wall publications
  intro count
  induction count with
  | zero =>
      intro Γ names program profile prefixed refs registry revelations embedding refsBefore
        offset _ _ _ _ assignment _ rounds remaining _
      rfl
  | succ count ih =>
      intro Γ names program profile prefixed refs registry revelations embedding refsBefore
        offset aligned opens lowOffset offsetEnd assignment assignedRange rounds remaining trace
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
          have owned : (serviceGraph setup mode).actor? event = some owner := by
            change (toEventGraph setup.program).actor? event = some owner
            simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
          have tailAligned := aligned.revealTail setup.program wholeProfile fresh selected
            unresolved next profile refs revelations registry embedding refsBefore offset
          have eventLow : low ≤ event.val := by omega
          by_cases own : drawn owner
          · let opening : (serviceGraph setup mode).Action event :=
              cast (congrArg EventGraph.EventField.Action (reveal_head_layout embedding).symm)
                true
            have unassigned : assignment event = none := by
              cases assigned : assignment event with
              | none => rfl
              | some action =>
                  have range := assignedRange event action assigned
                  omega
            have selfPolicy : drawnPlayers bound turns wholeProfile drawn others assignment owner =
                assignedTurnPolicy bound turns wholeProfile owner assignment := by
              simp only [drawnPlayers, own, ↓reduceIte]
            have shape : drawnPlayers bound turns wholeProfile drawn others assignment =
                Function.update (drawnPlayers bound turns wholeProfile drawn others assignment)
                  owner (assignedTurnPolicy bound turns wholeProfile owner assignment) := by
              rw [← selfPolicy, Function.update_eq_self]
            have holds : WithinBlock low high start :=
              ⟨startPrefix.within (lowHigh offset (count + 1) lowOffset offsetEnd),
                fun other above => startUntouched other
                  (Nat.le_trans (lowHigh offset (count + 1) lowOffset offsetEnd) above)⟩
            have preserved : ∀ (rest : Nat) (execution : app.Execution),
                (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
                  (some ⟨rest + 1, none, execution⟩) →
                WithinBlock low high execution →
                ¬ BlockDone high execution →
                ∀ next ∈ (app.round scheduler (Function.update
                  (drawnPlayers bound turns wholeProfile drawn others assignment) owner
                  (assignedTurnPolicy bound turns wholeProfile owner assignment))
                  execution).support,
                  WithinBlock low high next := by
              intro rest execution _ inside running next reached
              exact round_within sealed scheduler _ execution next inside running reached
            have policy : ∀ (rest : Nat) (execution : app.Execution),
                (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
                  (some ⟨rest + 1, none, execution⟩) →
                WithinBlock low high execution →
                ¬ BlockDone high execution →
                ∀ command ∈ (scheduler execution.environmentRecall
                  (execution.observeEnvironment app)).support,
                ∀ middle ∈ (execution.environmentStep app command).support,
                  command.actor? app = some owner →
                  serviceTurn setup mode deadline leaks owner event (middle.recall owner)
                    (middle.observe app owner) = some 0 →
                  serviceCanonicalPolicy setup mode deadline leaks wholeProfile owner
                      (middle.recall owner) (middle.observe app owner) =
                    (PMF.pure opening).map fun action =>
                        (serviceRuntime setup mode deadline).canonicalServiceDecision
                      leaks owner (middle.recall owner) (middle.observe app owner) event
                          action := by
              intro rest execution _ inside _ command _ middle moved active first
              have activateIs : command = .activate owner := by
                cases command with
                | activate actor => cases active; rfl
                | «include» => cases active
                | application => cases active
                | wait => cases active
              subst activateIs
              have sameApp := activation_application setup leaks execution middle owner moved
              have turn : middle.application.publicView.ownTurn? owner = some event :=
                (sourceServiceTurn_first first).1
              have readyNow : middle.application.config.cut.Ready event :=
                (middle.application.publicView_eventReady event).mp
                  (PublicView.ownTurn?_spec _ owner event turn).1
              have available : ∀ {readName : VarId} {cell : CellTy Player L}
                  (ref : HasVar Γ readName cell), (∀ other, cell ≠ .publication other) →
                    ((refs.get ref).get? middle.application.config.store).isSome :=
                fun ref plain => refs_available_of_completed refs embedding refsBefore index
                  (fun other lower upper => publications other lower (by omega))
                  middle.application.config (fun other below => by
                    rw [sameApp]
                    exact inside.within.1 other below) ref plain
              rw [PMF.pure_map]
              exact serviceCanonicalPolicy_reveal_opening setup leaks fresh selected unresolved
                next wholeProfile profile refs registry revelations embedding refsBefore offset
                aligned (opens owner own).1 middle readyNow available
            have clean : ∀ entry ∈ start.recall owner,
                entry.beforeView.application.publicView.ownTurn? owner ≠ some event :=
              fun entry member turn => startUntouched event eventLow owner entry member
                (PublicView.ownTurn?_spec _ owner event turn).1
            conv_lhs => rw [shape]
            rw [assignedTurnPolicy_runUntil_mixture (serviceInitialLaw setup mode) horizon scheduler
              (drawnPlayers bound turns wholeProfile drawn others assignment) bound turns
              wholeProfile owner assignment event unassigned owned (PMF.pure opening)
              (BlockDone high) (WithinBlock low high) policy preserved rounds remaining start trace
              holds clean, PMF.pure_bind,
              ← drawnPlayers_update bound turns wholeProfile drawn others assignment owned own]
            have later := ih next (afterReveal profile) prefixed _ _ _
              (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) _ (offset + 1)
              tailAligned (fun player drawnPlayer => (opens player drawnPlayer).2) (by omega)
              (by omega) (Function.update assignment event (some opening))
              (fun other action assigned => by
                by_cases same : other = event
                · subst same
                  omega
                · rw [Function.update_of_ne same] at assigned
                  have range := assignedRange other action assigned
                  omega)
              rounds remaining trace
            rw [later]
            simp only [openAssignment, own, ↓reduceIte]
            rfl
          · have later := ih next (afterReveal profile) prefixed _ _ _
              (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) _ (offset + 1)
              tailAligned (fun player drawnPlayer => (opens player drawnPlayer).2) (by omega)
              (by omega) assignment
              (fun other action assigned => by
                have range := assignedRange other action assigned
                omega)
              rounds remaining trace
            rw [later]
            simp only [openAssignment, own, ↓reduceIte]

/-- The block's openings leave every event outside the leading disclosures as
assigned. -/
theorem openAssignment_of_ne (drawn : Player → Prop) [DecidablePred drawn] :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (assignment : Assignment setup mode) (event : (serviceGraph setup mode).EventId),
      (∀ index : Fin (eventCount program), index.val < count → embedding.event index ≠ event) →
      openAssignment setup mode drawn count program prefixed embedding assignment event =
        assignment event := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed embedding assignment event _; rfl
  | succ count ih =>
      intro Γ names program prefixed embedding assignment event outside
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | @reveal Γ names published owner name payload fresh selected unresolved next =>
          simp only [openAssignment]
          rw [ih next prefixed _ _ event (fun index below => outside
            ⟨index.val + 1, by simp only [eventCount]; omega⟩ (by simp only; omega))]
          split_ifs
          · rw [Function.update_of_ne (outside ⟨0, by simp [eventCount]⟩ (by simp)).symm]
          · rfl

/-- **The block's openings open.** Every leading disclosure of an owner
satisfying `drawn` is assigned the opening. -/
theorem openAssignment_opens (drawn : Player → Prop) [DecidablePred drawn] :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (assignment : Assignment setup mode) (index : Fin (eventCount program)),
      index.val < count →
      (∀ owner, eventOwner? program index = some owner → drawn owner) →
      ∀ {payload : L.Ty}
        (outputEq : (serviceGraph setup mode).outputLayout (embedding.event index) =
          .publication payload),
      openAssignment setup mode drawn count program prefixed embedding assignment
          (embedding.event index) =
        some (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed embedding assignment index below; omega
  | succ count ih =>
      intro Γ names program prefixed embedding assignment index below drawnOwner payload
        outputEq
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | @reveal Γ names published owner name headPayload fresh selected unresolved next =>
          rcases index with ⟨position, bounded⟩
          cases position with
          | zero =>
              have ownDrawn : drawn owner := drawnOwner owner (by simp [eventOwner?])
              simp only [openAssignment, ownDrawn, ↓reduceIte]
              rw [openAssignment_of_ne drawn count next prefixed _ _ _ (fun tailIndex _ same => by
                have := embedding.strictMono.injective same
                simp [Fin.ext_iff] at this)]
              rw [Function.update_self]
          | succ position =>
              have tailBelow : position < count := by simp at below; omega
              simp only [openAssignment]
              exact ih next prefixed
                (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) _
                ⟨position, by simp only [eventCount] at bounded; omega⟩ tailBelow
                (fun owner tailOwner => drawnOwner owner (by
                  simpa [eventOwner?] using tailOwner)) outputEq

/-- **Leading disclosures compile to resolutions.** In a compiled suffix, every
event among the first `count` leading disclosures has a resolution node, owned
by the disclosure's owner. -/
theorem CompiledSuffix.revealPrefix_resolve :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (_prefixed : RevealPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (revelations : Revelations Γ) (registry : Registry Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledSuffix setup.program program refs revelations registry embedding refsBefore
        offset →
      ∀ index : Fin (eventCount program), index.val < count →
        ∃ owner payload binding checks outputEq codeEq,
          EventGraphRuntime.nodeView (serviceGraph setup mode) (embedding.event index) =
            .resolve owner payload binding checks outputEq codeEq ∧
          eventOwner? program index = some owner := by
  intro count
  induction count with
  | zero => intro _ _ _ _ _ _ _ _ _ _ _ index below; omega
  | succ count ih =>
      intro Γ names program prefixed refs revelations registry embedding refsBefore offset
        suffix index below
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | @reveal Γ names published owner name payload fresh selected unresolved next =>
          rcases index with ⟨position, bounded⟩
          cases position with
          | zero =>
              have outputEq : (serviceGraph setup mode).outputLayout
                  (embedding.event ⟨0, bounded⟩) = .publication payload := by
                change outputLayout setup.program _ = _
                simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, bounded⟩
              have codeEq : cast (congrArg (EventGraph.EventCode
                  (serviceGraph setup mode).layout) outputEq)
                  ((serviceGraph setup mode).nodes (embedding.event ⟨0, bounded⟩)) =
                    .resolve owner payload (refs.get selected)
                      (compileChecks (published := published) refs registry revelations
                        selected) := by
                change cast (congrArg (EventGraph.EventCode (graphLayout setup.program))
                  outputEq) ((toEventGraph setup.program).nodes _) = _
                simpa [compileRankedNodes] using suffix.nodeEq ⟨0, bounded⟩
              exact ⟨owner, payload, _, _, outputEq, codeEq,
                EventGraphRuntime.nodeView_eq_resolve _ _, by simp [eventOwner?]⟩
          | succ position =>
              obtain ⟨owner', payload', binding', checks', outputEq', codeEq', node', owned'⟩ :=
                ih next prefixed _ _ _
                  (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) _ (offset + 1)
                  (suffix.revealTail setup.program fresh selected unresolved next refs
                    revelations registry embedding refsBefore offset)
                  ⟨position, by simp only [eventCount] at bounded; omega⟩
                  (by simp at below; omega)
              exact ⟨owner', payload', binding', checks', outputEq', codeEq', node', by
                simpa [eventOwner?] using owned'⟩

end Vegas
