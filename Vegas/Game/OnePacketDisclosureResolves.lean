/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.IntendedForPlayer
import Vegas.Game.OnePacketOpeningUnique

/-! # Disclosures resolve at states forced for the observer

From a point intended for a player at which no reveal of the player has failed,
a step in which the player discloses leaves no failed reveal of the player
(`Vegas.SourceProgram.ProtocolState.not_revealFailed_step`). The source action
decoded from a disclosure discloses
(`Vegas.SourceProgram.decodeEventAction_disclosure_true`), and a point decoded
past a reveal whose stored publication is a failure shows that reveal failed
(`Vegas.SourceProgram.ProtocolState.revealFailed_of_decode_failure`).

For a well-formed setup, along every history the configuration decodes to a
point intended for a given player or at which it owes a failed reveal
(`Vegas.decodedState_intendedFor_or_owes`). At a state forced for the observer,
another player owes no failed reveal, so its point is intended for it; were its
disclosure's resolution a failure, completing the reveal by disclosing would
decode to a failed reveal of a disclosing player intended for, which cannot be.
So every other player's canonical disclosure resolves
(`Vegas.disclosureResolves_of_forced`).
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The source action decoded from a disclosure discloses. -/
theorem decodeEventAction_disclosure_true {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (bound : count < eventCount program) {payload : L.Ty}
      (outputEq : outputLayout program ⟨count, bound⟩ = .publication payload),
      OwnAction.disclosure (decodeEventAction program ⟨count, bound⟩
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)) = true := by
  induction program with
  | ret _ =>
      intro count bound
      simp [eventCount] at bound
  | sample _ _ _ next ih =>
      intro count bound payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | commit name commitOwner fresh guard next ih =>
      intro count bound payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | reveal published revealOwner name fresh source unresolved next ih =>
      intro count bound payload outputEq
      cases count with
      | zero => rfl
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq

namespace ProtocolState

/-- No reveal has failed at a program's entry. -/
theorem not_revealFailed_entry (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    ¬ RevealFailed who program (entry program config) := by
  cases program <;> exact fun failed => failed

/-- **A disclosing player's reveals stay successful.** From a point intended for
a player at which no reveal of the player has failed, a step in which the
player discloses at its reveals leaves no failed reveal of the player. -/
theorem not_revealFailed_step (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → (target : ProtocolState program) →
    IntendedFor who program state → ¬ RevealFailed who program state →
    OwnAction.disclosure (joint who) = true →
    target ∈ (step program state joint).support → ¬ RevealFailed who program target
  | _, _, .ret _, _, _, _, _, clean, _, reached => by
      rw [step, PMF.mem_support_pure_iff] at reached
      rw [reached]
      exact clean
  | _, _, .sample _ _ _ next, state, joint, target, intended, clean, discloses, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          exact not_revealFailed_entry who next _
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact not_revealFailed_step who next rest joint after intended clean discloses supported
  | _, _, .commit _ _ _ _ next, state, joint, target, intended, clean, discloses, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          exact not_revealFailed_entry who next _
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact not_revealFailed_step who next rest joint after intended clean discloses supported
  | _, _, .reveal published owner name fresh source _ next, state, joint, target, intended,
      clean, discloses, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          rintro (⟨same, failed⟩ | later)
          · subst same
            rw [discloses] at failed
            obtain ⟨_, value, opened⟩ := Config.IntendedFor.reveal_own intended fresh source
            rw [base_entry, opened] at failed
            cases failed
          · exact not_revealFailed_entry who next _ later
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rintro (⟨same, failed⟩ | later)
          · exact clean (Or.inl ⟨same, (base_step next rest joint after supported) ▸ failed⟩)
          · exact not_revealFailed_step who next rest joint after intended
              (fun earlier => clean (Or.inr earlier)) discloses supported later

/-- **A stored failed publication is a failed reveal.** A point decoded past a
reveal of `who` whose stored publication is a failure shows `who`'s reveal
failed. -/
theorem revealFailed_of_decode_failure {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (state : ProtocolState program) (bound : count < eventCount program) (who : Player)
      (payload : L.Ty) (publication : outputLayout program ⟨count, bound⟩ = .publication payload),
      decodeSourcePrefix? program refs registry revelations outputs (count + 1) store history =
          some state →
      eventOwner? program ⟨count, bound⟩ = some who →
      (outputs ⟨count, bound⟩).get? store = some (cast
        (congrArg EventGraph.EventField.Value publication.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload))) →
      RevealFailed who program state := by
  induction program with
  | ret _ =>
      intro count _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro count refs registry revelations outputs store history state bound who payload
        publication decoded owned read
      cases count with
      | zero => cases publication
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) who payload
            publication restDecoded owned read
  | commit name owner fresh guard next ih =>
      intro count refs registry revelations outputs store history state bound who payload
        publication decoded owned read
      cases count with
      | zero => cases publication
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) who payload
            publication restDecoded owned read
  | reveal published owner name fresh source unresolved next ih =>
      intro count refs registry revelations outputs store history state bound who payload
        publication decoded owned read
      cases count with
      | zero =>
          cases Option.some.inj owned
          cases publication
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          obtain ⟨cells, cellsDecoded, rfl⟩ := Option.map_eq_some_iff.mp restDecoded
          refine Or.inl ⟨rfl, ?_⟩
          rw [base_entry]
          unfold decodeState? at cellsDecoded
          erw [read] at cellsDecoded
          obtain ⟨head, headEq, rest⟩ := Option.bind_eq_some_iff.mp cellsDecoded
          obtain ⟨tail, _, cellsEq⟩ := Option.bind_eq_some_iff.mp rest
          cases Option.some.inj headEq
          cases Option.some.inj cellsEq
          rfl
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact Or.inr (ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) who
            payload publication restDecoded owned read)

end ProtocolState

end Vegas.SourceProgram

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Being intended for a player or owing a failed reveal is closed under every
source step. -/
theorem intendedForOrOwes_stepClosed (who : Player) :
    StepClosed setup (fun point => ProtocolState.IntendedFor who setup.program point ∨
      ProtocolState.OwesFailure who setup.program point) :=
  fun state joint target holds reached =>
    ProtocolState.intendedForOrOwes_step who setup.program state joint target holds reached

/-- **Intended for a player or owing along every history.** For a well-formed
setup, along every history of a response menu of the supplied runtime, under any
scheduler, the configuration decodes to a point intended for the player or at
which the player owes a failed reveal. -/
theorem decodedState_intendedFor_or_owes (wellFormed : setup.WellFormed) (who : Player)
    (profile : BehavioralProfile setup.program)
    (menu : (application setup runtime leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler) :
    ∀ {state} (_ : (menu.protocol (initialLaw setup) horizon scheduler).Trace state)
      (control : (application setup runtime leaks).Control), state = some control →
      DecodedState setup runtime leaks profile (fun point =>
        ProtocolState.IntendedFor who setup.program point ∨
          ProtocolState.OwesFailure who setup.program point) (some control) := by
  intro state trace control current
  refine decodedState_history_of_stepClosed (intendedForOrOwes_stepClosed
    who) ?_
    menu horizon scheduler trace control current
  intro initial member
  exact Or.inl (ProtocolState.intendedFor_entry setup.program _
    ((Config.initial_intended wellFormed member).intendedFor who))

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- **Disclosures resolve at states forced for the observer.** For a
well-formed setup, along every history of the one-packet game at a state forced
for the observer, every other player's canonical disclosure at its pending
reveal transmits: the player owes no failed reveal, so the decoded point is
intended for it, and its disclosure there publishes a value. -/
theorem disclosureResolves_of_forced (wellFormed : setup.WellFormed)
    {control : (application setup runtime leaks).Control}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control))
    (who actor : Player) (forced : ForcedState setup runtime leaks who (some control))
    (other : actor ≠ who) :
    DisclosureResolves setup runtime leaks actor (control.execution.recall actor)
      (control.execution.observe (application setup runtime leaks) actor) := by
  intro event pending owner payload binding checks outputEq codeEq node
  obtain ⟨turn, _, owned, _⟩ := pendingEvent_spec (runtime := runtime) (setup := setup) pending
  have ownerEq : owner = actor :=
    Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
  subst ownerEq
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have facts := legalFacts setup leaks horizon scheduler control rawTrace
  have ready : control.execution.application.config.cut.Ready event :=
    (control.execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ owner event turn).1
  have available : (EventGraph.EventCode.resolveOutput? binding checks true
      control.execution.application.config.store).isSome = true := by
    apply EventGraph.EventCode.resolveOutput?_isSome
    intro field member
    apply control.execution.application.config.read_available ready
    rw [← EventGraph.EventCode.readFields_cast outputEq ((graph setup).nodes event), codeEq]
    exact member
  obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp available
  have discloses : (cast (congrArg EventGraph.EventField.Action outputEq)
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) : Bool) = true := by
    simp
  cases result with
  | success value =>
      obtain ⟨_, _, _, _, packet⟩ := EventGraphRuntime.reactiveResolutionPacket_provenance
        runtime leaks control.execution.application facts.binding owner event payload
        binding checks outputEq _ discloses value resolved
      simp only [EventGraphRuntime.canonicalServiceDecision,
        EventGraphRuntime.canonicalReactiveDecision, node]
      change ((EventGraphRuntime.reactiveNormalization runtime leaks).action owner
        (control.execution.recall owner) (control.execution.observe (application setup runtime
          leaks)
          owner)
        ⟨(EventGraphRuntime.reactiveResolutionPacket owner event payload binding checks
          outputEq _ (runtime.reactiveApplication leaks |>.observePlayer
            control.execution.application owner)).map fun packet =>
          (disclosureSubmission packet).normalizeReactive owner
            (runtime.reactiveApplication leaks |>.observePlayer
              control.execution.application owner) []⟩).transmission ≠ none
      rw [packet]
      simp only [Option.map_some, ReactiveApplication.SubmissionNormalization.action, ne_eq,
        reduceCtorEq, not_false_eq_true]
  | failure =>
      exfalso
      -- The decoded point is intended for the actor and shows no failed reveal of it.
      obtain ⟨rank, ⟨residual⟩, holds⟩ := decodedState_intendedFor_or_owes (runtime := runtime)
        wellFormed owner
        (failureProfile setup.program) _ horizon scheduler trace
        control rfl
      obtain ⟨forcedRank, point, ordered, decoded, forcedPoint⟩ := forced
      have sameRank := EventOrder.Cut.IsPrefix.unique ordered residual.checkpoint.ordered
      subst sameRank
      have pointEq : residual.lift (ProtocolState.entry residual.program residual.source) =
          point := Option.some.inj (residual.decode.symm.trans decoded)
      obtain ⟨notExcluded, notOwed⟩ := forcedPoint.2 owner other
      have intended : ProtocolState.IntendedFor owner setup.program point := by
        rcases holds _ decoded with intended | owed
        · exact intended
        · exact (notOwed owed).elim
      have clean : ¬ ProtocolState.RevealFailed owner setup.program point := fun failed =>
        notExcluded (ProtocolState.RevealFailed.excluded setup.program _ failed)
      -- Complete the reveal by disclosing: its output is a failure.
      have stepEq := control.execution.application.config.step_eq_map_of_code event ready
        outputEq _ codeEq true (PMF.pure .failure)
        (by rw [EventGraph.EventCode.resolve_eval?, resolved]; rfl)
      rw [PMF.pure_map] at stepEq
      have member : control.execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm)
            (PublicationResult.failure : PublicationResult (L.Val payload))) ∈
          (control.execution.application.config.step event ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) true)).support := by
        rw [stepEq]
        exact (PMF.mem_support_pure_iff _ _).mpr rfl
      obtain ⟨next, reached⟩ := residual.step event ready _ _ member
      rw [pointEq] at reached
      have atRank := (ready_iff_rank setup _ forcedRank ordered event).mp ready
      subst atRank
      have nextDecoded := next.decode
      unfold sourceServicePrefix? serviceSourcePrefix? at nextDecoded
      have failedNext := ProtocolState.revealFailed_of_decode_failure setup.program event.val
        (ContextRefs.initial setup.context (outputLayout setup.program)) []
        (Revelations.initial setup.context) (outputRef setup.program) _ _ _ event.isLt owner
        payload outputEq nextDecoded ((eventOwner?_eq_actor setup.program event).trans owned)
        (by
          change (control.execution.application.config.complete event ready _ _).outputs
            event = _
          rw [EventGraph.Config.complete_output_same])
      exact ProtocolState.not_revealFailed_step owner setup.program _ _ _ intended clean
        (decodeEventAction_disclosure_true setup.program event.val event.isLt outputEq)
        reached failedNext

end Vegas
