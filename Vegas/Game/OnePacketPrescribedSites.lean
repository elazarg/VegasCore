/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateCompletion

/-! # Forced debt-free first activations

**Resolving disclosures transmit canonically.** When the canonical disclosure
at the player's pending reveal transmits, as it does at a debt-free forced
state, so do the canonical decisions of every encoded source action there other
than a refusal (`Vegas.canonicalTransmitsAt_of_disclosureResolves`).

**A forced debt-free first activation.** At a history of a first activation of
a forced player, where no player owes a failure at the decoded point, the
configuration is the completed prefix of the site's rank and decodes there to a
point of the intended game reached by the intended game
(`Vegas.firstActivation_history_facts`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **Resolving disclosures transmit canonically.** When the canonical
disclosure of `who` at its pending reveal transmits, so do the canonical
decisions of every encoded source action at it other than a refusal. -/
theorem canonicalTransmitsAt_of_disclosureResolves {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (resolves : DisclosureResolves setup leaks who
      past view) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who (some (past, view)) = some event) {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq) :
    CanonicalTransmitsAt setup leaks who past view event := by
  intro action graphAction encoded _ discloses
  have disclose := encodeEventAction?_discloses setup.program event action discloses
    graphAction encoded payload outputEq
  have graphEq : graphAction = cast (congrArg EventGraph.EventField.Action outputEq.symm) true := by
    rw [← disclose]
    simp
  rw [graphEq]
  exact resolves event pending who payload binding checks outputEq codeEq node

omit [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- **A forced debt-free first activation.** At a history of a first activation
of `who` for its pending event, forced for `who` with no player owing a failure
at the decoded point, `who` is deciding at an execution whose recall has never
activated the event, whose configuration is the completed prefix of the site's
rank and decodes there to a point of the intended game reached by the intended
game. -/
theorem firstActivation_history_facts (wellFormed : setup.WellFormed) {who : Player}
    (site : (onePacketN).InformationSite who) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    (first : ¬ LateDelivery setup leaks who site.1)
    (history : (onePacketN).InformationHistory who site.1)
    (forced : ForcedState setup leaks who history.1.state)
    (regular : ∀ point, nativeDecodedState setup leaks history.1.state = some point →
      ∀ player, ¬ ProtocolState.OwesFailure player setup.program point) :
    ∃ (remaining : Nat) (execution : (application setup leaks).Execution)
      (point : ProtocolState setup.program),
      history.1.state = some ⟨remaining, some who, execution⟩ ∧
      site.1 = some (execution.recall who, execution.observe (application setup leaks) who) ∧
      (∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry) ∧
      execution.application.config.cut.IsPrefix (siteRank site.1) ∧
      sourceServicePrefix? setup (siteRank site.1) execution.application.config = some point ∧
      ProtocolState.Intended setup.program point ∧ IntendedReached setup point := by
  let menu := bounds.onePacketMenu (runtime setup) leaks
  obtain ⟨start, observed⟩ := history
  change ForcedState setup leaks who start.state at forced
  change ∀ point, nativeDecodedState setup leaks start.state = some point → _ at regular
  have observedState : (application setup leaks).observe who start.state = site.1 :=
    (menu.info (initialLaw setup) horizon scheduler who start.trace).symm.trans observed
  rcases startState : start.state with _ | ⟨remaining, actor, execution⟩
  · rw [startState] at forced
    exact forced.elim
  rw [startState] at observedState regular forced
  have actorEq : actor = some who := by
    by_contra different
    simp only [ReactiveApplication.observe, different, ↓reduceIte] at observedState
    rw [← observedState] at pending
    cases pending
  subst actorEq
  simp only [ReactiveApplication.observe, ↓reduceIte] at observedState
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := startState ▸ start.trace
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    menu.toRawTrace (initialLaw setup) horizon scheduler trace
  have pendingAt : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event := by
    rw [observedState]
    exact pending
  obtain ⟨turn, _, owned, _⟩ := pendingEvent_spec pendingAt
  have never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry :=
    fun entry member activated => first
      ⟨_, _, event, observedState.symm, pending, entry, member, activated⟩
  -- The decoded point is intended and reached by the intended game.
  obtain ⟨point, pointDecoded, forcedPoint⟩ := (forcedState_iff_decodedPoint _).mp forced
  obtain ⟨found, ordered, _⟩ := pendingAt_history rawTrace
  have rankEq : siteRank site.1 = found := by
    rw [← observedState]
    change (execution.application.config.history.map EventGraph.Completion.event).length = found
    rw [List.length_map]
    exact history_length_of_isPrefix _ ordered
  have decoded : sourceServicePrefix? setup found execution.application.config = some point :=
    (decodedPoint_eq_of_isPrefix ordered).symm.trans pointDecoded
  obtain ⟨decodedRank, ⟨residual⟩, holds⟩ := decodedState_intended_or_owes wellFormed
    (failureProfile setup.program) menu horizon scheduler trace _ rfl
  have sameRank := isPrefix_unique residual.checkpoint.ordered ordered
  subst sameRank
  have residualDecoded := residual.decode
  generalize residual.lift (ProtocolState.entry residual.program residual.source) = residualPoint
    at residualDecoded
  rw [decoded, Option.some.injEq] at residualDecoded
  subst residualDecoded
  have intendedPoint : ProtocolState.Intended setup.program point := by
    rcases holds point decoded with intendedHere | ⟨player, owed⟩
    · exact intendedHere
    · exact (regular point pointDecoded player owed).elim
  obtain ⟨replay, replayed⟩ := intendedHistory?_isSome_of_debtFree wellFormed trace _ rfl
    (fun found foundDecoded player => regular found foundDecoded player)
  have reached : IntendedReached setup point :=
    ⟨replay, (intendedHistory?_state trace replayed).trans pointDecoded⟩
  have freshOf : ∀ control, ¬ StoreEventFailed control.execution.application.config.store
      event → siteFresh who site.1 control := fun control notFailed => by
    simpa only [siteFresh, pending] using notFailed
  rw [rankEq]
  exact ⟨remaining, execution, point, rfl, observedState.symm, never, ordered, decoded,
    intendedPoint, reached⟩

end Vegas
