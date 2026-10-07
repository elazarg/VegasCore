/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRevealDecode
import Vegas.Game.ServiceHonestLaw

/-! # The honest law of a block of disclosures

When the owners of a block's disclosures follow first-turn clients of a profile
that opens effectively, every disclosure of the block whose owner is one of
them completes with the decision to disclose exactly when its opening is
effective (`Vegas.openBlock_opened`), whatever the other players do. When every
player is such a client, the block decodes to the source configuration in
which the block's disclosures open in source order, deterministically
(`Vegas.honest_revealBlock_law`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- A disclosure decided to be opened completed with the decision to disclose
exactly when its opening is effective. -/
theorem DecidedEventPhase.opened {bound : (serviceGraph setup mode).EventId → Nat}
    {start execution : (serviceApplication setup mode deadline leaks).Execution}
    {decider : Player} {event : (serviceGraph setup mode).EventId} {owner : Player}
    {payload : L.Ty}
    {binding : EventGraph.FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    (phase : DecidedEventPhase bound start decider event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) execution)
    (done : event ∈ execution.application.config.cut.completed) :
    OpenedAt execution.application.config event := by
  unfold OpenedAt
  rw [node]
  intro action member
  rcases phase.completed done with ⟨decided, effective⟩ | ⟨ineffective, expired, expiry, member'⟩
  · have same := completion_eq_of_event member decided rfl
    simp only [EventGraph.Completion.mk.injEq, heq_eq_eq, true_and] at same
    subst same
    unfold EffectiveAction at effective
    rw [node] at effective
    simp only [cast_cast, cast_eq] at effective ⊢
    exact ⟨fun _ => effective trivial, fun _ => trivial⟩
  · have same := completion_eq_of_event member member' rfl
    simp only [EventGraph.Completion.mk.injEq, heq_eq_eq, true_and] at same
    subst same
    unfold ExpiryAction at expiry
    rw [node] at expiry
    unfold EffectiveAction at ineffective
    rw [node] at ineffective
    simp only [cast_cast, cast_eq, forall_const] at ineffective
    simp only [expiry, Bool.false_eq_true, false_iff]
    exact ineffective

/-- **Opened disclosures.** On a reveal-relaxed graph, along a run of a block of
disclosures from its start, under the asynchronous contract with
`delay + bound < deadline`, every disclosure of the block whose owner satisfies
`drawn` and follows its client with the block's openings assigned completes, if
at all, with the decision to disclose exactly when its opening is effective.
The other players are arbitrary. -/
theorem openBlock_opened {low : Nat} {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (drawn : Player → Prop)
    [DecidablePred drawn] (others : Player → (serviceApplication setup mode deadline leaks).Policy)
    (start : (serviceApplication setup mode deadline leaks).Execution)
    (startPrefix : start.application.config.cut.IsPrefix low)
    (startUntouched : ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val →
      Untouched setup leaks event start)
    (startOwn : ∀ owner, drawn owner → OwnSubmissionsAtTurn setup leaks start owner)
    (startAnswered : ActivationsAnswered setup leaks start)
    (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
    (refs : ContextRefs (graphLayout setup.program) Γ) (revelations : Revelations Γ)
    (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (refsBefore : ContextRefsBefore refs embedding)
    (suffix : CompiledSuffix setup.program program refs revelations registry embedding refsBefore
      low)
    (rounds remaining : Nat)
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨remaining + rounds, none, start⟩))
    (final : (serviceApplication setup mode deadline leaks).Execution)
    (reached : final ∈ ((serviceApplication setup mode deadline leaks).runUntil scheduler
      (drawnPlayers bound turns wholeProfile drawn others
        (openAssignment setup mode drawn count program prefixed embedding (fun _ => none)))
      (BlockDone (low + count)) rounds start).support)
    (index : Fin (eventCount program)) (below : index.val < count)
    (drawnOwner : ∀ owner, eventOwner? program index = some owner → drawn owner)
    (done : embedding.event index ∈ final.application.config.cut.completed) :
    OpenedAt final.application.config (embedding.event index) := by
  obtain ⟨owner, payload, binding, checks, outputEq, codeEq, node, owned⟩ :=
    CompiledSuffix.revealPrefix_resolve count program prefixed refs revelations registry
      embedding refsBefore low suffix index below
  have rank : (embedding.event index).val = low + index.val := suffix.rankEq index
  have actor : (serviceGraph setup mode).actor? (embedding.event index) = some owner :=
    nodeView_resolve_actor outputEq codeEq
  have ownDrawn := drawnOwner owner owned
  let opening : (serviceGraph setup mode).Action (embedding.event index) :=
    cast (congrArg EventGraph.EventField.Action outputEq.symm) true
  have assigned := openAssignment_opens (setup := setup) (mode := mode) drawn count program
    prefixed embedding (fun _ => none) index below drawnOwner outputEq
  have untouched := startUntouched (embedding.event index) (by omega)
  have loud : ¬ SilentAction (embedding.event index) opening := by
    unfold SilentAction
    rw [node]
    simp [opening]
  have nonsample : ∀ other, (serviceGraph setup mode).outputLayout (embedding.event index) ≠
      .publicData other := by
    intro other same
    rw [outputEq] at same
    cases same
  have phase := DecidedEventPhase.runUntil contract timely actor nonsample loud untouched
    (players := drawnPlayers bound turns wholeProfile drawn others
      (openAssignment setup mode drawn count program prefixed embedding (fun _ => none)))
    (by
      simp only [drawnPlayers, ownDrawn, ↓reduceIte]
      exact assignedTurnPolicy_decidesAt bound turns wholeProfile owner _ _ opening assigned)
    (by
      simp only [drawnPlayers, ownDrawn, ↓reduceIte]
      exact assignedTurnPolicy_submitsAtTurn bound turns wholeProfile owner _)
    (BlockDone (low + count)) rounds remaining start trace
    (DecidedEventPhase.initial bound opening untouched (startOwn owner ownDrawn)
      (fun completed => by
        have := (startPrefix.2 _).mp completed
        omega))
    (startOwn owner ownDrawn) startAnswered final reached
  exact phase.opened node done

/-- The events of a block of leading disclosures are its embedded disclosures. -/
theorem RevealPrefix.embedded {low count : Nat} {Γ : SourceCtx Player L} {names : Finset VarId}
    {program : SourceProgram Player L Γ names} (prefixed : RevealPrefix program count)
    {refs : ContextRefs (graphLayout setup.program) Γ} {revelations : Revelations Γ}
    {registry : Registry Γ}
    {embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      program} {refsBefore : ContextRefsBefore refs embedding}
    (suffix : CompiledSuffix setup.program program refs revelations registry embedding refsBefore
      low)
    (event : (serviceGraph setup mode).EventId) (lower : low ≤ event.val)
    (upper : event.val < low + count) :
    ∃ index : Fin (eventCount program), index.val < count ∧ embedding.event index = event := by
  have within := prefixed.le_eventCount
  have below : event.val - low < count := by omega
  refine ⟨⟨event.val - low, Nat.lt_of_lt_of_le below within⟩, below, ?_⟩
  apply Fin.ext
  rw [suffix.rankEq]
  simp only
  omega

/-- The events of a block of leading disclosures are publications. -/
theorem RevealPrefix.publications {low count : Nat} {Γ : SourceCtx Player L}
    {names : Finset VarId} {program : SourceProgram Player L Γ names}
    (prefixed : RevealPrefix program count)
    {refs : ContextRefs (graphLayout setup.program) Γ} {revelations : Revelations Γ}
    {registry : Registry Γ}
    {embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      program} {refsBefore : ContextRefsBefore refs embedding}
    (suffix : CompiledSuffix setup.program program refs revelations registry embedding refsBefore
      low) :
    ∀ event : (serviceGraph setup mode).EventId, low ≤ event.val → event.val < low + count →
      ((serviceGraph setup mode).outputLayout event).IsPublication := by
  intro event lower upper
  obtain ⟨index, below, rfl⟩ := prefixed.embedded suffix event lower upper
  obtain ⟨_, _, _, _, outputEq, _, _, _⟩ :=
    CompiledSuffix.revealPrefix_resolve (mode := mode) count program prefixed refs revelations
      registry embedding refsBefore low suffix index below
  rw [outputEq]
  trivial

/-- **The honest block of disclosures.** On a reveal-relaxed graph, under the
asynchronous contract with `delay + bound < deadline`, when every player follows
the first-turn client of a source profile that opens effectively at a block of
disclosures, the run from completion boundaries at the block's start until the
block is done decodes, through its leading disclosures, to the source
configuration in which they open in source order. -/
theorem honest_revealBlock_law (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {low high : Nat} (wall : RevealBlockEnd setup mode high) {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    {Γ : SourceCtx Player L} {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (profile : BehavioralProfile program) (count : Nat) (prefixed : RevealPrefix program count)
    (positive : 0 < count)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (refsBefore : ContextRefsBefore refs embedding) (highEq : low + count = high)
    {Seed : Type} (prior : PMF Seed) (source : Seed → Config Player L Γ)
    (execution : Seed → (serviceApplication setup mode deadline leaks).Execution)
    (aligned : ∀ seed, CompiledPolicySuffix setup.program wholeProfile program profile refs
      (source seed).revelations (source seed).registry embedding refsBefore low)
    (opens : ∀ seed player, OpensThrough count program prefixed (source seed).registry
      (source seed).revelations (profile player))
    (checkpoint : ∀ seed, SourceCheckpoint setup (source seed) refs low
      (execution seed).application.config)
    (boundary : ∀ seed ∈ prior.support, CompletionBoundary setup leaks scheduler
      (serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
        wholeProfile) low (execution seed))
    (bounded : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon) :
    (prior.bind fun seed =>
      ((serviceApplication setup mode deadline leaks).runUntilHorizon scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
          wholeProfile) (BlockDone high) horizon (execution seed)).map fun final =>
        decodeSourcePrefix? program refs (source seed).registry (source seed).revelations
          embedding.ref count final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode)))) =
      (prior.map source).map fun config =>
        some ((revealTail count program prefixed).lift
          (ProtocolState.entry _ (openChain count program prefixed config))) := by
  let app := serviceApplication setup mode deadline leaks
  let others : Player → app.Policy := fun _ => app.silentPolicy
  subst highEq
  rw [show (prior.map source).map (fun config => some ((revealTail count program prefixed).lift
      (ProtocolState.entry _ (openChain count program prefixed config)))) =
    prior.bind (fun seed => PMF.pure (some ((revealTail count program prefixed).lift
      (ProtocolState.entry _ (openChain count program prefixed (source seed)))))) by
    rw [PMF.map_comp, ← PMF.bind_pure_comp]
    rfl]
  apply bind_congr_on_support _
  intro seed supported
  have start := boundary seed supported
  have suffix := (aligned seed).graphSuffix
  have publications := prefixed.publications (mode := mode) suffix
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler _ _
    (bounded seed supported) _ start.supported
  have ownSlots (owner : Player) :
      OwnSubmissionsAtTurn setup leaks (execution seed) owner ∧
        CanonicalSlotsUsed setup leaks (execution seed) owner :=
    canonicalSlots_roundsFrom scheduler _ owner (bound := bound)
      (firstTurnTiming setup turns mode) wholeProfile rfl _ _ start.supported
  have answered := roundsFrom_activationsAnswered _ _ start.supported
  have opened := drawnPlayers_runUntil_open relaxed wall bound turns wholeProfile
    (fun _ => True) others (execution seed) start.ordered start.untouched publications count
    program profile prefixed refs (source seed).registry (source seed).revelations embedding
    refsBefore low (aligned seed) (fun player _ => opens seed player) le_rfl rfl (fun _ => none)
    (fun _ _ none => by cases none) _ 0 (by simpa only [Nat.zero_add] using trace)
  -- Every run decodes to the opened block.
  have decoded (final : app.Execution)
      (reached : final ∈ (app.runUntil scheduler
        (drawnPlayers bound turns wholeProfile (fun _ => True) others
          (openAssignment setup mode (fun _ => True) count program prefixed embedding
            (fun _ => none))) (BlockDone (low + count))
        (horizon - (execution seed).environmentRecall.length) (execution seed)).support) :
      decodeSourcePrefix? program refs (source seed).registry (source seed).revelations
          embedding.ref count final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode))) =
        some ((revealTail count program prefixed).lift
          (ProtocolState.entry _ (openChain count program prefixed (source seed)))) := by
    have done := runUntil_blockDone_of_trace _ contract.completes (low + count) _ _ final trace
      reached
    have reach := runUntil_configReaches scheduler _ _ _ _ final reached
    have inside := runUntil_within (RevealBlockEnd.sealed relaxed wall publications)
      scheduler _ _ _ final (start.withinBlock (Nat.le_add_right _ _)) reached
    have finalPrefix : final.application.config.cut.IsPrefix (low + count) :=
      inside.within.isPrefix wall.1 done
    have agree : refs.Agrees (source seed).state final.application.config.store :=
      reach.agrees refs (source seed).state (checkpoint seed).agrees
        (fun ref producer fieldEq => by
          have before := refsBefore ref ⟨0, Nat.lt_of_lt_of_le positive prefixed.le_eventCount⟩
          rw [fieldEq] at before
          change producer.val < (embedding.event _).val at before
          rw [suffix.rankEq] at before
          exact (start.ordered.2 producer).mpr (by simpa using before))
    refine revealBlockDecode relaxed wholeProfile (execution seed).application.config
      final.application.config reach start.ordered finalPrefix publications ?_ count program
      profile prefixed refs embedding refsBefore low (source seed) (aligned seed) agree []
      (by rw [List.append_nil]; exact (checkpoint seed).history)
      (fun completion => by
        simp only [List.not_mem_nil, false_iff, not_and, not_lt]
        intro _ lower
        exact lower)
      List.Pairwise.nil le_rfl rfl
    intro event lower upper
    obtain ⟨index, below, rfl⟩ := prefixed.embedded suffix event lower upper
    exact openBlock_opened contract timely turns wholeProfile (fun _ => True) others
      (execution seed) start.ordered start.untouched (fun owner _ => (ownSlots owner).1)
      answered count program prefixed refs (source seed).revelations (source seed).registry
      embedding refsBefore suffix _ 0 (by simpa only [Nat.zero_add] using trace) final reached
      index below (fun _ _ => trivial) (done _ upper)
  unfold ReactiveApplication.runUntilHorizon
  rw [firstTurnProfile_eq_drawnPlayers bound turns wholeProfile others, opened]
  rw [map_congr_on_support _ (g := fun _ => some ((revealTail count program prefixed).lift
    (ProtocolState.entry _ (openChain count program prefixed (source seed)))))
    (fun final reached => decoded final reached), pmf_map_fun_const]

end Vegas
