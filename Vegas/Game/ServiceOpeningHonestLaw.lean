/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRevealLaw

/-! # The honest law of the opening clients on reveal-relaxed graphs

On a reveal-relaxed graph, such as that of the concurrent-reveal dependency
mode, a run splits into phases (`Vegas.ConcurrentPhaseEnds`): a maximal run of
commitments, a public sample, or a maximal run of disclosures. When every player
follows the first-turn client of a source profile that opens effectively, each
phase decodes to the source law of the profile
(`Vegas.openingHonestLaw`), and from initialization the typed outcome has the
source law of the profile (`Vegas.openingFirstTurn_readout_law`): a run of
disclosures opens in source order whatever order its disclosures complete in.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The number of leading disclosures of a program. -/
def leadingReveals : {Γ : SourceCtx Player L} → {names : Finset VarId} →
    SourceProgram Player L Γ names → Nat
  | _, _, .reveal _ _ _ _ _ _ next => leadingReveals next + 1
  | _, _, .ret _ => 0
  | _, _, .sample _ _ _ _ => 0
  | _, _, .commit _ _ _ _ _ => 0

/-- A program's leading disclosures are disclosures. -/
theorem leadingReveals_prefix : ∀ {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names), RevealPrefix program (leadingReveals program)
  | _, _, .reveal _ _ _ _ _ _ next => leadingReveals_prefix next
  | _, _, .ret _ => trivial
  | _, _, .sample _ _ _ _ => trivial
  | _, _, .commit _ _ _ _ _ => trivial

/-- After all its leading disclosures, a program has none left. -/
theorem leadingReveals_revealTail : ∀ {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names),
    leadingReveals (revealTail (leadingReveals program) program
      (leadingReveals_prefix program)).tail = 0
  | _, _, .reveal _ _ _ _ _ _ next => leadingReveals_revealTail next
  | _, _, .ret _ => rfl
  | _, _, .sample _ _ _ _ => rfl
  | _, _, .commit _ _ _ _ _ => rfl

/-- **The phases of a program on a reveal-relaxed graph.** A maximal run of
commitments is one phase, a maximal run of disclosures is one phase, and a
sample is a phase of its own. Each phase is named by the rank its end leaves
completed. -/
inductive ConcurrentPhaseEnds : {Γ : SourceCtx Player L} → {names : Finset VarId} →
    SourceProgram Player L Γ names → Nat → List Nat → Prop
  | ret {Γ : SourceCtx Player L} (payoffs) (offset : Nat) :
      ConcurrentPhaseEnds (.ret (Γ := Γ) payoffs) offset []
  | sample {Γ : SourceCtx Player L} {names : Finset VarId} {name : VarId} {payload : L.Ty}
      {fresh : name ∉ Γ.map Prod.fst} {law : L.DistExpr (SourcePublicCtx L Γ) payload}
      {next : SourceProgram Player L ((name, .publicData payload) :: Γ) names}
      {offset : Nat} {rest : List Nat} :
      ConcurrentPhaseEnds next (offset + 1) rest →
      ConcurrentPhaseEnds (.sample name fresh law next) offset ((offset + 1) :: rest)
  | commits {Γ : SourceCtx Player L} {names : Finset VarId}
      {program : SourceProgram Player L Γ names} {offset : Nat} {rest : List Nat}
      (count : Nat) (prefixed : CommitPrefix program count) (positive : 0 < count)
      (maximal : leadingCommits (commitTail count program prefixed).tail = 0) :
      ConcurrentPhaseEnds (commitTail count program prefixed).tail (offset + count) rest →
      ConcurrentPhaseEnds program offset ((offset + count) :: rest)
  | reveals {Γ : SourceCtx Player L} {names : Finset VarId}
      {program : SourceProgram Player L Γ names} {offset : Nat} {rest : List Nat}
      (count : Nat) (prefixed : RevealPrefix program count) (positive : 0 < count)
      (maximal : leadingReveals (revealTail count program prefixed).tail = 0) :
      ConcurrentPhaseEnds (revealTail count program prefixed).tail (offset + count) rest →
      ConcurrentPhaseEnds program offset ((offset + count) :: rest)

/-- Every program has its phases from every rank. -/
theorem ConcurrentPhaseEnds.exists : ∀ (size : Nat) {Γ : SourceCtx Player L}
    {names : Finset VarId} (program : SourceProgram Player L Γ names),
    eventCount program = size → ∀ offset, ∃ ends, ConcurrentPhaseEnds program offset ends := by
  intro size
  induction size using Nat.strong_induction_on with
  | _ size ih =>
      intro Γ names program sized offset
      by_cases commits : leadingCommits program = 0
      · by_cases reveals : leadingReveals program = 0
        · cases program with
          | ret payoffs => exact ⟨[], .ret payoffs offset⟩
          | sample name fresh law next =>
              obtain ⟨rest, ends⟩ := ih (eventCount next) (by simp [eventCount] at sized; omega)
                next rfl (offset + 1)
              exact ⟨_, .sample ends⟩
          | reveal => simp [leadingReveals] at reveals
          | commit => simp [leadingCommits] at commits
        · have counted := eventCount_revealTail (leadingReveals program) program
            (leadingReveals_prefix program)
          obtain ⟨rest, ends⟩ := ih (eventCount (revealTail (leadingReveals program) program
            (leadingReveals_prefix program)).tail) (by omega) _ rfl
            (offset + leadingReveals program)
          exact ⟨_, .reveals (leadingReveals program) (leadingReveals_prefix program)
            (Nat.pos_of_ne_zero reveals) (leadingReveals_revealTail program) ends⟩
      · have counted := eventCount_commitTail (leadingCommits program) program
          (leadingCommits_prefix program)
        obtain ⟨rest, ends⟩ := ih (eventCount (commitTail (leadingCommits program) program
          (leadingCommits_prefix program)).tail) (by omega) _ rfl
          (offset + leadingCommits program)
        exact ⟨_, .commits (leadingCommits program) (leadingCommits_prefix program)
          (Nat.pos_of_ne_zero commits) (leadingCommits_commitTail program) ends⟩

section Phases

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- A maximal run of disclosures ends at an event that is not a publication, or
at the end of the graph. -/
theorem CompiledSuffix.revealBlockEnd {Δ : SourceCtx Player L} {names : Finset VarId}
    {tail : SourceProgram Player L Δ names} (maximal : leadingReveals tail = 0)
    {refs : ContextRefs (graphLayout setup.program) Δ} {revelations : Revelations Δ}
    {registry : Registry Δ}
    {embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) tail}
    {refsBefore : ContextRefsBefore refs embedding} {high : Nat}
    (suffix : CompiledSuffix setup.program tail refs revelations registry embedding refsBefore
      high) : RevealBlockEnd setup mode high := by
  have counted := suffix.countEq
  refine ⟨?_, ?_⟩
  · change high ≤ eventCount setup.program
    omega
  · intro event rank
    have below : event.val < eventCount setup.program := event.isLt
    have same (positive : 0 < eventCount tail) :
        event = embedding.event ⟨0, positive⟩ := by
      apply Fin.ext
      rw [suffix.rankEq]
      simpa using rank
    cases tail with
    | ret _ =>
        simp only [eventCount] at counted
        omega
    | reveal => simp [leadingReveals] at maximal
    | @sample _ _ name payload fresh law next =>
        have outputEq : (serviceGraph setup mode).outputLayout
            (embedding.event ⟨0, by simp [eventCount]⟩) = .publicData payload := by
          change outputLayout setup.program _ = _
          simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
        rw [same (by simp [eventCount]), outputEq]
        simp [EventGraph.EventField.IsPublication]
    | @commit _ _ name owner payload fresh guard next =>
        have outputEq : (serviceGraph setup mode).outputLayout
            (embedding.event ⟨0, by simp [eventCount]⟩) = .binding owner payload := by
          change outputLayout setup.program _ = _
          simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
        rw [same (by simp [eventCount]), outputEq]
        simp [EventGraph.EventField.IsPublication]

/-- **The phases of a program end at the end of the graph.** On a reveal-relaxed
graph, under a scheduler that completes play, the phases of a compiled residual
program, from a completion boundary at its rank within the horizon, stop at
completion boundaries of the whole graph within the horizon. -/
theorem ConcurrentPhaseEnds.boundary (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (complete : CompletesPlay (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy)
    (wholeProfile : BehavioralProfile setup.program) {Γ : SourceCtx Player L}
    {names : Finset VarId} {program : SourceProgram Player L Γ names} {offset : Nat}
    {ends : List Nat} (phases : ConcurrentPhaseEnds program offset ends) :
    ∀ (profile : BehavioralProfile program) (refs : ContextRefs (graphLayout setup.program) Γ)
      (revelations : Revelations Γ) (registry : Registry Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding),
      CompiledPolicySuffix setup.program wholeProfile program profile refs revelations registry
        embedding refsBefore offset →
      ∀ execution : (serviceApplication setup mode deadline leaks).Execution,
      CompletionBoundary setup leaks scheduler players offset execution →
      execution.environmentRecall.length ≤ horizon →
      ∀ final ∈ (deviationPhases scheduler players horizon ends execution).support,
        CompletionBoundary setup leaks scheduler players (eventCount setup.program) final ∧
          final.environmentRecall.length ≤ horizon := by
  induction phases with
  | ret payoffs offset =>
      intro profile refs revelations registry embedding refsBefore aligned execution boundary
        bounded final reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      have counted := aligned.graphSuffix.countEq
      simp only [eventCount, Nat.add_zero] at counted
      rw [← counted]
      exact ⟨boundary, bounded⟩
  | @sample Γ names name payload fresh distribution next offset rest _ ih =>
      intro profile refs revelations registry embedding refsBefore aligned execution boundary
        bounded final reached
      let index : Fin (eventCount (.sample name fresh distribution next)) :=
        ⟨0, by simp [eventCount]⟩
      let event : (serviceGraph setup mode).EventId := embedding.event index
      have eventRank : event.val = offset := by
        simpa only [event, index, Fin.val_zero, Nat.add_zero] using
          aligned.graphSuffix.rankEq index
      have outputEq : (serviceGraph setup mode).outputLayout event = .publicData payload := by
        change outputLayout setup.program event = _
        simpa [event, index, outputLayout, eventCount] using embedding.layout_eq index
      have sealed : BlockSealed setup mode offset (offset + 1) := by
        have alone := sealed_of_alone (event := event) (sample_alone relaxed outputEq)
        rwa [eventRank] at alone
      have counted := aligned.graphSuffix.countEq
      simp only [eventCount] at counted
      simp only [deviationPhases] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have done := blockRun_completes complete (offset + 1) execution boundary bounded middle
        moved
      obtain ⟨middleBounded, middleBoundary⟩ := blockRun_boundary (Nat.le_succ _) sealed
        (by change offset + 1 ≤ eventCount setup.program; omega) execution boundary bounded
        middle moved done
      exact ih _ _ _ _ _ _ (aligned.sampleTail setup.program wholeProfile (_openNames := names)
        fresh distribution next profile refs revelations registry embedding refsBefore offset)
        middle middleBoundary middleBounded final later
  | @commits Γ names program offset rest count prefixed _ maximal _ ih =>
      intro profile refs revelations registry embedding refsBefore aligned execution boundary
        bounded final reached
      have tailAligned := CompiledPolicySuffix.commitTailMany wholeProfile count program prefixed
        profile refs revelations registry embedding refsBefore offset aligned
      have wall : BlockEnd setup mode (offset + count) :=
        CompiledSuffix.blockEnd maximal tailAligned.graphSuffix
      have bindings : ∀ event : (serviceGraph setup mode).EventId, offset ≤ event.val →
          event.val < offset + count → ∃ owner payload outputEq codeEq,
            EventGraphRuntime.nodeView (serviceGraph setup mode) event =
              .bind owner payload outputEq codeEq := by
        intro event lower upper
        have within := prefixed.le_eventCount
        obtain ⟨index, below, same⟩ : ∃ index : Fin (eventCount program), index.val < count ∧
            embedding.event index = event := by
          refine ⟨⟨event.val - offset, by omega⟩, by simp only; omega, ?_⟩
          apply Fin.ext
          rw [aligned.graphSuffix.rankEq]
          simp only
          omega
        subst same
        exact CompiledSuffix.commitPrefix_bind count program prefixed refs _ _ embedding
          refsBefore offset aligned.graphSuffix index below
      simp only [deviationPhases] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have done := blockRun_completes complete (offset + count) execution boundary bounded middle
        moved
      obtain ⟨middleBounded, middleBoundary⟩ := blockRun_boundary (Nat.le_add_right _ _)
        (BlockEnd.sealed_relaxed relaxed wall (plain_of_bindings bindings)) wall.1 execution
        boundary bounded middle moved done
      exact ih _ _ _ _ _ _ tailAligned middle middleBoundary middleBounded final later
  | @reveals Γ names program offset rest count prefixed _ maximal _ ih =>
      intro profile refs revelations registry embedding refsBefore aligned execution boundary
        bounded final reached
      have tailAligned := CompiledPolicySuffix.revealTailMany wholeProfile count program prefixed
        profile refs revelations registry embedding refsBefore offset aligned
      have wall : RevealBlockEnd setup mode (offset + count) :=
        CompiledSuffix.revealBlockEnd maximal tailAligned.graphSuffix
      simp only [deviationPhases] at reached
      obtain ⟨middle, moved, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have done := blockRun_completes complete (offset + count) execution boundary bounded middle
        moved
      obtain ⟨middleBounded, middleBoundary⟩ := blockRun_boundary (Nat.le_add_right _ _)
        (RevealBlockEnd.sealed relaxed wall (prefixed.publications aligned.graphSuffix))
        wall.1 execution boundary bounded middle moved done
      exact ih _ _ _ _ _ _ tailAligned middle middleBoundary middleBounded final later

end Phases

/-- Every player of the residual profile opens effectively. -/
def openingResidual : ResidualProperty Player L := fun program profile registry revelations =>
  ∀ player, (profile player).OpensEffectively program registry revelations

/-- The residual profile after leading commitments keeps opening effectively. -/
theorem opensEffectively_commitTail {who : Player} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : CommitPrefix program count)
      (profile : BehavioralProfile program) (registry : Registry Γ)
      (revelations : Revelations Γ),
      (profile who).OpensEffectively program registry revelations →
      ((commitTailProfile count program prefixed profile) who).OpensEffectively
        (commitTail count program prefixed).tail
        (commitTailRegistry count program prefixed registry)
        (commitTailRevelations count program prefixed revelations) := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed profile registry revelations opens; exact opens
  | succ count ih =>
      intro Γ names program prefixed profile registry revelations opens
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ next =>
          exact ih next prefixed (afterCommit profile) _ _ opens

/-- **The honest law of the opening clients over every phase.** On a
reveal-relaxed graph, under the asynchronous contract with timely delays, when
every player follows the first-turn client of a source profile that opens
effectively, the phases of any residual program decode to the law of the source
run of the residual profile. -/
theorem openingHonestLaw [Fintype Player]
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program)
    {Γ : SourceCtx Player L} {names : Finset VarId} {program : SourceProgram Player L Γ names}
    {offset : Nat} {ends : List Nat} (phases : ConcurrentPhaseEnds program offset ends) :
    ∀ (profile : BehavioralProfile program) (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding),
      HonestLaw setup leaks horizon scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) wholeProfile)
        wholeProfile openingResidual program profile refs embedding refsBefore offset ends := by
  let players := serviceTurnPolicy setup mode deadline leaks bound turns
    (firstTurnTiming setup turns mode) wholeProfile
  induction phases with
  | ret payoffs offset =>
      intro profile refs embedding refsBefore Seed prior source execution _aligned checkpoint
        _boundary _bounded _opens
      apply bind_congr_on_support _
      intro seed _
      simp only [deviationPhases, eventCount, Function.iterate_zero, id_eq, PMF.pure_map]
      rw [(checkpoint seed).decode (.ret payoffs) embedding.ref]
  | sample _ ih =>
      exact HonestLaw.sample_step setup leaks relaxed contract turns wholeProfile openingResidual
        (fun _ _ _ opens => opens) ih
  | commits count prefixed positive maximal _ ih =>
      exact HonestLaw.commits_step setup leaks relaxed contract timely turns wholeProfile
        openingResidual
        (fun program count prefixed profile registry revelations opens player =>
          opensEffectively_commitTail (who := player) count program prefixed profile registry
            revelations (opens player))
        count prefixed positive maximal ih
  | @reveals Γ names program offset rest count prefixed positive maximal _ ih =>
      intro profile refs embedding refsBefore Seed prior source execution aligned checkpoint
        boundary bounded opens
      let tailRefs := revealTailRefs setup count program prefixed refs embedding
      let tailEmbedding := revealTailEmbedding setup count program prefixed embedding
      have tailBefore : ContextRefsBefore tailRefs tailEmbedding :=
        revealTailRefsBefore count program prefixed refs embedding refsBefore
      have tailAligned (seed : Seed) := CompiledPolicySuffix.revealTailMany wholeProfile count
        program prefixed profile refs (source seed).revelations (source seed).registry embedding
        refsBefore offset (aligned seed)
      have wall : RevealBlockEnd setup mode (offset + count) :=
        CompiledSuffix.revealBlockEnd maximal
          (tailAligned prior.support_nonempty.choose).graphSuffix
      have publications := prefixed.publications (mode := mode)
        (aligned prior.support_nonempty.choose).graphSuffix
      have nextFacts (point : PhasePoint setup leaks horizon scheduler players (offset + count)
          prior execution) :
          CompletionBoundary setup leaks scheduler players (offset + count) point.val.2 ∧
            point.val.2.environmentRecall.length ≤ horizon := by
        obtain ⟨supported, reached⟩ := phaseJoint_mem setup leaks horizon scheduler players
          point.property
        have done := blockRun_completes contract.completes (offset + count)
          (execution point.val.1) (boundary _ supported) (bounded _ supported) _ reached
        obtain ⟨nextBounded, nextBoundary⟩ := blockRun_boundary (Nat.le_add_right _ _)
          (RevealBlockEnd.sealed relaxed wall publications) wall.1 (execution point.val.1)
          (boundary _ supported) (bounded _ supported) _ reached done
        exact ⟨nextBoundary, nextBounded⟩
      have through (seed : Seed) (player : Player) :=
        BehavioralPolicy.OpensEffectively.through count program prefixed (source seed).registry
          (source seed).revelations (profile player) (opens seed player)
      have block := honest_revealBlock_law relaxed wall contract timely turns wholeProfile
        program profile count prefixed positive refs embedding refsBefore rfl prior source
        execution aligned (fun seed player => (through seed player).1) checkpoint boundary
        bounded
      refine HonestLaw.phase setup leaks horizon scheduler players wholeProfile openingResidual
        program profile refs embedding (revealTail count program prefixed).tail
        (revealTailProfile count program prefixed profile) tailRefs tailEmbedding tailBefore
        (offset + count) rest (ih _ tailRefs tailEmbedding tailBefore) prior source execution
        (revealTail count program prefixed).lift
        ((revealTail_lift_injective count program prefixed).comp
          (ProtocolState.entry_injective _))
        (fun seed => revealTailRegistry count program prefixed (source seed).registry)
        (fun seed => revealTailRevelations count program prefixed (source seed).revelations)
        (fun seed final => decodeSourcePrefix? program refs (source seed).registry
          (source seed).revelations embedding.ref count final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode))))
        (fun seed final => decodeSourcePrefix?_revealTail_entry count program prefixed refs _ _
          embedding _ _)
        (fun config => PMF.pure (openChain count program prefixed config)) ?_
        (fun point => (nextFacts point).1) (fun point => (nextFacts point).2) tailAligned
        (fun seed player => (through seed player).2 profile rfl) ?_ ?_
      · simp only [phaseJoint, PMF.map_bind, PMF.map_comp, Function.comp_def]
        rw [block]
        simp only [PMF.pure_map]
        exact (PMF.bind_pure_comp _ _).symm
      · intro seed final
        have through := decodeSourcePrefix?_revealTail count program prefixed refs
          (source seed).registry (source seed).revelations embedding
          (eventCount (revealTail count program prefixed).tail) final.application.config.store
          (decodeHistory setup.program (final.application.config.history.map
            (setup.eventGraph.fromModeCompletion mode)))
        rw [eventCount_revealTail] at through
        exact through
      · intro seed supported
        have chained := iterate_openChain count program profile prefixed
          (eventCount (revealTail count program prefixed).tail) (source seed)
          (fun player => (through seed player).1)
        rw [eventCount_revealTail] at chained
        rw [PMF.pure_bind]
        exact chained

/-- **The opening clients have the source outcome law.** On a reveal-relaxed
graph, under a scheduler satisfying the asynchronous contract with timely
delays, when every player follows the first-turn client of a source profile
that opens effectively, the typed outcome has exactly the source law of the
profile. -/
theorem openingFirstTurn_readout_law [Finite Player]
    (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (relaxed : (serviceGraph setup mode).RevealRelaxedOrdered)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound) (turns : Nat)
    (profile : BehavioralProfile setup.program)
    (opens : ∀ player, (profile player).OpensEffectively setup.program []
      (Revelations.initial setup.context)) :
    ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
      scheduler (serviceTurnPolicy setup mode deadline leaks bound turns
        (firstTurnTiming setup turns mode) profile) horizon).map
        (fun execution => serviceSourceReadout setup mode deadline leaks
          ((serviceApplication setup mode deadline leaks).finished execution)) =
      (setup.run profile).map some := by
  have := Fintype.ofFinite Player
  obtain ⟨ends, phases⟩ := ConcurrentPhaseEnds.exists (eventCount setup.program) setup.program
    rfl 0
  exact firstTurn_readout_law_of_honest setup leaks turns profile openingResidual opens
    (openingHonestLaw setup leaks relaxed contract timely turns profile phases profile _ _
      (initialRefsBefore setup.program))
    (fun execution boundary bounded final reached => (ConcurrentPhaseEnds.boundary relaxed
      contract.completes _ profile phases profile _ _ _ (outputEmbedding setup.program)
      (initialRefsBefore setup.program) (CompiledPolicySuffix.whole setup.program profile)
      execution boundary bounded final reached).1)

end Vegas
