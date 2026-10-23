/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompiledRevealReadCone
import Vegas.Game.CompiledRevealLayout
import Vegas.Game.RecoverySourceCheckpoint

/-! # Actual saved publication checkpoints determine every owner read cone -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem reveal_prefix_reads :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (_prefixed : RevealPrefix program count)
    (target : Fin (eventCount setup.program)) (refs : ContextRefs (graphLayout setup.program) Γ)
    (revelations : Revelations Γ) (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program)
    (before : ContextRefsBefore refs embedding) (offset : Nat),
    CompiledSuffix setup.program program refs revelations registry embedding before offset →
    RegistryPublicReadsBefore target refs registry →
    RevealedCommitmentReadCone (toEventGraph setup.program).actor? target refs revelations →
    ∀ (index : Fin (eventCount program)), index.val < count → ∀ owner,
      (toEventGraph setup.program).actor? (embedding.event index) = some owner →
      ∀ field, field ∈ ((toEventGraph setup.program).nodes (embedding.event index)).readFields →
        RevealReadCone (toEventGraph setup.program).actor? target owner field := by
  intro count
  induction count with
  | zero =>
      intro Γ names program prefixed target refs revelations registry embedding before offset
        compiled publicReads commitmentReads index inside
      omega
  | succ count ih =>
      intro Γ names program prefixed target refs revelations registry embedding before offset
        compiled publicReads commitmentReads index inside who acting field member
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | @reveal Γ names published owner name payload fresh selected unresolved next =>
          let zero : Fin (eventCount
              (.reveal published owner name fresh selected unresolved next)) :=
            ⟨0, by simp only [eventCount]; omega⟩
          have outputEq : (toEventGraph setup.program).outputLayout (embedding.event zero) =
              .publication payload := (embedding.layout_eq zero).trans rfl
          have code : cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
              ((toEventGraph setup.program).nodes (embedding.event zero)) =
              .resolve owner payload (refs.get selected)
                (compileChecks (published := published) refs registry revelations selected) := by
            simpa only [zero, compileRankedNodes, outputLayout, Fin.mk_zero, Fin.cases_zero]
              using compiled.nodeEq zero
          have actor : (toEventGraph setup.program).actor? (embedding.event zero) = some owner :=
            (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor code)
          by_cases first : index.val = 0
          · have equal : index = zero := Fin.ext first
            rw [equal] at acting member
            have same : owner = who := Option.some.inj (actor.symm.trans acting)
            subst who
            exact compiled.resolve_read_cone setup fresh selected unresolved next refs revelations
              registry embedding before offset target publicReads commitmentReads field member
          · let tailIndex : Fin (eventCount next) := ⟨index.val - 1, by
              have bounded := index.isLt
              simp only [eventCount] at bounded
              omega⟩
            have equal : Fin.succ tailIndex = index := Fin.ext (by
              simp only [tailIndex, Fin.val_succ]
              omega)
            let publicationRef : FieldRef (graphLayout setup.program) (.publication payload) :=
              ⟨.inr (embedding.event zero), outputEq⟩
            have nextCommitment : RevealedCommitmentReadCone (toEventGraph setup.program).actor?
                target (refs.cons (name := published) publicationRef)
                  (revelations.reveal (published := published) selected) :=
              RevealedCommitmentReadCone.reveal (published := published)
                (toEventGraph setup.program).actor? target refs revelations selected
                  publicationRef (Or.inr actor) commitmentReads
            have nextPublic := RegistryPublicReadsBefore.weaken
              (name := published) (cell := .publication payload) target refs publicationRef
                registry publicReads
            have nextCompiled := compiled.revealTail setup.program fresh selected unresolved next
              refs revelations registry embedding before offset
            have nextActing : (toEventGraph setup.program).actor?
                ((embedding.tail next (by simp only [eventCount]) (fun _ => rfl)).event
                  tailIndex) = some who := by
              simpa only [OutputEmbedding.tail, Fin.cast_eq_self, equal] using acting
            have nextMember : field ∈ ((toEventGraph setup.program).nodes
                ((embedding.tail next (by simp only [eventCount]) (fun _ => rfl)).event
                  tailIndex)).readFields := by
              simp only [OutputEmbedding.tail, Fin.cast_eq_self]
              rw [equal]
              exact member
            exact ih next prefixed target _ _ _ _ _ (offset + 1) nextCompiled nextPublic
              nextCommitment tailIndex (by dsimp only [tailIndex]; omega) who nextActing field
                nextMember

/-- Every guard operand in the actual installed publication block is fixed at
its saved source checkpoint or belongs to the same owner's publication chain.
The compiler prefix and its read cones are derived from that checkpoint. -/
theorem RecoverySourceCheckpoint.publication_read_cone
    {mode : EventGraph.ExecutionMode}
    {state : PhaseRuntimeState ((toEventGraph setup.program).withMode mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (phase : RuntimePhase ((toEventGraph setup.program).withMode mode))
    (installed : phase ∈ state.phases.head?) (kind : phase.kind = .reveal)
    (event : ((toEventGraph setup.program).withMode mode).EventId)
    (inside : event ∈ phase.events) (owner : Player)
    (acting : ((toEventGraph setup.program).withMode mode).actor? event = some owner)
    (field : ((toEventGraph setup.program).withMode mode).Field)
    (member : field ∈ (((toEventGraph setup.program).withMode mode).nodes event).readFields) :
    match field with
    | .inl _ => True
    | .inr prior => prior.val < phase.low ∨
        ((toEventGraph setup.program).withMode mode).actor? prior = some owner := by
  have low : phase.low = state.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, Option.mem_def.mp installed, Option.map_some,
      Option.getD_some]
  let count := phase.high - phase.low
  have high : phase.high = state.attempt.phase + count := by
    have positive := phase.nonempty
    dsimp only [count]
    omega
  let program := checkpoint.residual.tail
  let prefixed := checkpoint.compiled.revealPrefix_of_phase setup.program mode program
    checkpoint.refs checkpoint.source.revelations checkpoint.registry checkpoint.embedding
      checkpoint.before state.attempt.phase phase kind low count high
  have intervals := (phase.mem_events event).mp inside
  have total := checkpoint.compiled.countEq
  let index : Fin (eventCount program) := ⟨event.val - state.attempt.phase, by
    change state.attempt.phase + eventCount program = eventCount setup.program at total
    have bounded := event.isLt
    change event.val < eventCount setup.program at bounded
    omega⟩
  have exactEvent : checkpoint.embedding.event index = event := by
    apply Fin.ext
    rw [checkpoint.compiled.rankEq]
    dsimp only [index]
    omega
  have countPositive : 0 < count := by
    have positive := phase.nonempty
    dsimp only [count]
    omega
  let first : Fin (eventCount program) := ⟨0, by
    have bounded := phase.bounded
    change state.attempt.phase + eventCount program = eventCount setup.program at total
    change phase.high ≤ eventCount setup.program at bounded
    omega⟩
  have targetRank : (checkpoint.embedding.event first).val = phase.low := by
    rw [checkpoint.compiled.rankEq, ← low]
    rfl
  have publicReads : RegistryPublicReadsBefore (checkpoint.embedding.event first)
      checkpoint.refs checkpoint.registry := by
    intro obligation _member
    exact GuardPublicReadsBefore.of_refs _ checkpoint.refs
      (fun source => checkpoint.before source first) obligation.guard
  have commitmentReads : RevealedCommitmentReadCone (toEventGraph setup.program).actor?
      (checkpoint.embedding.event first) checkpoint.refs checkpoint.source.revelations :=
    RevealedCommitmentReadCone.of_refs _ _ checkpoint.refs
      (fun source => checkpoint.before source first) checkpoint.source.revelations
  have read := reveal_prefix_reads setup count program prefixed
    (checkpoint.embedding.event first) checkpoint.refs checkpoint.source.revelations
      checkpoint.registry checkpoint.embedding checkpoint.before state.attempt.phase
        checkpoint.compiled publicReads commitmentReads index (by dsimp only [index, count]; omega)
          owner (by
            rw [exactEvent]
            exact acting) field (by
              rw [exactEvent]
              exact member)
  cases field with
  | inl input => trivial
  | inr prior =>
      change prior.val < (checkpoint.embedding.event first).val ∨
        (toEventGraph setup.program).actor? prior = some owner at read
      simpa only [targetRank, EventGraph.actor?, EventGraph.withMode_nodes] using read

end Vegas
