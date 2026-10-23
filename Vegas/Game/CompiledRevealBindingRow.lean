/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledRevealBindingOrigins
import Vegas.Game.CompiledRevealLayout

/-! # Original binding references at every compiled disclosure row -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Each row of the actual compiled disclosure prefix resolves one original
commitment reference. Guards are retained literally, without a success premise. -/
theorem CompiledSuffix.reveal_binding_origin_at :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (_prefixed : RevealPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ) (revelations : Revelations Γ)
      (registry : Registry Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (before : ContextRefsBefore refs embedding) (offset : Nat)
      (_compiled : CompiledSuffix setup.program program refs revelations registry embedding
        before offset)
      (index : Fin (eventCount program)), index.val < count →
      ∃ (owner : Player) (payload : L.Ty) (name : VarId)
        (selected : HasVar Γ name (.commitment owner payload))
        (checks : List (GuardCheck (graphLayout setup.program) payload))
        (output : outputLayout setup.program (embedding.event index) = .publication payload),
        cast (congrArg (EventCode (graphLayout setup.program)) output)
          ((toEventGraph setup.program).nodes (embedding.event index)) =
            .resolve owner payload (refs.get selected) checks := by
  intro count
  induction count with
  | zero =>
      intro Γ O program prefixed refs revelations registry embedding before offset compiled index
        impossible
      omega
  | succ count ih =>
      intro Γ O program prefixed refs revelations registry embedding before offset compiled index
        inside
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | @reveal Γ O published owner name payload fresh selected unresolved next =>
          let program := SourceProgram.reveal published owner name fresh selected unresolved next
          let zero : Fin (eventCount program) := ⟨0, by simp only [program, eventCount]; omega⟩
          have output : outputLayout setup.program (embedding.event zero) =
              .publication payload := by
            simpa only [zero, program, outputLayout, Fin.mk_zero, Fin.cases_zero] using
              embedding.layout_eq zero
          let tailEmbedding := embedding.tail next (by simp only [eventCount]) (fun _ => rfl)
          let tailRefs := refs.cons (name := published) (cell := .publication payload)
            (⟨.inr (embedding.event zero), output⟩ :
              FieldRef (graphLayout setup.program) (.publication payload))
          have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
            intro readName cell source later
            cases source with
            | here =>
                change (embedding.event zero).val < (embedding.event (Fin.succ later)).val
                apply embedding.strictMono
                change 0 < later.val + 1
                omega
            | there source => exact before source (Fin.succ later)
          have tailCompiled : CompiledSuffix setup.program next tailRefs
              (revelations.reveal (published := published) selected) registry.weaken
              tailEmbedding tailBefore (offset + 1) :=
            compiled.revealTail setup.program fresh selected unresolved next refs revelations
              registry embedding before offset
          cases index using Fin.cases with
          | zero =>
              refine ⟨owner, payload, name, selected,
                compileChecks (published := published) refs registry revelations selected,
                output, ?_⟩
              simpa only [program, zero, compileRankedNodes, Fin.mk_zero, Fin.cases_zero] using
                compiled.nodeEq zero
          | succ index =>
              obtain ⟨who, sort, sourceName, read, checks, publication, code⟩ := ih next prefixed
                tailRefs _ registry.weaken tailEmbedding tailBefore (offset + 1) tailCompiled index
                  (by change index.val + 1 < count + 1 at inside; omega)
              have one : RevealPrefix program 1 := by simp only [program, RevealPrefix]
              obtain ⟨original, same⟩ := revealTailRefs_commitment_origin setup 1 program one
                refs embedding read
              have reference : tailRefs.get read = refs.get original := same
              refine ⟨who, sort, sourceName, original, checks, publication, ?_⟩
              rw [reference] at code
              exact code

/-- An actual installed publication event exposes its original saved binding
and its proper current typed value. This is compiler metadata and immutable
store readback; no guard-success or whole source-kernel premise is required. -/
theorem RecoverySourceCheckpoint.publication_binding_row
    (mode : ExecutionMode) {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (phase : RuntimePhase (serviceGraph setup mode)) (installed : phase ∈ state.phases.head?)
    (kind : phase.kind = .reveal) (stored : state.StoredCheckpoint)
    (event : (serviceGraph setup mode).EventId) (inside : event ∈ phase.events)
    (owner : Player) (acting : (serviceGraph setup mode).actor? event = some owner)
    (proper : checkpoint.source.BindingsHoldValues owner) :
    ∃ (payload : L.Ty) (name : VarId)
      (selected : HasVar checkpoint.residual.context name (.commitment owner payload))
      (checks : List (GuardCheck (graphLayout setup.program) payload))
      (output : (serviceGraph setup mode).outputLayout event = .publication payload),
      cast (congrArg (EventCode (graphLayout setup.program)) output)
        ((serviceGraph setup mode).nodes event) =
          .resolve owner payload (checkpoint.refs.get selected) checks ∧
      ∃ value, (checkpoint.refs.get selected).get? state.current.native.config.store =
        some (.success value) := by
  have low : phase.low = state.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, Option.mem_def.mp installed, Option.map_some,
      Option.getD_some]
  let count := phase.high - phase.low
  have high : phase.high = state.attempt.phase + count := by
    have nonempty := phase.nonempty
    dsimp only [count]
    omega
  have prefixed := checkpoint.compiled.revealPrefix_of_phase setup.program mode
    checkpoint.residual.tail checkpoint.refs checkpoint.source.revelations checkpoint.registry
      checkpoint.embedding checkpoint.before state.attempt.phase phase kind low count high
  have interval := (phase.mem_events event).mp inside
  have total := checkpoint.compiled.countEq
  let index : Fin (eventCount checkpoint.residual.tail) :=
    ⟨event.val - phase.low, by
      have bounded := phase.bounded
      change phase.high ≤ eventCount setup.program at bounded
      omega⟩
  have indexInside : index.val < count := by dsimp only [index, count]; omega
  have eventEq : checkpoint.embedding.event index = event := by
    apply Fin.ext
    rw [checkpoint.compiled.rankEq]
    dsimp only [index]
    omega
  obtain ⟨actor, payload, name, selected, checks, output, code⟩ :=
    checkpoint.compiled.reveal_binding_origin_at setup count checkpoint.residual.tail prefixed
      checkpoint.refs checkpoint.source.revelations checkpoint.registry checkpoint.embedding
      checkpoint.before state.attempt.phase index indexInside
  have atEvent : ∃ output : outputLayout setup.program event = .publication payload,
      cast (congrArg (EventCode (graphLayout setup.program)) output)
        ((toEventGraph setup.program).nodes event) =
          .resolve actor payload (checkpoint.refs.get selected) checks := by
    rw [← eventEq]
    exact ⟨output, code⟩
  obtain ⟨output, code⟩ := atEvent
  have rowActor : (serviceGraph setup mode).actor? event = some actor :=
    (EventCode.actor_cast output ((serviceGraph setup mode).nodes event)).symm.trans
      (congrArg EventCode.actor code)
  have ownerEq : actor = owner := Option.some.inj (rowActor.symm.trans acting)
  subst actor
  obtain ⟨value, locked⟩ := RecoverySourceCheckpoint.publication_binding_value setup checkpoint
    stored 0 (by simp only [RevealPrefix]) selected proper
  exact ⟨payload, name, selected, checks, output, code, value, locked⟩

end Vegas
