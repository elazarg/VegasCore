/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefix
import Vegas.Game.RevealServiceRosterCheckpoint

/-! # Public checkpoints at existing source protocol positions

This proof predicate follows the static sum nesting of the existing source
protocol state. It retains the actual native execution and imposes the public
checkpoint equations, without restricting pending copies or private leak lists.
It is not a source evaluator or another strategic game.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

def PublicPrefixCheckpoint (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (initial : State L setup.context) :
    {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) →
    ContextRefs (graph setup).layout Γ → Revelations Γ →
    (∀ event, EventGraph.FieldRef (graph setup).layout (outputLayout program event)) →
    Nat → Nat → ProtocolState program → (application setup leaks).Execution → Prop
  | _, _, program, refs, revelations, _, offset, 0, state, execution =>
      ∃ source, state = ProtocolState.entry program source ∧
        @source.revelations = @revelations ∧
        PublicCheckpoint setup leaks initial source refs offset execution
  | _, _, .ret _, _, _, _, _, _ + 1, _, _ => False
  | _, _, .sample _ _ _ _, _, _, _, _, _ + 1, _, _ => False
  | _, _, .commit _ _ _ _ _, _, _, _, _, _ + 1, _, _ => False
  | _, _, .reveal (payload := payload) _ _ _ _ selected _ next,
      refs, revelations, outputs, offset, count + 1, state, execution =>
      let headRef : EventGraph.FieldRef (graph setup).layout (.publication payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      match state with
      | .inl _ => False
      | .inr rest => PublicPrefixCheckpoint setup leaks initial next (refs.cons headRef)
          (revelations.reveal selected) (fun tail => outputs tail.succ) (offset + 1)
          count rest execution

/-- Every operationally related prefix decodes to its complete existing source
state. In particular the partial decoder never fails on these prefixes. -/
theorem PublicPrefixCheckpoint.decode
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (graph setup).layout Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout
        (outputLayout program event))
      (offset count : Nat) (state : ProtocolState program)
      (execution : (application setup leaks).Execution),
      PublicPrefixCheckpoint setup leaks initial program refs revelations outputs
        offset count state execution →
      decodePrefix? program refs revelations outputs count execution.application.config.store
        (decodeHistory setup.program (execution.application.config.history.map
          (setup.eventGraph.fromModeCompletion .sequential))) = some state := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro refs revelations outputs offset count state execution related
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [checkpoint.history, ← revelationsEq]
          exact decodePrefix?_zero_of_agrees _ refs outputs state checkpoint.emptyRegistry _
            checkpoint.agrees
      | succ count => exact related.elim
  | sample name fresh law next ih =>
      intro refs revelations outputs offset count state execution related
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [checkpoint.history, ← revelationsEq]
          exact decodePrefix?_zero_of_agrees _ refs outputs source checkpoint.emptyRegistry _
            checkpoint.agrees
      | succ count => exact related.elim
  | commit name owner fresh guard next ih =>
      intro refs revelations outputs offset count state execution related
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [checkpoint.history, ← revelationsEq]
          exact decodePrefix?_zero_of_agrees _ refs outputs source checkpoint.emptyRegistry _
            checkpoint.agrees
      | succ count => exact related.elim
  | reveal published owner name fresh selected unresolved next ih =>
      intro refs revelations outputs offset count state execution related
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [checkpoint.history, ← revelationsEq]
          exact decodePrefix?_zero_of_agrees _ refs outputs source checkpoint.emptyRegistry _
            checkpoint.agrees
      | succ count =>
          cases state with
          | inl source => exact related.elim
          | inr rest =>
              rw [decodePrefix?_reveal]
              rw [ih _ _ _ (offset + 1) count rest execution related]
              rfl

end Vegas.SourceProgram.RevealService
