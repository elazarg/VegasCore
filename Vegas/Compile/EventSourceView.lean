/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphPolicy
import Vegas.Source.CommitRecoveryStep

/-! # Source protocol views at compiled event addresses

The decoder follows the existing policy compiler's context references and
source sum constructors. It does not decode foreign hidden source cells or
construct a source execution history.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Decode the current source protocol view through its actual syntactic
address, using only the source-visible store and effective own actions. -/
def decodeEventView? {Field : Type} {layout : Field → EventField Player L} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ContextRefs layout Γ →
    (∀ event, FieldRef layout (outputLayout program event)) →
    (who : Player) → Fin (eventCount program) → Store layout → List (OwnAction Player L) →
      Option (ProtocolView who program)
  | _, _, .ret _, _, _, _, event, _, _ => nomatch event
  | _, _, .sample name fresh law next, refs, outputs, who, event, store, past =>
      let first : FieldRef layout (.publicData _) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      Fin.cases
        ((decodeObservation? who refs store).map fun observation => .inl (observation, past))
        (fun tail => (decodeEventView? next (refs.cons first)
          (fun later => outputs (Fin.succ later)) who tail store past).map Sum.inr) event
  | _, _, .commit (payload := payload) name owner fresh guard next,
      refs, outputs, who, event, store, past =>
      let first : FieldRef layout (.binding owner payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      Fin.cases
        ((decodeObservation? who refs store).map fun observation => .inl (observation, past))
        (fun tail => (decodeEventView? next (refs.cons first)
          (fun later => outputs (Fin.succ later)) who tail store past).map Sum.inr) event
  | _, _, .reveal (payload := payload) published owner name fresh source unresolved next,
      refs, outputs, who, event, store, past =>
      let first : FieldRef layout (.publication payload) := by
        simpa [outputLayout, eventCount] using outputs ⟨0, by simp [eventCount]⟩
      Fin.cases
        ((decodeObservation? who refs store).map fun observation => .inl (observation, past))
        (fun tail => (decodeEventView? next (refs.cons first)
          (fun later => outputs (Fin.succ later)) who tail store past).map Sum.inr) event

/-- A legal source action at a decoded view is exactly an action of the named
compiled event. The source action's payload and address are retained. -/
theorem decodeEventView?_available {Field : Type} {layout : Field → EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, FieldRef layout (outputLayout program event)) (who : Player)
      (event : Fin (eventCount program)) (store : Store layout) (past : List (OwnAction Player L))
      (view : ProtocolView who program),
      decodeEventView? program refs outputs who event store past = some view →
      ∀ action ∈ ProtocolView.available who program (CommitmentInterface.forfeiture program) view,
        ∃ choice, decodeEventAction program event choice = some action := by
  intro Γ O program
  induction program with
  | ret => intro refs outputs who event; exact Fin.elim0 event
  | sample name fresh law next ih =>
      intro refs outputs who event store past view decoded action available
      refine Fin.cases ?_ ?_ event decoded available
      · intro decoded available
        obtain ⟨observation, _present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact available.elim
      · intro tail decoded available
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact ih _ _ who tail store past later present action available
  | commit name owner fresh guard next ih =>
      intro refs outputs who event store past view decoded action available
      refine Fin.cases ?_ ?_ event decoded available
      · intro decoded available
        obtain ⟨observation, _present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        obtain ⟨choice, _admitted, rfl⟩ := available
        exact ⟨choice, rfl⟩
      · intro tail decoded available
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact ih _ _ who tail store past later present action available
  | reveal published owner name fresh source unresolved next ih =>
      intro refs outputs who event store past view decoded action available
      refine Fin.cases ?_ ?_ event decoded available
      · intro decoded available
        obtain ⟨observation, _present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        obtain ⟨choice, rfl⟩ := available
        exact ⟨choice, rfl⟩
      · intro tail decoded available
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact ih _ _ who tail store past later present action available

end Vegas
