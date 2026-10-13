/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketProjectedDecision
import Vegas.Game.OnePacketSureFailure
import Vegas.Game.OnePacketDisclosureResolves
import Vegas.Source.IntendedForPlayer

/-! # Unintended commitments leave their owner owing

**At the source.** At a point intended for a player, completing an event of
the player with a decoded action outside the intended actions of the player's
view leaves the player owing a failure
(`Vegas.SourceProgram.ProtocolState.owesFailure_of_decode_not_intendedAvailable`):
a failed binding is a failed binding, a binding of a value outside the intended
values is a binding of a value its guard is predicted to reject, and a withheld
disclosure fails the reveal.
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **An unintended completion owes.** At a point intended for `actor`, decoded
after `count` events, stepping with the decoded action of the event of index
`count`, owned by `actor`, when that action is not an intended action of
`actor`'s view, leaves `actor` owing a failure. -/
theorem owesFailure_of_decode_not_intendedAvailable {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (state : ProtocolState program) (bound : count < eventCount program) (actor : Player)
      (action : EventGraph.EventField.Action (outputLayout program ⟨count, bound⟩))
      (target : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history =
          some state →
      IntendedFor actor program state →
      eventOwner? program ⟨count, bound⟩ = some actor →
      target ∈ (step program state
        (fun _ => decodeEventAction program ⟨count, bound⟩ action)).support →
      (∀ act, decodeEventAction program ⟨count, bound⟩ action = some act →
        act ∉ ProtocolView.intendedAvailable actor program (observe actor program state)) →
      OwesFailure actor program target := by
  induction program with
  | ret _ =>
      intro count _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached unintended
      cases count with
      | zero => cases owned
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended owned supported unintended
  | @commit commitCtx commitNames name owner payload fresh guard next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached unintended
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          change PublicationResult (L.Val payload) at action
          change ∀ act, some (OwnAction.commit owner name payload action) = some act → _
            at unintended
          change OwesFailure owner (.commit name owner fresh guard next) (Sum.inr (entry next
            (commitSuccessor name guard ⟨cells, registry, revelations, history⟩
              (OwnAction.binding owner name payload
                (some (OwnAction.commit owner name payload action))))))
          rw [OwnAction.binding_commit]
          cases action with
          | failure =>
              exact Or.inr (failedBinding_entry next _ (intended.failedBinding_commit fresh guard))
          | success value =>
              have outside := unintended _ rfl
              have rejected : guard.predicts (sourceObserve owner cells) value = false := by
                cases predicted : guard.predicts (sourceObserve owner cells) value with
                | false => rfl
                | true =>
                    exact (outside ⟨value, Or.inl
                      ((mem_predictedValues_self guard _ value).mpr predicted), rfl⟩).elim
              exact Or.inl (indebted_entry next _ (intended.indebted_commit fresh guard value
                rejected))
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended owned supported unintended
  | reveal published owner name fresh source unresolved next ih =>
      intro count refs registry revelations outputs store history state bound actor action target
        decoded intended owned reached unintended
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          change Bool at action
          change ∀ act, some (OwnAction.reveal owner name action) = some act → _ at unintended
          cases action with
          | true => exact (unintended _ rfl rfl).elim
          | false =>
              refine Or.inl (Or.inl ⟨rfl, ?_⟩)
              rw [base_entry]
              exact disclosureResult_false published source _
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases ih count _ _ _ _ store history rest (Nat.lt_of_succ_lt_succ bound) actor action
            after read intended owned supported unintended with indebted | failed
          · exact Or.inl (Or.inr indebted)
          · exact Or.inr (Or.inr failed)

end Vegas.SourceProgram.ProtocolState
