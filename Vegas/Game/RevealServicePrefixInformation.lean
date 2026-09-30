/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefix
import Vegas.Source.ObservationRecall

/-! # Exact source views at restricted service prefixes

The actual checkpoint invariant equates source information with the native
before-view. Native own-response recall remains separate:
different aliases may refine a source information set without changing this
view or the source Boolean choices.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The operational checkpoint decoder fixes the existing source state
uniquely; this does not identify native histories or their private aliases. -/
theorem PrefixCheckpoint.state_unique
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {initial : State L setup.context} {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (refs : ContextRefs (graph setup).layout Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout (outputLayout program event))
    (offset count : Nat) (left right : ProtocolState program)
    (execution : (application setup leaks).Execution)
    (leftRelated : PrefixCheckpoint setup leaks initial program refs revelations outputs
      offset count left execution)
    (rightRelated : PrefixCheckpoint setup leaks initial program refs revelations outputs
      offset count right execution) : left = right := by
  have leftRead := PrefixCheckpoint.decode program refs revelations outputs offset count
    left execution leftRelated
  have rightRead := PrefixCheckpoint.decode program refs revelations outputs offset count
    right execution rightRelated
  exact Option.some.inj (leftRead.symm.trans rightRead)

theorem PublicPrefixCheckpoint.observe_eq_iff
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {leftInitial rightInitial : State L setup.context} (who : Player) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (graph setup).layout Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout
        (outputLayout program event))
      (offset count : Nat) (left right : ProtocolState program)
      (nativeLeft nativeRight : (application setup leaks).Execution),
      PublicPrefixCheckpoint setup leaks leftInitial program refs revelations outputs
        offset count left nativeLeft →
      PublicPrefixCheckpoint setup leaks rightInitial program refs revelations outputs
        offset count right nativeRight →
      nativeLeft.network.leaked who = nativeRight.network.leaked who →
      (ProtocolState.observe who program left = ProtocolState.observe who program right ↔
        nativeLeft.observe (application setup leaks) who =
          nativeRight.observe (application setup leaks) who) := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro refs revelations outputs offset count left right nativeLeft nativeRight
        leftRelated rightRelated leaked
      cases count with
      | zero =>
          obtain ⟨leftSource, rfl, _leftRevelations, leftCheckpoint⟩ := leftRelated
          obtain ⟨rightSource, rfl, _rightRevelations, rightCheckpoint⟩ := rightRelated
          constructor
          · exact leftCheckpoint.observe_eq rightCheckpoint who leaked
          · exact source_view_eq_of_observe_eq setup leaks refs who _ _
              nativeLeft nativeRight leftCheckpoint.agrees rightCheckpoint.agrees
              leftCheckpoint.history rightCheckpoint.history
      | succ count => exact leftRelated.elim
  | sample name fresh law next ih =>
      intro refs revelations outputs offset count left right nativeLeft nativeRight
        leftRelated rightRelated leaked
      cases count with
      | zero =>
          obtain ⟨leftSource, rfl, _leftRevelations, leftCheckpoint⟩ := leftRelated
          obtain ⟨rightSource, rfl, _rightRevelations, rightCheckpoint⟩ := rightRelated
          change Sum.inl (leftSource.view who) = Sum.inl (rightSource.view who) ↔ _
          rw [Sum.inl.injEq]
          exact ⟨leftCheckpoint.observe_eq rightCheckpoint who leaked,
            source_view_eq_of_observe_eq setup leaks refs who leftSource rightSource
              nativeLeft nativeRight leftCheckpoint.agrees rightCheckpoint.agrees
              leftCheckpoint.history rightCheckpoint.history⟩
      | succ count => exact leftRelated.elim
  | commit name owner fresh guard next ih =>
      intro refs revelations outputs offset count left right nativeLeft nativeRight
        leftRelated rightRelated leaked
      cases count with
      | zero =>
          obtain ⟨leftSource, rfl, _leftRevelations, leftCheckpoint⟩ := leftRelated
          obtain ⟨rightSource, rfl, _rightRevelations, rightCheckpoint⟩ := rightRelated
          change Sum.inl (leftSource.view who) = Sum.inl (rightSource.view who) ↔ _
          rw [Sum.inl.injEq]
          exact ⟨leftCheckpoint.observe_eq rightCheckpoint who leaked,
            source_view_eq_of_observe_eq setup leaks refs who leftSource rightSource
              nativeLeft nativeRight leftCheckpoint.agrees rightCheckpoint.agrees
              leftCheckpoint.history rightCheckpoint.history⟩
      | succ count => exact leftRelated.elim
  | reveal published owner name fresh selected unresolved next ih =>
      intro refs revelations outputs offset count left right nativeLeft nativeRight
        leftRelated rightRelated leaked
      cases count with
      | zero =>
          obtain ⟨leftSource, rfl, _leftRevelations, leftCheckpoint⟩ := leftRelated
          obtain ⟨rightSource, rfl, _rightRevelations, rightCheckpoint⟩ := rightRelated
          change Sum.inl (leftSource.view who) = Sum.inl (rightSource.view who) ↔ _
          rw [Sum.inl.injEq]
          exact ⟨leftCheckpoint.observe_eq rightCheckpoint who leaked,
            source_view_eq_of_observe_eq setup leaks refs who leftSource rightSource
              nativeLeft nativeRight leftCheckpoint.agrees rightCheckpoint.agrees
              leftCheckpoint.history rightCheckpoint.history⟩
      | succ count =>
          cases left with
          | inl source => exact leftRelated.elim
          | inr left =>
              cases right with
              | inl source => exact rightRelated.elim
              | inr right =>
                  have tail := ih _ (revelations.reveal selected) _ (offset + 1) count
                    left right nativeLeft nativeRight leftRelated rightRelated leaked
                  simpa only [ProtocolState.observe, Sum.elim_inr, Sum.inr.injEq] using tail

/-- The source view is already fixed by the local application observation.
This direction needs no agreement of passive leaks or auxiliary metadata. -/
theorem PublicPrefixCheckpoint.source_view_eq_of_application_eq
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {leftInitial rightInitial : State L setup.context} (who : Player) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (graph setup).layout Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef (graph setup).layout
        (outputLayout program event))
      (offset count : Nat) (left right : ProtocolState program)
      (nativeLeft nativeRight : (application setup leaks).Execution),
      PublicPrefixCheckpoint setup leaks leftInitial program refs revelations outputs
        offset count left nativeLeft →
      PublicPrefixCheckpoint setup leaks rightInitial program refs revelations outputs
        offset count right nativeRight →
      (application setup leaks).observePlayer nativeLeft.application who =
        (application setup leaks).observePlayer nativeRight.application who →
      ProtocolState.observe who program left = ProtocolState.observe who program right := by
  have head {Γ : SourceCtx Player L} (leftSource rightSource : Config Player L Γ)
      (refs : ContextRefs (graph setup).layout Γ) (rank : Nat)
      (nativeLeft nativeRight : (application setup leaks).Execution)
      (leftRelated : PublicCheckpoint setup leaks leftInitial leftSource refs rank nativeLeft)
      (rightRelated : PublicCheckpoint setup leaks rightInitial rightSource refs rank nativeRight)
      (same : (application setup leaks).observePlayer nativeLeft.application who =
        (application setup leaks).observePlayer nativeRight.application who) :
      leftSource.view who = rightSource.view who := by
    let aligned : (application setup leaks).Execution :=
      { nativeRight with network := nativeLeft.network, receipts := nativeLeft.receipts }
    apply source_view_eq_of_observe_eq setup leaks refs who leftSource rightSource
      nativeLeft aligned leftRelated.agrees rightRelated.agrees
      leftRelated.history rightRelated.history
    change ReactiveApplication.PlayerView.mk _ _ _ = ReactiveApplication.PlayerView.mk _ _ _
    exact congrArg (fun localView =>
      (⟨nativeLeft.network.observe who, localView, nativeLeft.receipts⟩ :
        (application setup leaks).PlayerView)) same
  intro Γ openNames program refs revelations outputs offset count
  induction count generalizing Γ openNames program refs revelations outputs offset with
  | zero =>
      intro left right nativeLeft nativeRight leftRelated rightRelated same
      cases program <;>
        obtain ⟨leftSource, rfl, _, leftCheckpoint⟩ := leftRelated <;>
        obtain ⟨rightSource, rfl, _, rightCheckpoint⟩ := rightRelated
      · exact head _ _ refs offset nativeLeft nativeRight
          leftCheckpoint rightCheckpoint same
      all_goals
        exact congrArg Sum.inl (head leftSource rightSource refs offset nativeLeft nativeRight
          leftCheckpoint rightCheckpoint same)
  | succ count ih =>
      intro left right nativeLeft nativeRight leftRelated rightRelated same
      cases program with
      | ret payoffs => exact leftRelated.elim
      | sample name fresh law next => exact leftRelated.elim
      | commit name owner fresh guard next => exact leftRelated.elim
      | reveal published owner name fresh selected unresolved next =>
          cases left with
          | inl source => exact leftRelated.elim
          | inr left =>
              cases right with
              | inl source => exact rightRelated.elim
              | inr right =>
                  exact congrArg Sum.inr (ih next _ _ _ (offset + 1) left right
                    nativeLeft nativeRight leftRelated rightRelated same)

end Vegas
