/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Protocol

/-! # Source policies at an explicit commitment interface

The policy bridge is playerwise and information-local. Admission constrains
the actions a policy chooses; the execution protocol separately constrains the
legal histories on which subgames are defined.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A source pure policy satisfies the admission rule at every owned site and
every source decision view. -/
def PurePolicy.Admitted {who : Player} : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → CommitmentInterface program →
    PurePolicy who program → Prop
  | _, _, .ret _, _, _ => True
  | _, _, .sample _ _ _ next, admission, policy => Admitted next admission policy
  | _, _, .commit _ owner _ _ next, admission, policy =>
      (∀ (own : owner = who) view, (admission none).Admits (policy.1 own view)) ∧
        Admitted next (fun site => admission (some site)) policy.2
  | _, _, .reveal _ _ _ _ _ _ next, admission, policy => Admitted next admission policy.2

/-- Encoding an action does not require a utility, hidden configuration, or
the strategies of the other players. -/
def PurePolicy.protocolAction {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → PurePolicy who program →
    ProtocolView who program → Option (OwnAction Player L)
  | _, _, .ret _ => fun _ _ => none
  | _, _, .sample _ _ _ next => fun policy =>
      Sum.elim (fun _ => none) (protocolAction next policy)
  | _, _, .commit (payload := payload) name owner _ _ next => fun policy =>
      Sum.elim
        (fun view => if own : owner = who then
          some (.commit owner name payload (policy.1 own view)) else none)
        (protocolAction next policy.2)
  | _, _, .reveal _ owner name _ _ _ next => fun policy =>
      Sum.elim
        (fun view => if own : owner = who then
          some (.reveal owner name (policy.1 own view)) else none)
        (protocolAction next policy.2)

theorem PurePolicy.protocolAction_mem_menu {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : PurePolicy who program) → policy.Admitted program admission →
    ∀ view, ProtocolView.menu who program admission view (policy.protocolAction program view)
  | _, _, .ret _, _, _, _, _ => by simp [protocolAction, ProtocolView.menu, ProtocolView.actor]
  | _, _, .sample _ _ _ next, admission, policy, permitted, view => by
      cases view with
      | inl current => simp [protocolAction, ProtocolView.menu, ProtocolView.actor]
      | inr later => exact protocolAction_mem_menu next admission policy permitted later
  | _, _, .commit (payload := payload) name owner _ _ next, admission, policy, permitted, view => by
      cases view with
      | inl current =>
          by_cases own : owner = who
          · simp only [protocolAction, Sum.elim_inl, own, ↓reduceDIte, ProtocolView.menu,
              ProtocolView.actor, ProtocolView.available, Set.mem_ofPred_eq]
            exact ⟨by simp, policy.1 own current, permitted.1 own current, rfl⟩
          · simp [protocolAction, own, ProtocolView.menu, ProtocolView.actor]
      | inr later =>
          exact protocolAction_mem_menu next (fun site => admission (some site))
            policy.2 permitted.2 later
  | _, _, .reveal _ owner _ _ _ _ next, admission, policy, permitted, view => by
      cases view with
      | inl current =>
          by_cases own : owner = who
          · simp [protocolAction, own, ProtocolView.menu, ProtocolView.actor,
              ProtocolView.available]
          · simp [protocolAction, own, ProtocolView.menu, ProtocolView.actor]
      | inr later => exact protocolAction_mem_menu next admission policy.2 permitted later

def PurePolicy.toProtocol {who : Player} {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (policy : PurePolicy who program) (permitted : policy.Admitted program admission)
    (view : ProtocolView who program) :
    { action : Option (OwnAction Player L) //
      ProtocolView.menu who program admission view action } :=
  ⟨policy.protocolAction program view,
    policy.protocolAction_mem_menu program admission permitted view⟩

/-- Decode a protocol policy back into source decisions. The explicit function
type is definitionally the canonical model's policy type; it avoids threading
an irrelevant initial configuration through recursive suffixes. -/
def PurePolicy.fromProtocol {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    ((view : ProtocolView who program) →
      { action : Option (OwnAction Player L) //
        ProtocolView.menu who program admission view action }) →
    PurePolicy who program
  | _, _, .ret _, _, _ => PUnit.unit
  | _, _, .sample _ _ _ next, admission, policy =>
      fromProtocol next admission (fun view => policy (Sum.inr view))
  | _, _, .commit (payload := payload) name owner _ _ next, admission, policy =>
      (fun _ view => OwnAction.binding owner name payload (policy (Sum.inl view)).1,
        fromProtocol next (fun site => admission (some site)) (fun view => policy (Sum.inr view)))
  | _, _, .reveal _ _ _ _ _ _ next, admission, policy =>
      (fun _ view => OwnAction.disclosure (policy (Sum.inl view)).1,
        fromProtocol next admission (fun view => policy (Sum.inr view)))

theorem PurePolicy.admitted_fromProtocol {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : (view : ProtocolView who program) →
      { action : Option (OwnAction Player L) //
        ProtocolView.menu who program admission view action }) →
    (fromProtocol program admission policy).Admitted program admission
  | _, _, .ret _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, policy =>
      admitted_fromProtocol next admission (fun view => policy (Sum.inr view))
  | _, _, .commit _ owner _ _ next, admission, policy => by
      constructor
      · intro own view
        have legal := (policy (Sum.inl view)).2
        cases selected : (policy (Sum.inl view)).1 with
        | none => simp [ProtocolView.menu, ProtocolView.actor, selected, own] at legal
        | some action =>
            simp only [ProtocolView.menu, selected, ProtocolView.available,
              Sum.elim_inl, Set.mem_ofPred_eq] at legal
            obtain ⟨value, permitted, actionEq⟩ := legal.2
            simp only [fromProtocol, selected, actionEq, OwnAction.binding_commit]
            exact permitted
      · exact admitted_fromProtocol next (fun site => admission (some site))
          (fun view => policy (Sum.inr view))
  | _, _, .reveal _ _ _ _ _ _ next, admission, policy =>
      admitted_fromProtocol next admission (fun view => policy (Sum.inr view))

theorem PurePolicy.from_toProtocol {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : PurePolicy who program) → (permitted : policy.Admitted program admission) →
    fromProtocol program admission (policy.toProtocol program admission permitted) = policy
  | _, _, .ret _, _, policy, _ => by cases policy; rfl
  | _, _, .sample _ _ _ next, admission, policy, permitted =>
      from_toProtocol next admission policy permitted
  | _, _, .commit _ _ _ _ next, admission, policy, permitted => by
      apply Prod.ext
      · funext own view
        simp [fromProtocol, toProtocol, protocolAction, own]
      · exact from_toProtocol next (fun site => admission (some site)) policy.2 permitted.2
  | _, _, .reveal _ _ _ _ _ _ next, admission, policy, permitted => by
      apply Prod.ext
      · funext own view
        simp [fromProtocol, toProtocol, protocolAction, own, OwnAction.disclosure]
      · exact from_toProtocol next admission policy.2 permitted

theorem PurePolicy.protocolAction_fromProtocol {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : (view : ProtocolView who program) →
      { action : Option (OwnAction Player L) //
        ProtocolView.menu who program admission view action }) →
    ∀ view, (fromProtocol program admission policy).protocolAction program view = (policy view).1
  | _, _, .ret _, _, policy, view => by
      have legal := (policy view).2
      cases selected : (policy view).1 with
      | none => rfl
      | some action => simp [ProtocolView.menu, ProtocolView.actor, selected] at legal
  | _, _, .sample _ _ _ next, admission, policy, view => by
      cases view with
      | inl current =>
          have legal := (policy (Sum.inl current)).2
          cases selected : (policy (Sum.inl current)).1 with
          | none => rfl
          | some action => simp [ProtocolView.menu, ProtocolView.actor, selected] at legal
      | inr later =>
          exact protocolAction_fromProtocol next admission (fun view => policy (Sum.inr view)) later
  | _, _, .commit _ owner _ _ next, admission, policy, view => by
      cases view with
      | inl current =>
          have legal := (policy (Sum.inl current)).2
          by_cases own : owner = who
          · cases selected : (policy (Sum.inl current)).1 with
            | none => simp [ProtocolView.menu, ProtocolView.actor, selected, own] at legal
            | some action =>
                simp only [ProtocolView.menu, selected, ProtocolView.available,
                  Sum.elim_inl, Set.mem_ofPred_eq] at legal
                obtain ⟨value, _, actionEq⟩ := legal.2
                simp [fromProtocol, protocolAction, own, selected, actionEq]
          · cases selected : (policy (Sum.inl current)).1 with
            | none => simp [fromProtocol, protocolAction, own]
            | some action => simp [ProtocolView.menu, ProtocolView.actor, selected, own] at legal
      | inr later =>
          exact protocolAction_fromProtocol next (fun site => admission (some site))
            (fun view => policy (Sum.inr view)) later
  | _, _, .reveal _ owner _ _ _ _ next, admission, policy, view => by
      cases view with
      | inl current =>
          have legal := (policy (Sum.inl current)).2
          by_cases own : owner = who
          · cases selected : (policy (Sum.inl current)).1 with
            | none => simp [ProtocolView.menu, ProtocolView.actor, selected, own] at legal
            | some action =>
                simp only [ProtocolView.menu, selected, ProtocolView.available,
                  Sum.elim_inl, Set.mem_ofPred_eq] at legal
                obtain ⟨disclose, actionEq⟩ := legal.2
                simp [fromProtocol, protocolAction, own, selected, actionEq, OwnAction.disclosure]
          · cases selected : (policy (Sum.inl current)).1 with
            | none => simp [fromProtocol, protocolAction, own]
            | some action => simp [ProtocolView.menu, ProtocolView.actor, selected, own] at legal
      | inr later =>
          exact protocolAction_fromProtocol next admission (fun view => policy (Sum.inr view)) later

/-- The bridge covers every legal information-local protocol policy, including
policies used as deviations. It does not enlarge a player's observation. -/
def purePolicyEquiv {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) (who : Player) :
    { policy : PurePolicy who program // policy.Admitted program admission } ≃
      (informationModel program admission initial).Policy who where
  toFun policy := policy.1.toProtocol program admission policy.2
  invFun policy := ⟨PurePolicy.fromProtocol program admission policy,
    PurePolicy.admitted_fromProtocol program admission policy⟩
  left_inv policy := Subtype.ext (PurePolicy.from_toProtocol program admission policy.1 policy.2)
  right_inv policy := by
    funext view
    apply Subtype.ext
    exact PurePolicy.protocolAction_fromProtocol program admission policy view

end Vegas.SourceProgram
