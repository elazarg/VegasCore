/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProtocolPolicy
import GameTheoryExtensions.Math.Probability.FinDist

/-! # Information-local behavioral policies at a commitment interface

Admission constrains the support of each binding law. Encoding retains that
law exactly; it neither conditions away forbidden choices nor renormalizes.
The interface still separately restricts the execution history tree.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def BehavioralPolicy.Admitted {who : Player} : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → CommitmentInterface program →
    BehavioralPolicy who program → Prop
  | _, _, .ret _, _, _ => True
  | _, _, .sample _ _ _ next, admission, policy => Admitted next admission policy
  | _, _, .commit _ owner _ _ next, admission, policy =>
      (∀ (own : owner = who) view choice, choice ∈ (policy.1 own view).support →
        (admission none).Admits choice) ∧
      Admitted next (fun site => admission (some site)) policy.2
  | _, _, .reveal _ _ _ _ _ _ next, admission, policy => Admitted next admission policy.2

def BehavioralPolicy.protocolAction {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → BehavioralPolicy who program →
    ProtocolView who program → FinDist (Option (OwnAction Player L))
  | _, _, .ret _ => fun _ _ => FinDist.pure none
  | _, _, .sample _ _ _ next => fun policy =>
      Sum.elim (fun _ => FinDist.pure none) (protocolAction next policy)
  | _, _, .commit (payload := payload) name owner _ _ next => fun policy =>
      Sum.elim
        (fun view => if own : owner = who then
          (policy.1 own view).map (fun choice => some (.commit owner name payload choice))
          else FinDist.pure none)
        (protocolAction next policy.2)
  | _, _, .reveal _ owner name _ _ _ next => fun policy =>
      Sum.elim
        (fun view => if own : owner = who then
          (policy.1 own view).map (fun disclose => some (.reveal owner name disclose))
          else FinDist.pure none)
        (protocolAction next policy.2)

theorem BehavioralPolicy.protocolAction_mem_menu {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : BehavioralPolicy who program) → policy.Admitted program admission →
    ∀ view action, action ∈ (policy.protocolAction program view).support →
      ProtocolView.menu who program admission view action
  | _, _, .ret _, _, _, _, _, _, member => by
      have same := FinDist.mem_support_pure.mp member
      subst_vars
      simp [ProtocolView.menu, ProtocolView.actor]
  | _, _, .sample _ _ _ next, admission, policy, permitted, view, action, member => by
      cases view with
      | inl current =>
          have same := FinDist.mem_support_pure.mp member
          subst action
          simp [ProtocolView.menu, ProtocolView.actor]
      | inr later =>
          exact protocolAction_mem_menu next admission policy permitted later action member
  | _, _, .commit _ owner _ _ next, admission, policy, permitted, view, action, member => by
      cases view with
      | inl current =>
          by_cases own : owner = who
          · simp only [protocolAction, Sum.elim_inl, own, dite_true, FinDist.support_map] at member
            obtain ⟨choice, supported, rfl⟩ := member
            exact ⟨by simp [ProtocolView.actor, own], choice,
              permitted.1 own current choice supported, by simp [own]⟩
          · simp only [protocolAction, Sum.elim_inl, own, dite_false,
              FinDist.mem_support_pure] at member
            subst action
            simp [ProtocolView.menu, ProtocolView.actor, own]
      | inr later =>
          exact protocolAction_mem_menu next (fun site => admission (some site))
            policy.2 permitted.2 later action member
  | _, _, .reveal _ owner _ _ _ _ next, admission, policy, permitted, view, action, member => by
      cases view with
      | inl current =>
          by_cases own : owner = who
          · simp only [protocolAction, Sum.elim_inl, own, dite_true, FinDist.support_map] at member
            obtain ⟨disclose, _, rfl⟩ := member
            exact ⟨by simp [ProtocolView.actor, own], disclose, by simp [own]⟩
          · simp only [protocolAction, Sum.elim_inl, own, dite_false,
              FinDist.mem_support_pure] at member
            subst action
            simp [ProtocolView.menu, ProtocolView.actor, own]
      | inr later =>
          exact protocolAction_mem_menu next admission policy.2 permitted later action member

def BehavioralPolicy.toProtocol {who : Player} {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (policy : BehavioralPolicy who program) (permitted : policy.Admitted program admission)
    (view : ProtocolView who program) :
    FinDist {action : Option (OwnAction Player L) //
      ProtocolView.menu who program admission view action} :=
  (policy.protocolAction program view).toSubtype
    (policy.protocolAction_mem_menu program admission permitted view)

@[simp] theorem BehavioralPolicy.toProtocol_map_val {who : Player}
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (policy : BehavioralPolicy who program) (permitted : policy.Admitted program admission)
    (view : ProtocolView who program) :
    (policy.toProtocol program admission permitted view).map Subtype.val =
      policy.protocolAction program view := FinDist.map_val_toSubtype _ _

def BehavioralPolicy.fromProtocol {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    ((view : ProtocolView who program) → FinDist
      {action : Option (OwnAction Player L) //
        ProtocolView.menu who program admission view action}) → BehavioralPolicy who program
  | _, _, .ret _, _, _ => PUnit.unit
  | _, _, .sample _ _ _ next, admission, policy =>
      fromProtocol next admission (fun view => policy (Sum.inr view))
  | _, _, .commit (payload := payload) name owner _ _ next, admission, policy =>
      (fun _ view => (policy (Sum.inl view)).map
        (fun choice => OwnAction.binding owner name payload choice.1),
        fromProtocol next (fun site => admission (some site)) (fun view => policy (Sum.inr view)))
  | _, _, .reveal _ _ _ _ _ _ next, admission, policy =>
      (fun _ view => (policy (Sum.inl view)).map (fun choice => OwnAction.disclosure choice.1),
        fromProtocol next admission (fun view => policy (Sum.inr view)))

theorem BehavioralPolicy.admitted_fromProtocol {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : (view : ProtocolView who program) → FinDist
      {action : Option (OwnAction Player L) //
        ProtocolView.menu who program admission view action}) →
    (fromProtocol program admission policy).Admitted program admission
  | _, _, .ret _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, policy =>
      admitted_fromProtocol next admission (fun view => policy (Sum.inr view))
  | _, _, .commit _ owner _ _ next, admission, policy => by
      constructor
      · intro own view choice member
        obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ member
        have legal := selected.2
        cases action : selected.1 with
        | none => simp [ProtocolView.menu, ProtocolView.actor, action, own] at legal
        | some actionValue =>
            simp only [ProtocolView.menu, action, ProtocolView.available,
              Sum.elim_inl, Set.mem_ofPred_eq] at legal
            obtain ⟨value, permitted, actionEq⟩ := legal.2
            simpa only [action, actionEq, OwnAction.binding_commit] using permitted
      · exact admitted_fromProtocol next (fun site => admission (some site))
          (fun view => policy (Sum.inr view))
  | _, _, .reveal _ _ _ _ _ _ next, admission, policy =>
      admitted_fromProtocol next admission (fun view => policy (Sum.inr view))

theorem BehavioralPolicy.from_toProtocol {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : BehavioralPolicy who program) → (permitted : policy.Admitted program admission) →
    fromProtocol program admission (policy.toProtocol program admission permitted) = policy
  | _, _, .ret _, _, policy, _ => by cases policy; rfl
  | _, _, .sample _ _ _ next, admission, policy, permitted =>
      from_toProtocol next admission policy permitted
  | _, _, .commit _ _ _ _ next, admission, policy, permitted => by
      apply Prod.ext
      · funext own view
        dsimp only [fromProtocol]
        rw [toProtocol, FinDist.map_toSubtype]
        simp only [protocolAction, Sum.elim_inl, dite_eq_left own,
          FinDist.map_comp, Function.comp_def, OwnAction.binding_commit]
        exact FinDist.map_id _
      · exact from_toProtocol next (fun site => admission (some site)) policy.2 permitted.2
  | _, _, .reveal _ _ _ _ _ _ next, admission, policy, permitted => by
      apply Prod.ext
      · funext own view
        dsimp only [fromProtocol]
        rw [toProtocol, FinDist.map_toSubtype]
        simp only [protocolAction, Sum.elim_inl, dite_eq_left own,
          FinDist.map_comp, Function.comp_def, OwnAction.disclosure]
        exact FinDist.map_id _
      · exact from_toProtocol next admission policy.2 permitted

private theorem protocolLaw_idle {who : Player} {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (view : ProtocolView who program) (inactive : ProtocolView.actor who program view ≠ some who)
    (law : FinDist {action : Option (OwnAction Player L) //
      ProtocolView.menu who program admission view action}) :
    law.map Subtype.val = FinDist.pure none := by
  have onlyIdle (choice : {action : Option (OwnAction Player L) //
      ProtocolView.menu who program admission view action}) : choice.1 = none := by
    have legal := choice.2
    cases selected : choice.1 with
    | none => rfl
    | some action =>
        simp only [ProtocolView.menu, selected] at legal
        exact (inactive legal.1).elim
  calc
    _ = law.map (fun _ => none) :=
      FinDist.map_congr_of_eq_on_support (fun choice _ => onlyIdle choice)
    _ = _ := by simp [FinDist.map_eq_bind]

theorem BehavioralPolicy.protocolAction_fromProtocol {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : (view : ProtocolView who program) → FinDist
      {action : Option (OwnAction Player L) //
        ProtocolView.menu who program admission view action}) →
    ∀ view, (fromProtocol program admission policy).protocolAction program view =
      (policy view).map Subtype.val
  | _, _, .ret _, admission, policy, view =>
      (protocolLaw_idle _ admission view (by simp [ProtocolView.actor]) (policy view)).symm
  | _, _, .sample _ _ _ next, admission, policy, view => by
      cases view with
      | inl current =>
          exact (protocolLaw_idle _ admission (Sum.inl current)
            (by simp [ProtocolView.actor]) (policy (Sum.inl current))).symm
      | inr later =>
          exact protocolAction_fromProtocol next admission (fun view => policy (Sum.inr view)) later
  | _, _, .commit _ owner _ _ next, admission, policy, view => by
      cases view with
      | inl current =>
          by_cases own : owner = who
          · simp only [fromProtocol, protocolAction, Sum.elim_inl, dite_eq_left own,
              FinDist.map_comp]
            apply FinDist.map_congr_of_eq_on_support
            intro choice _
            have legal := choice.2
            cases selected : choice.1 with
            | none => simp [ProtocolView.menu, ProtocolView.actor, selected, own] at legal
            | some action =>
                simp only [ProtocolView.menu, selected, ProtocolView.available,
                  Sum.elim_inl, Set.mem_ofPred_eq] at legal
                obtain ⟨value, _, actionEq⟩ := legal.2
                simp [selected, actionEq]
          · simp only [protocolAction, Sum.elim_inl, dite_eq_right own]
            exact (protocolLaw_idle _ admission (Sum.inl current)
              (by simp [ProtocolView.actor, own]) (policy (Sum.inl current))).symm
      | inr later =>
          exact protocolAction_fromProtocol next (fun site => admission (some site))
            (fun view => policy (Sum.inr view)) later
  | _, _, .reveal _ owner _ _ _ _ next, admission, policy, view => by
      cases view with
      | inl current =>
          by_cases own : owner = who
          · simp only [fromProtocol, protocolAction, Sum.elim_inl, dite_eq_left own,
              FinDist.map_comp]
            apply FinDist.map_congr_of_eq_on_support
            intro choice _
            have legal := choice.2
            cases selected : choice.1 with
            | none => simp [ProtocolView.menu, ProtocolView.actor, selected, own] at legal
            | some action =>
                simp only [ProtocolView.menu, selected, ProtocolView.available,
                  Sum.elim_inl, Set.mem_ofPred_eq] at legal
                obtain ⟨disclose, actionEq⟩ := legal.2
                simp [selected, actionEq, OwnAction.disclosure]
          · simp only [protocolAction, Sum.elim_inl, dite_eq_right own]
            exact (protocolLaw_idle _ admission (Sum.inl current)
              (by simp [ProtocolView.actor, own]) (policy (Sum.inl current))).symm
      | inr later =>
          exact protocolAction_fromProtocol next admission (fun view => policy (Sum.inr view)) later

def behavioralPolicyEquiv {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) (who : Player) :
    {policy : BehavioralPolicy who program // policy.Admitted program admission} ≃
      (informationModel program admission initial).BehavioralPolicy who where
  toFun policy := policy.1.toProtocol program admission policy.2
  invFun policy := ⟨BehavioralPolicy.fromProtocol program admission policy,
    BehavioralPolicy.admitted_fromProtocol program admission policy⟩
  left_inv policy := Subtype.ext
    (BehavioralPolicy.from_toProtocol program admission policy.1 policy.2)
  right_inv policy := by
    funext view
    apply FinDist.map_injective Subtype.val_injective
    rw [BehavioralPolicy.toProtocol_map_val, BehavioralPolicy.protocolAction_fromProtocol]

end Vegas.SourceProgram
