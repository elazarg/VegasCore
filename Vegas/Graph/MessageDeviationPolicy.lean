/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageDeviationContinuation

/-! # Completing observation-local effective actions to a graph policy

An effective action is specified only at observations reached by a native
deviation. When it is single-valued there, it extends to a total graph policy:
unreached bindings choose failure and unreached resolutions choose withholding.
The completed policy uses the graph observation, not native cache markers or
the graph's own-action history.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- Partial effective actions at each decision in a typed graph. The ownership
equality makes decisions controlled by other players uninhabited. -/
def ObservationActionRelation (focal : Player) :
    {Γ Δ : VCtx Player L} → Graph Player L Γ Δ → Type
  | _, _, .ret _ => PUnit
  | _, _, .sample _ _ _ next => ObservationActionRelation focal next
  | Γ, _, .bind (payload := payload) _ owner _ next =>
      ((owner = focal) → Observation L focal Γ →
        PublicationResult (L.Val payload) → Prop) × ObservationActionRelation focal next
  | Γ, _, .resolve _ owner _ _ _ _ next =>
      ((owner = focal) → Observation L focal Γ → Bool → Prop) ×
        ObservationActionRelation focal next

namespace ObservationActionRelation

/-- Equal graph observations must give the same effective action. This is the
information condition, separate from the total policy construction. -/
def Functional (focal : Player) : {Γ Δ : VCtx Player L} →
    (graph : Graph Player L Γ Δ) → ObservationActionRelation focal graph → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample _ _ _ next, relation => Functional focal next relation
  | _, _, .bind _ _ _ next, relation =>
      (∀ owned observation left right,
        relation.1 owned observation left → relation.1 owned observation right →
          left = right) ∧ Functional focal next relation.2
  | _, _, .resolve _ _ _ _ _ _ next, relation =>
      (∀ owned observation left right,
        relation.1 owned observation left → relation.1 owned observation right →
          left = right) ∧ Functional focal next relation.2

private def chooseAction {α : Type} (relation : α → Prop) (fallback : α) : α := by
  classical
  exact if existsAction : ∃ action, relation action then
    Classical.choose existsAction else fallback

private theorem chooseAction_eq {α : Type} (relation : α → Prop) (fallback action : α)
    (functional : ∀ left right, relation left → relation right → left = right)
    (realized : relation action) : chooseAction relation fallback = action := by
  unfold chooseAction
  rw [dif_pos ⟨action, realized⟩]
  exact functional _ action (Classical.choose_spec _) realized

/-- Extend the partial action relation, choosing source failure at observations
outside its domain. This definition requires no reachability assumption. -/
def complete (focal : Player) : {Γ Δ : VCtx Player L} →
    (graph : Graph Player L Γ Δ) → ObservationActionRelation focal graph →
      BehavioralPolicy focal graph
  | _, _, .ret _, _ => PUnit.unit
  | _, _, .sample _ _ _ next, relation => complete focal next relation
  | _, _, .bind _ _ _ next, relation =>
      (fun owned view => FinDist.pure (chooseAction (relation.1 owned view.1) .failure),
        complete focal next relation.2)
  | _, _, .resolve _ _ _ _ _ _ next, relation =>
      (fun owned view => FinDist.pure (chooseAction (relation.1 owned view.1) false),
        complete focal next relation.2)

/-- A policy realizes each specified effective action, at every possible
own-action history. -/
def RealizedBy (focal : Player) : {Γ Δ : VCtx Player L} →
    (graph : Graph Player L Γ Δ) → ObservationActionRelation focal graph →
      BehavioralPolicy focal graph → Prop
  | _, _, .ret _, _, _ => True
  | _, _, .sample _ _ _ next, relation, policy => RealizedBy focal next relation policy
  | _, _, .bind _ _ _ next, relation, policy =>
      (∀ owned observation history action, relation.1 owned observation action →
        policy.1 owned (observation, history) = FinDist.pure action) ∧
      RealizedBy focal next relation.2 policy.2
  | _, _, .resolve _ _ _ _ _ _ next, relation, policy =>
      (∀ owned observation history action, relation.1 owned observation action →
        policy.1 owned (observation, history) = FinDist.pure action) ∧
      RealizedBy focal next relation.2 policy.2

theorem complete_ignoresOwnHistory (focal : Player) (graph : Graph Player L Γ Δ)
    (relation : ObservationActionRelation focal graph) :
    PolicyIgnoresOwnHistory focal graph (complete focal graph relation) := by
  induction graph with
  | ret => trivial
  | sample _ _ _ _ ih => exact ih relation
  | bind _ _ _ _ ih => exact ⟨fun _ _ _ _ => rfl, ih relation.2⟩
  | resolve _ _ _ _ _ _ _ ih => exact ⟨fun _ _ _ _ => rfl, ih relation.2⟩

theorem complete_realizes (focal : Player) (graph : Graph Player L Γ Δ)
    (relation : ObservationActionRelation focal graph)
    (functional : Functional focal graph relation) :
    RealizedBy focal graph relation (complete focal graph relation) := by
  induction graph with
  | ret => trivial
  | sample _ _ _ _ ih => exact ih relation functional
  | bind _ _ _ _ ih =>
      refine ⟨?_, ih relation.2 functional.2⟩
      intro owned observation history action realized
      exact congrArg FinDist.pure (chooseAction_eq _ _ action
        (functional.1 owned observation) realized)
  | resolve _ _ _ _ _ _ _ ih =>
      refine ⟨?_, ih relation.2 functional.2⟩
      intro owned observation history action realized
      exact congrArg FinDist.pure (chooseAction_eq _ _ action
        (functional.1 owned observation) realized)

/-- Restrict partial actions along the same typed prefix as graph policies. -/
def tail (focal : Player) : {Γ : VCtx Player L} → {whole : Graph Player L Γ Δ} →
    {target : VCtx Player L} → {suffix : Graph Player L target Δ} → {length : Nat} →
    Prefix Δ whole suffix length → ObservationActionRelation focal whole →
      ObservationActionRelation focal suffix
  | _, _, _, _, _, .refl _, relation => relation
  | _, _, _, _, _, .sample walk, relation => tail focal walk relation
  | _, _, _, _, _, .bind walk, relation => tail focal walk relation.2
  | _, _, _, _, _, .resolve walk, relation => tail focal walk relation.2

theorem realizedBy_tail (focal : Player) {whole : Graph Player L Γ₀ Δ}
    {suffix : Graph Player L Γ Δ} {length : Nat} (walk : Prefix Δ whole suffix length)
    (relation : ObservationActionRelation focal whole) (policy : BehavioralPolicy focal whole)
    (realizes : RealizedBy focal whole relation policy) :
    RealizedBy focal suffix (tail focal walk relation) (walk.policyTail focal policy) := by
  induction walk with
  | refl => exact realizes
  | sample _ ih => exact ih relation policy realizes
  | bind _ ih => exact ih relation.2 policy.2 realizes.2
  | resolve _ ih => exact ih relation.2 policy.2 realizes.2

end ObservationActionRelation

end Vegas.GraphRuntime
