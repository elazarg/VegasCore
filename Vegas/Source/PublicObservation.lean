/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Semantics

/-! # Public-cell congruence for source readouts and guards

Public environment readout and completed guard inputs depend only on public
data and publication cells. Hidden immutable bindings are not guard readouts.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable {Γ : SourceCtx Player L}

omit [DecidableEq Player] in
/-- Two states with the same public data and the same publications have the same
public result, whatever their private bindings are. -/
theorem sourcePublicEnv_congr :
    {Γ : SourceCtx Player L} → (left right : State L Γ) →
    (publicEq : ∀ {x τ} (h : HasVar Γ x (.publicData τ)), left.get h = right.get h) →
    (publicationEq : ∀ {x τ} (h : HasVar Γ x (.publication τ)), left.get h = right.get h) →
    sourcePublicEnv left = sourcePublicEnv right
  | [], _, _, _, _ => rfl
  | (_, .publicData _) :: tail, left, right, publicEq, publicationEq => by
      have tailEq := sourcePublicEnv_congr (Γ := tail)
        (fun _ _ h => left.get (HasVar.there h)) (fun _ _ h => right.get (HasVar.there h))
        (fun h => publicEq (HasVar.there h)) (fun h => publicationEq (HasVar.there h))
      simp only [sourcePublicEnv, publicEq HasVar.here, tailEq]
  | (_, .commitment _ _) :: tail, left, right, publicEq, publicationEq => by
      have tailEq := sourcePublicEnv_congr (Γ := tail)
        (fun _ _ h => left.get (HasVar.there h)) (fun _ _ h => right.get (HasVar.there h))
        (fun h => publicEq (HasVar.there h)) (fun h => publicationEq (HasVar.there h))
      simpa only [sourcePublicEnv] using tailEq
  | (_, .privateInput _ _) :: tail, left, right, publicEq, publicationEq => by
      have tailEq := sourcePublicEnv_congr (Γ := tail)
        (fun _ _ h => left.get (HasVar.there h)) (fun _ _ h => right.get (HasVar.there h))
        (fun h => publicEq (HasVar.there h)) (fun h => publicationEq (HasVar.there h))
      simpa only [sourcePublicEnv] using tailEq
  | (_, .publication _) :: tail, left, right, publicEq, publicationEq => by
      have tailEq := sourcePublicEnv_congr (Γ := tail)
        (fun _ _ h => left.get (HasVar.there h)) (fun _ _ h => right.get (HasVar.there h))
        (fun h => publicEq (HasVar.there h)) (fun h => publicationEq (HasVar.there h))
      simp only [sourcePublicEnv, publicationEq HasVar.here, tailEq]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem Revelation.result_congr {payload : L.Ty} (revelation : Revelation Γ payload)
    (left right : State L Γ)
    (publicationEq : ∀ {x τ} (h : HasVar Γ x (.publication τ)), left.get h = right.get h) :
    revelation.result left = revelation.result right := by
  cases revelation with
  | unrevealed => rfl
  | revealed cell => exact publicationEq cell

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem SourceGuardRead.result_congr {author : Player} {τ : L.Ty}
    (read : SourceGuardRead Γ author τ) (revelations : Revelations Γ)
    (left right : State L Γ)
    (publicEq : ∀ {x τ} (h : HasVar Γ x (.publicData τ)), left.get h = right.get h)
    (publicationEq : ∀ {x τ} (h : HasVar Γ x (.publication τ)), left.get h = right.get h) :
    read.result revelations left = read.result revelations right := by
  cases read with
  | publicData h => exact congrArg _ (publicEq h)
  | commitment h => exact Revelation.result_congr _ _ _ publicationEq
  | publication h => exact publicationEq h

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem Obligation.accepts_congr (obligation : Obligation Γ) (revelations : Revelations Γ)
    (left right : State L Γ)
    (publicEq : ∀ {x τ} (h : HasVar Γ x (.publicData τ)), left.get h = right.get h)
    (publicationEq : ∀ {x τ} (h : HasVar Γ x (.publication τ)), left.get h = right.get h) :
    obligation.accepts revelations left = obligation.accepts revelations right := by
  simp only [Obligation.accepts, SourceGuard.accepts,
    Revelation.result_congr _ left right publicationEq]
  refine congrArg _ ?_
  funext x τ h hx
  exact SourceGuardRead.result_congr _ _ left right publicEq publicationEq

end Vegas.SourceProgram
