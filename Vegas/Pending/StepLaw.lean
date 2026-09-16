/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.Application

/-! # Local step laws for the graph message host -/

noncomputable section
namespace Vegas.GraphRuntime

open Interaction GameTheory.Math.Probability Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Inclusion of an openable, correctly typed candidate realizes that exact
graph binding choice.  Acceptance remains public-shape independent of this
opening fact; the premise identifies its private denotation for simulation. -/
theorem handle_bind_openable
    {Γ Δ : VCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (runtime : GraphRuntime Player L Δ)
    (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt serial : Nat) (handle : Handle Player)
    (encoded : L.Val (R.result payload))
    (howner : handle.1 = owner)
    (hlookup : candidates.lookup handle = .openable ⟨R.result payload, encoded⟩) :
    runtime.handle
      (.running (.bind name owner fresh next) ideal values bindings candidates pc clock enteredAt)
      ⟨(owner, serial), .commitment pc handle⟩ =
      some (.running next (VEnv.cons encoded ideal) (PublicValues.consSealed values)
        ((name, handle) :: bindings) (candidates.accept handle) (pc + 1) clock clock) := by
  simp [GraphRuntime.handle, Message.sender, advanceBind, howner, hlookup, Raw.as?]

/-- A fresh accepted handle is frozen as unopenable and realizes the explicit
failure binding, without requiring an inhabitant of the payload type. -/
theorem handle_bind_fresh
    {Γ Δ : VCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (runtime : GraphRuntime Player L Δ)
    (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt serial : Nat) (handle : Handle Player)
    (howner : handle.1 = owner) (hlookup : candidates.lookup handle = .fresh) :
    runtime.handle
      (.running (.bind name owner fresh next) ideal values bindings candidates pc clock enteredAt)
      ⟨(owner, serial), .commitment pc handle⟩ =
      some (.running next
        (VEnv.cons ((R.valueEquiv payload).symm .failure) ideal)
        (PublicValues.consSealed values) ((name, handle) :: bindings)
        (candidates.accept handle) (pc + 1) clock clock) := by
  simp [GraphRuntime.handle, Message.sender, advanceBind, howner, hlookup]

/-- A verified opening atomically publishes the same failure-aware value as
the graph semantics.  Guard rejection is included: `acceptedResult` itself
turns only the current proposal into failure. -/
theorem handle_resolve_verified
    {Γ Δ : VCtx Player L} {outputName bindingName : VarId}
    {owner : Player} {payload : L.Ty}
    (runtime : GraphRuntime Player L Δ)
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt serial : Nat) (handle : Handle Player)
    (encoded : L.Val (R.result payload))
    (hbinding : lookupBinding bindings bindingName = some handle)
    (howner : handle.1 = owner)
    (hverify : candidates.verify handle ⟨R.result payload, encoded⟩ = true)
    (hsource : ideal.get source = encoded) :
    runtime.handle
      (.running (.resolve outputName owner bindingName fresh source checks next)
        ideal (PublicValues.ofVEnv ideal) bindings candidates pc clock enteredAt)
      ⟨(owner, serial), .opening pc handle ⟨R.result payload, encoded⟩⟩ =
      some (.running next
        (VEnv.cons ((R.valueEquiv payload).symm
          (acceptedResult source checks ideal true)) ideal)
        (PublicValues.consPublic ((R.valueEquiv payload).symm
          (acceptedResult source checks ideal true)) (PublicValues.ofVEnv ideal))
        bindings candidates (pc + 1) clock clock) := by
  simp only [GraphRuntime.handle, Message.sender, hbinding, howner, hverify,
    Raw.as?_mk]
  have haccepted := acceptedProposal_eq_acceptedResult source checks ideal true
  simp only [proposedResult, if_true, hsource] at haccepted
  rw [haccepted]
  rfl

/-- Authenticated withholding realizes the graph's `disclose = false` step. -/
theorem handle_resolve_withhold
    {Γ Δ : VCtx Player L} {outputName bindingName : VarId}
    {owner : Player} {payload : L.Ty}
    (runtime : GraphRuntime Player L Δ)
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt serial : Nat) :
    runtime.handle
      (.running (.resolve outputName owner bindingName fresh source checks next)
        ideal values bindings candidates pc clock enteredAt)
      ⟨(owner, serial), .withhold pc⟩ =
      some (.running next (VEnv.cons ((R.valueEquiv payload).symm .failure) ideal)
        (PublicValues.consPublic ((R.valueEquiv payload).symm .failure) values)
        bindings candidates (pc + 1) clock clock) := by
  simp [GraphRuntime.handle, Message.sender, advanceResolve]

/-- A chance tick is exactly the retained graph distribution, mapped by the
single immutable public-field append. -/
theorem environmentStep_sample
    {Γ Δ : VCtx Player L} {name : VarId} {payload : L.Ty}
    (runtime : GraphRuntime Player L Δ)
    (fresh : name ∉ Γ.map Prod.fst) (law : PublicDist (L := L) Γ payload)
    (next : Graph Player L ((name, .pub payload) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat) :
    runtime.environmentStep
      (.running (.sample name fresh law next) ideal values bindings candidates pc clock enteredAt)
      .tick =
      (law.evalPublic values).map fun value =>
        .running next (VEnv.cons value ideal) (PublicValues.consPublic value values)
          bindings candidates (pc + 1) (clock + 1) (clock + 1) := by
  rfl

/-- Bind expiry appends an unopenable/failure private field and no handle. -/
theorem environmentStep_bind_expired
    {Γ Δ : VCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    (runtime : GraphRuntime Player L Δ)
    (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat)
    (hexpired : runtime.deadline pc ≤ clock + 1 - enteredAt) :
    runtime.environmentStep
      (.running (.bind name owner fresh next) ideal values bindings candidates pc clock enteredAt)
      .tick = FinDist.pure
        (.running next (VEnv.cons ((R.valueEquiv payload).symm .failure) ideal)
          (PublicValues.consSealed values) bindings candidates
          (pc + 1) (clock + 1) (clock + 1)) := by
  simp [environmentStep, GraphRuntime.tick, advanceBindFailure, hexpired]

/-- Resolve expiry atomically publishes the canonical failure value. -/
theorem environmentStep_resolve_expired
    {Γ Δ : VCtx Player L} {outputName bindingName : VarId}
    {owner : Player} {payload : L.Ty}
    (runtime : GraphRuntime Player L Δ)
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat)
    (hexpired : runtime.deadline pc ≤ clock + 1 - enteredAt) :
    runtime.environmentStep
      (.running (.resolve outputName owner bindingName fresh source checks next)
        ideal values bindings candidates pc clock enteredAt) .tick =
      FinDist.pure (.running next
        (VEnv.cons ((R.valueEquiv payload).symm .failure) ideal)
        (PublicValues.consPublic ((R.valueEquiv payload).symm .failure) values)
        bindings candidates (pc + 1) (clock + 1) (clock + 1)) := by
  simp [environmentStep, GraphRuntime.tick, advanceResolve, hexpired]

/-- Ticking a terminal state changes only its clock and cannot reroll or append. -/
theorem environmentStep_ret
    {Δ : VCtx Player L} (runtime : GraphRuntime Player L Δ)
    (payoffs : List (Player × PublicExpr (L := L) Δ L.int))
    (ideal : VEnv L Δ) (values : PublicValues Δ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat) :
    runtime.environmentStep (.running (.ret payoffs) ideal values bindings candidates
      pc clock enteredAt) .tick =
      FinDist.pure (.running (.ret payoffs) ideal values bindings candidates
        pc (clock + 1) enteredAt) := by
  rfl

end Vegas.GraphRuntime
