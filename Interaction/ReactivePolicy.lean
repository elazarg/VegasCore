/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveProtocol

/-! # All information-local response policies

The native policy interface and canonical behavioral policies are equivalent.
The equivalence is playerwise and includes every replacement policy, with no
capacity constraint or access to the scheduler's private control state.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

def encodePolicy (policy : app.Policy) (info : app.Info) :
    FinDist {choice : Option app.Action // choice.isSome = info.isSome} :=
  match info with
  | none => FinDist.pure ⟨none, rfl⟩
  | some (history, view) => (policy history view).map fun action => ⟨some action, rfl⟩

def decodePolicy (policy : (info : app.Info) →
    FinDist {choice : Option app.Action // choice.isSome = info.isSome}) : app.Policy :=
  fun history view => (policy (some (history, view))).map
    (fun selected => selected.1.getD ⟨none⟩)

theorem decode_encodePolicy (policy : app.Policy) :
    app.decodePolicy (app.encodePolicy policy) = policy := by
  funext history view
  simp only [decodePolicy, encodePolicy, FinDist.map_comp, Function.comp_def, Option.getD_some]
  exact FinDist.map_id _

theorem encode_decodePolicy (policy : (info : app.Info) →
    FinDist {choice : Option app.Action // choice.isSome = info.isSome}) :
    app.encodePolicy (app.decodePolicy policy) = policy := by
  funext info
  cases info with
  | none =>
      have unique (choice : {choice : Option app.Action //
          choice.isSome = (none : app.Info).isSome}) : choice = ⟨none, rfl⟩ := by
        apply Subtype.ext
        have valid := choice.2
        cases selected : choice.1 with
        | none => rfl
        | some action => simp [selected] at valid
      change FinDist.pure _ = policy none
      symm
      calc
        _ = (policy none).map id := (FinDist.map_id _).symm
        _ = (policy none).map (fun _ => ⟨none, rfl⟩) :=
          FinDist.map_congr_of_eq_on_support (fun choice _ => unique choice)
        _ = _ := FinDist.map_const _ _
  | some arguments =>
      rcases arguments with ⟨history, view⟩
      rw [encodePolicy, decodePolicy, FinDist.map_comp]
      calc
        _ = (policy (some (history, view))).map id := by
          apply FinDist.map_congr_of_eq_on_support
          intro selected _
          apply Subtype.ext
          have present := selected.2
          cases chosen : selected.1 with
          | none => simp [chosen] at present
          | some action => simp [chosen]
        _ = _ := FinDist.map_id _

variable [DecidableEq Principal]

def policyEquiv (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (who : Principal) :
    app.Policy ≃ (app.information initial horizon scheduler).BehavioralPolicy who where
  toFun := app.encodePolicy
  invFun := app.decodePolicy
  left_inv := app.decode_encodePolicy
  right_inv := app.encode_decodePolicy

end Interaction.ReactiveApplication
