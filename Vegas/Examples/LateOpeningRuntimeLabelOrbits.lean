/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLabelTrace

/-! # Legal native history orbits preserving Bob's complete information -/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeLabelOrbits

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLabelTrace

variable (horizon : Nat) (scheduler : app.Scheduler)

def permuteHistory (permutation : Equiv.Perm (Fin 3))
    (history : (rawMenu.protocol initial horizon scheduler).History) :
    (rawMenu.protocol initial horizon scheduler).History :=
  ⟨permuteProtocolState permutation history.state,
    permuteTrace permutation horizon scheduler history.trace⟩

theorem permuteProtocolState_inverse (permutation : Equiv.Perm (Fin 3))
    (state : app.ProtocolState) (trace : (rawMenu.protocol initial horizon scheduler).Trace state) :
    permuteProtocolState permutation.symm (permuteProtocolState permutation state) = state := by
  cases state with
  | none => rfl
  | some control =>
      have aligned := recordedLabels_history horizon scheduler control
        (rawMenu.toRawTrace initial horizon scheduler trace)
      change some { control with
        execution := permuteExecution permutation.symm
          (permuteExecution permutation control.execution) } = _
      rw [permuteExecution_inverse permutation control.execution aligned]

theorem permuteTrace_length (permutation : Equiv.Perm (Fin 3)) :
    ∀ {state} (trace : (rawMenu.protocol initial horizon scheduler).Trace state),
      (permuteTrace permutation horizon scheduler trace).length = trace.length
  | _, .start => rfl
  | _, .extend prior _ _ _ =>
      congrArg Nat.succ (permuteTrace_length permutation prior)

private theorem extend_eq_of_history_target_eq {E : ExecutionProtocol Player}
    {first second : E.History} (same : first = second) {target other : E.State}
    (targetEq : target = other) (joint : ∀ who, Option (E.Action who))
    (firstLegal : E.Legal first.state joint) (secondLegal : E.Legal second.state joint)
    (firstReached : target ∈ (E.step first.state ⟨joint, firstLegal⟩).support)
    (secondReached : other ∈ (E.step second.state ⟨joint, secondLegal⟩).support) :
    first.extend firstLegal firstReached = second.extend secondLegal secondReached := by
  subst second
  subst other
  rfl

theorem permuteHistory_inverse (permutation : Equiv.Perm (Fin 3))
    (history : (rawMenu.protocol initial horizon scheduler).History) :
    permuteHistory horizon scheduler permutation.symm
      (permuteHistory horizon scheduler permutation history) = history := by
  rcases history with ⟨state, trace⟩
  induction trace with
  | start => rfl
  | @extend source target prior joint legal reached ih =>
      have targetEq := permuteProtocolState_inverse horizon scheduler permutation target
        (.extend prior joint legal reached)
      apply extend_eq_of_history_target_eq ih targetEq joint


def historyEquiv (permutation : Equiv.Perm (Fin 3)) :
    (rawMenu.protocol initial horizon scheduler).History ≃
      (rawMenu.protocol initial horizon scheduler).History where
  toFun := permuteHistory horizon scheduler permutation
  invFun := permuteHistory horizon scheduler permutation.symm
  left_inv := permuteHistory_inverse horizon scheduler permutation
  right_inv history := by
    simpa only [Equiv.symm_symm] using
      permuteHistory_inverse horizon scheduler permutation.symm history

theorem permuteHistory_info_bob (permutation : Equiv.Perm (Fin 3))
    (history : (rawMenu.protocol initial horizon scheduler).History) :
    (rawMenu.signals initial horizon scheduler).infoOf bob
        (permuteHistory horizon scheduler permutation history).trace =
      (rawMenu.signals initial horizon scheduler).infoOf bob history.trace :=
  info_bob_permutation permutation horizon scheduler history.state history.trace

def informationHistoryEquiv (permutation : Equiv.Perm (Fin 3))
    (site : (rawMenu.information initial horizon scheduler).InformationSite bob) :
    (rawMenu.information initial horizon scheduler).InformationHistory bob site.1 ≃
      (rawMenu.information initial horizon scheduler).InformationHistory bob site.1 where
  toFun history := ⟨permuteHistory horizon scheduler permutation history.1,
    (permuteHistory_info_bob horizon scheduler permutation history.1).trans history.2⟩
  invFun history := ⟨permuteHistory horizon scheduler permutation.symm history.1,
    (permuteHistory_info_bob horizon scheduler permutation.symm history.1).trans history.2⟩
  left_inv history := Subtype.ext (permuteHistory_inverse horizon scheduler permutation history.1)
  right_inv history := by
    apply Subtype.ext
    simpa only [Equiv.symm_symm] using
      permuteHistory_inverse horizon scheduler permutation.symm history.1

end Vegas.Examples.LateOpeningRuntimeLabelOrbits
