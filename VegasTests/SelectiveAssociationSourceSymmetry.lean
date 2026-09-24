/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceCalendar
import Interaction.ReactiveRoundReachability

/-! # The local symmetry used by the common source perturbations

At Alice's binding response, flip her Boolean choice and the value in her
private Alice-certificate request. Claims, addresses, request kinds, silence,
and every replay stay unchanged. This is a permutation of the full response
menu. The history and conditional-belief consequences require additional
prefix laws; local distribution symmetry alone is not an equilibrium proof.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Vegas.SourceProgram Interaction GameTheory GameTheory.Protocol
open GameTheory.Math.Probability

def flipBinding : PublicationResult Bool → PublicationResult Bool
  | .failure => .failure
  | .success bit => .success (!bit)

theorem flipBinding_involutive : Function.Involutive flipBinding := by
  intro value
  cases value <;> simp [flipBinding]

def flipFact (fact : NamedFact) : NamedFact :=
  if fact.1 = 0 then (fact.1, !fact.2) else fact

theorem flipFact_involutive : Function.Involutive flipFact := by
  rintro ⟨name, bit⟩
  by_cases same : name = 0 <;> simp [flipFact, same]

def flipSubmission {Claim : Type} (submission : Submission Claim) : Submission Claim :=
  { submission with
    binding := flipBinding submission.binding
    evidence := submission.evidence.map flipFact }

theorem flipSubmission_involutive {Claim : Type} :
    Function.Involutive (flipSubmission (Claim := Claim)) := by
  intro submission
  cases submission with
  | mk address kind claim binding evidence =>
      simp only [flipSubmission]
      rw [flipBinding_involutive]
      congr 1
      cases evidence with
      | none => rfl
      | some fact => exact congrArg some (flipFact_involutive fact)

def flipResponse {Claim : Type} (action : (application Claim).Action) :
    (application Claim).Action :=
  match action.transmission with
  | some (.submit submission) => ⟨some (.submit (flipSubmission submission))⟩
  | _ => action

theorem flipResponse_involutive {Claim : Type} :
    Function.Involutive (flipResponse (Claim := Claim)) := by
  rintro ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay => rfl
      | submit submission =>
          change (⟨some (.submit (flipSubmission (flipSubmission submission)))⟩ :
            (application Claim).Action) = _
          rw [flipSubmission_involutive]

theorem flipResponse_available (Claim : Type) [Fintype Claim] (who : Player)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (action : (application Claim).Action)
    (allowed : action ∈ (menu Claim).actions who past view) :
    flipResponse action ∈ (menu Claim).actions who past view := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact allowed
  | some transmission =>
      cases transmission with
      | replay => exact allowed
      | submit submission => exact every_submission Claim who past view _

def responseFlip (Claim : Type) [Fintype Claim] (who : Player)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView) :
    (menu Claim).actions who past view ≃ (menu Claim).actions who past view where
  toFun action := ⟨flipResponse action.1, flipResponse_available Claim who past view _ action.2⟩
  invFun action := ⟨flipResponse action.1, flipResponse_available Claim who past view _ action.2⟩
  left_inv action := Subtype.ext (flipResponse_involutive action.1)
  right_inv action := Subtype.ext (flipResponse_involutive action.1)

theorem uniform_flip (Claim : Type) [Fintype Claim] (who : Player)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView) :
    ((menu Claim).uniformResponses who past view).map flipResponse =
      (menu Claim).uniformResponses who past view := by
  classical
  let choices := (menu Claim).actions who past view
  let : Nonempty choices :=
    ⟨⟨((menu Claim).nonempty who past view).choose,
      ((menu Claim).nonempty who past view).choose_spec⟩⟩
  have uniform : (FinDist.uniformOfFintype : FinDist choices).map
      (responseFlip Claim who past view) = FinDist.uniformOfFintype := by
    apply FinDist.ext_of_prob
    intro action
    obtain ⟨before, rfl⟩ := (responseFlip Claim who past view).surjective action
    rw [FinDist.prob_map_of_injective _ (responseFlip Claim who past view).injective]
    simp only [FinDist.prob_uniformOfFintype]
  change ((FinDist.uniformOfFintype : FinDist choices).map Subtype.val).map flipResponse = _
  rw [FinDist.map_comp]
  calc
    _ = ((FinDist.uniformOfFintype : FinDist choices).map
        (responseFlip Claim who past view)).map Subtype.val := by rw [FinDist.map_comp]; rfl
    _ = _ := by rw [uniform]; rfl

theorem flipResponse_playing (Claim : Type) (defaultClaim : Claim)
    (event : Event) (binding : PublicationResult Bool) :
    flipResponse (playing Claim defaultClaim event binding) =
      playing Claim defaultClaim event (flipBinding binding) := rfl

theorem fairBinding_flip (Claim : Type) (defaultClaim : Claim) (event : Event) :
    ((FinDist.uniformOfFintype (α := Bool)).map
        (fun bit => playing Claim defaultClaim event (.success bit))).map flipResponse =
      (FinDist.uniformOfFintype (α := Bool)).map
        (fun bit => playing Claim defaultClaim event (.success bit)) := by
  have uniform : (FinDist.uniformOfFintype (α := Bool)).map Bool.not =
      FinDist.uniformOfFintype := by
    apply FinDist.ext_of_prob
    intro bit
    have involutive : Function.Involutive Bool.not := fun bit => Bool.not_not bit
    have same := FinDist.prob_map_of_injective Bool.not involutive.injective
      (FinDist.uniformOfFintype (α := Bool)) (!bit)
    simpa only [Bool.not_not, FinDist.prob_uniformOfFintype] using same
  rw [FinDist.map_comp]
  calc
    _ = ((FinDist.uniformOfFintype (α := Bool)).map Bool.not).map
        (fun bit => playing Claim defaultClaim event (.success bit)) := by
      rw [FinDist.map_comp]
      rfl
    _ = _ := by rw [uniform]

theorem alice_policy_flip (Claim : Type) (defaultClaim : Claim)
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (visit : view.application.visit = some 0) :
    (policy Claim defaultClaim alice past view).map flipResponse =
      policy Claim defaultClaim alice past view := by
  simp only [policy, visit, eventOwner, bindingOwner]
  simp only [Fin.val_zero, Nat.zero_mod, ↓reduceIte]
  exact fairBinding_flip Claim defaultClaim 0

end VegasTests.SelectiveAssociation.NamedSource
