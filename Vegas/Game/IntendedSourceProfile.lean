module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceContinuation
public import Vegas.Source.IntendedGame
public import Vegas.Source.Honest
public import Vegas.Source.ValueBindingAdmission
public import GameTheory.Protocol.RestrictionProfile

@[expose] public section

/-! # Intended source choices in a full interface

The same pointwise choice map embeds an intended profile into every commitment
interface. Its decoded policies bind values and disclose at every abstract source
view. The embedding preserves every intended information site directly.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A choice that is not a refusal to disclose. -/
def NotRefusal (choice : Option (OwnAction Player L)) : Prop :=
  ∀ owner name, choice ≠ some (.reveal owner name false)

/-- An intended action never refuses a disclosure. -/
theorem ProtocolView.intendedAvailable_notRefusal (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (view : ProtocolView who program) →
      ∀ action ∈ intendedAvailable who program view, NotRefusal (some action)
  | _, _, .ret _, _, _, member => member.elim
  | _, _, .sample _ _ _ next, view, action, member => by
      cases view with
      | inl _ => exact member.elim
      | inr later => exact intendedAvailable_notRefusal who next later action member
  | _, _, .commit _ _ _ _ next, view, action, member => by
      cases view with
      | inl _ =>
          obtain ⟨_, _, rfl⟩ := member
          exact fun _ _ => nofun
      | inr later => exact intendedAvailable_notRefusal who next later action member
  | _, _, .reveal _ _ _ _ _ _ next, view, action, member => by
      cases view with
      | inl _ =>
          change action = _ at member
          subst member
          intro other otherName same
          simp at same
      | inr later => exact intendedAvailable_notRefusal who next later action member

/-- A protocol policy that never refuses decodes to a disclosing source policy. -/
theorem BehavioralPolicy.disclosing_fromProtocol {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : (view : ProtocolView who program) → PMF
      {action : Option (OwnAction Player L) //
        ProtocolView.menu who program admission view action}) →
    (∀ view, ∀ choice ∈ (policy view).support, NotRefusal choice.1) →
    Disclosing program (BehavioralPolicy.fromProtocol program admission policy)
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, policy, opens =>
      disclosing_fromProtocol next admission (fun view => policy (Sum.inr view))
        (fun view => opens (Sum.inr view))
  | _, _, .commit _ _ _ _ next, admission, policy, opens =>
      disclosing_fromProtocol next (fun site => admission (some site))
        (fun view => policy (Sum.inr view)) (fun view => opens (Sum.inr view))
  | _, _, .reveal _ owner name _ _ _ next, admission, policy, opens => by
      refine ⟨fun own view active refused => ?_,
        disclosing_fromProtocol next admission (fun view => policy (Sum.inr view))
          (fun view => opens (Sum.inr view))⟩
      obtain ⟨choice, supported, decision⟩ := (PMF.mem_support_map_iff _ _ _).mp refused
      have legal := choice.2
      have notRefused := opens (Sum.inl view) choice supported
      cases selected : choice.1 with
      | none =>
          rw [selected] at legal
          simp [ProtocolView.menu, ProtocolView.actor, own, active] at legal
      | some action =>
          rw [selected] at legal decision notRefused
          obtain ⟨_, disclose, rfl⟩ := legal
          change disclose = false at decision
          subst decision
          exact notRefused owner name rfl

/-- A protocol policy supported by intended choices binds a value and opens,
including at abstract views that are not reached by the intended profile. -/
theorem BehavioralPolicy.honest_fromProtocol_of_intended {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : (view : ProtocolView who program) → PMF
      {action : Option (OwnAction Player L) //
        ProtocolView.menu who program admission view action}) →
    (∀ view, ∀ choice ∈ (policy view).support,
      ProtocolView.intendedMenu who program view choice.1) →
    Honest program (BehavioralPolicy.fromProtocol program admission policy)
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, policy, intended =>
      honest_fromProtocol_of_intended next admission (fun view => policy (Sum.inr view))
        (fun view => intended (Sum.inr view))
  | _, _, .commit _ owner _ _ next, admission, policy, intended => by
      constructor
      · intro own view active choice reached
        obtain ⟨selected, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
        have legal := intended (Sum.inl view) selected supported
        cases action : selected.1 with
        | none =>
            simp [ProtocolView.intendedMenu, ProtocolView.actor, action, own, active] at legal
        | some chosen =>
            simp only [ProtocolView.intendedMenu, action, ProtocolView.intendedAvailable,
              Sum.elim_inl, Set.mem_ofPred_eq] at legal
            obtain ⟨value, _, equality⟩ := legal.2
            exact ⟨value, by simp [equality]⟩
      · exact honest_fromProtocol_of_intended next (fun site => admission (some site))
          (fun view => policy (Sum.inr view)) (fun view => intended (Sum.inr view))
  | _, _, .reveal _ owner name _ _ _ next, admission, policy, intended => by
      constructor
      · intro own view active refused
        obtain ⟨selected, supported, equality⟩ := (PMF.mem_support_map_iff _ _ _).mp refused
        have legal := intended (Sum.inl view) selected supported
        cases action : selected.1 with
        | none =>
            simp [ProtocolView.intendedMenu, ProtocolView.actor, action, own, active] at legal
        | some chosen =>
            simp only [ProtocolView.intendedMenu, action, ProtocolView.intendedAvailable,
              Sum.elim_inl, Set.mem_singleton_iff] at legal
            simp [action, legal.2, OwnAction.disclosure] at equality
      · exact honest_fromProtocol_of_intended next admission
          (fun view => policy (Sum.inr view)) (fun view => intended (Sum.inr view))

/-- Repair the binding part of a recorded own action, retaining its identity. -/
private def submitOwnBinding : Option (OwnAction Player L) → Option (OwnAction Player L)
  | some (.commit owner name payload choice) =>
      some (.commit owner name payload (some (choice.getD .failure)))
  | action => action

private theorem BehavioralPolicy.protocolAction_submitBindings {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (policy : BehavioralPolicy who program) → (view : ProtocolView who program) →
    (policy.submitBindings program).protocolAction program view =
      (policy.protocolAction program view).map submitOwnBinding
  | _, _, .ret _, policy, view => by simp [protocolAction, PMF.pure_map, submitOwnBinding]
  | _, _, .sample _ _ _ next, policy, view => by
      cases view with
      | inl current => simp [protocolAction, PMF.pure_map, submitOwnBinding]
      | inr later => exact protocolAction_submitBindings next policy later
  | _, _, .commit _ owner _ _ next, policy, view => by
      cases view with
      | inl current =>
          simp only [protocolAction, submitBindings, Sum.elim_inl]
          by_cases own : owner = who
          · simp only [dite_eq_left own]
            by_cases active : who ∉ current.defaulted
            · simp only [dite_eq_left active, PMF.map_comp]
              rfl
            · simp [active, PMF.pure_map, submitOwnBinding]
          · simp [own, PMF.pure_map, submitOwnBinding]
      | inr later => exact protocolAction_submitBindings next policy.2 later
  | _, _, .reveal _ owner _ _ _ _ next, policy, view => by
      cases view with
      | inl current =>
          simp only [protocolAction, submitBindings, Sum.elim_inl]
          by_cases own : owner = who
          · simp only [dite_eq_left own]
            by_cases active : who ∉ current.defaulted
            · simp only [dite_eq_left active, PMF.map_comp]
              rfl
            · simp [active, PMF.pure_map, submitOwnBinding]
          · simp [own, PMF.pure_map, submitOwnBinding]
      | inr later => exact protocolAction_submitBindings next policy.2 later

private theorem submitOwnBinding_of_intendedAvailable (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (view : ProtocolView who program) →
      ∀ action ∈ ProtocolView.intendedAvailable who program view,
        submitOwnBinding (some action) = some action
  | _, _, .ret _, _, _, member => member.elim
  | _, _, .sample _ _ _ next, view, action, member => by
      cases view with
      | inl _ => exact member.elim
      | inr later => exact submitOwnBinding_of_intendedAvailable who next later action member
  | _, _, .commit _ _ _ _ next, view, action, member => by
      cases view with
      | inl current =>
          obtain ⟨value, _, rfl⟩ := member
          rfl
      | inr later => exact submitOwnBinding_of_intendedAvailable who next later action member
  | _, _, .reveal _ _ _ _ _ _ next, view, action, member => by
      cases view with
      | inl current =>
          change action = _ at member
          subst member
          rfl
      | inr later => exact submitOwnBinding_of_intendedAvailable who next later action member

/-- Force only the reveal flag of a recorded own action. -/
private def forceOwnReveal : Option (OwnAction Player L) → Option (OwnAction Player L)
  | some (.reveal owner name _) => some (.reveal owner name true)
  | action => action

private theorem BehavioralPolicy.protocolAction_forceDisclose {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (policy : BehavioralPolicy who program) → (view : ProtocolView who program) →
    (policy.forceDisclose program).protocolAction program view =
      (policy.protocolAction program view).map forceOwnReveal
  | _, _, .ret _, policy, view => by simp [protocolAction, PMF.pure_map, forceOwnReveal]
  | _, _, .sample _ _ _ next, policy, view => by
      cases view with
      | inl current => simp [protocolAction, PMF.pure_map, forceOwnReveal]
      | inr later => exact protocolAction_forceDisclose next policy later
  | _, _, .commit _ owner _ _ next, policy, view => by
      cases view with
      | inl current =>
          simp only [protocolAction, forceDisclose, Sum.elim_inl]
          by_cases own : owner = who
          · simp only [dite_eq_left own]
            by_cases active : who ∉ current.defaulted
            · simp only [dite_eq_left active, PMF.map_comp]
              rfl
            · simp [active, PMF.pure_map, forceOwnReveal]
          · simp [own, PMF.pure_map, forceOwnReveal]
      | inr later => exact protocolAction_forceDisclose next policy.2 later
  | _, _, .reveal _ owner _ _ _ _ next, policy, view => by
      cases view with
      | inl current =>
          simp only [protocolAction, forceDisclose, Sum.elim_inl]
          by_cases own : owner = who
          · simp only [dite_eq_left own]
            by_cases active : who ∉ current.defaulted
            · simp only [dite_eq_left active, PMF.pure_map, PMF.map_comp,
                Function.comp_def, forceOwnReveal]
              exact (PMF.map_const _ _).symm
            · simp [active, PMF.pure_map, forceOwnReveal]
          · simp [own, PMF.pure_map, forceOwnReveal]
      | inr later => exact protocolAction_forceDisclose next policy.2 later

private theorem forceOwnReveal_of_intendedAvailable (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (view : ProtocolView who program) →
      ∀ action ∈ ProtocolView.intendedAvailable who program view,
        forceOwnReveal (some action) = some action
  | _, _, .ret _, _, _, member => member.elim
  | _, _, .sample _ _ _ next, view, action, member => by
      cases view with
      | inl _ => exact member.elim
      | inr later => exact forceOwnReveal_of_intendedAvailable who next later action member
  | _, _, .commit _ _ _ _ next, view, action, member => by
      cases view with
      | inl current =>
          obtain ⟨value, _, rfl⟩ := member
          rfl
      | inr later => exact forceOwnReveal_of_intendedAvailable who next later action member
  | _, _, .reveal _ _ _ _ _ _ next, view, action, member => by
      cases view with
      | inl current =>
          change action = _ at member
          subst member
          rfl
      | inr later => exact forceOwnReveal_of_intendedAvailable who next later action member

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- The intended action law at every abstract source view, in any commitment interface. -/
def intendedSourceProfile (admission : CommitmentInterface setup.program)
    (intended : Profile setup.intendedModel.behavioralSignature) :
    Profile (setup.informationModel admission).behavioralSignature :=
  fun who info => (intended who info).map
    ((setup.intendedRestriction admission).choice who info)

theorem intendedSourceProfile_extends (admission : CommitmentInterface setup.program)
    (intended : Profile setup.intendedModel.behavioralSignature) :
    (setup.intendedRestriction admission).ExtendsProfile intended
      (setup.intendedSourceProfile admission intended) := by
  intro who site
  rfl

theorem intendedSourceProfile_mem_intendedMenu (admission : CommitmentInterface setup.program)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (who : Player) (info : setup.ProtocolView who)
    (choice : (setup.informationModel admission).Choice who info)
    (supported : choice ∈ (setup.intendedSourceProfile admission intended who info).support) :
    choice.1 ∈ setup.intendedMenu who info := by
  obtain ⟨selected, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact selected.2

theorem intendedSourceProfile_notRefusal (admission : CommitmentInterface setup.program)
    (intended : Profile setup.intendedModel.behavioralSignature)
    (who : Player) (info : setup.ProtocolView who) :
    ∀ choice ∈ (setup.intendedSourceProfile admission intended who info).support,
      NotRefusal choice.1 := by
  intro choice member
  have legal :=
    setup.intendedSourceProfile_mem_intendedMenu admission intended who info choice member
  cases info with
  | none =>
      change choice.1 = none at legal
      rw [legal]
      exact fun _ _ => nofun
  | some view =>
      change ProtocolView.intendedMenu who setup.program view choice.1 at legal
      cases chosen : choice.1 with
      | none => exact fun _ _ => nofun
      | some action =>
          rw [chosen] at legal
          exact ProtocolView.intendedAvailable_notRefusal who setup.program view action legal.2

theorem intendedSourceProfile_disclosing (admission : CommitmentInterface setup.program)
    (intended : Profile setup.intendedModel.behavioralSignature) (who : Player) :
    Disclosing setup.program (setup.decodeBehavioralProfile
      admission (setup.intendedSourceProfile admission intended) who) :=
  BehavioralPolicy.disclosing_fromProtocol setup.program _ _
    (fun view => setup.intendedSourceProfile_notRefusal admission intended who (some view))

theorem intendedSourceProfile_honest (admission : CommitmentInterface setup.program)
    (intended : Profile setup.intendedModel.behavioralSignature) (who : Player) :
    Honest setup.program (setup.decodeBehavioralProfile
      admission (setup.intendedSourceProfile admission intended) who) :=
  BehavioralPolicy.honest_fromProtocol_of_intended setup.program _ _
    (fun view choice member =>
      setup.intendedSourceProfile_mem_intendedMenu admission intended who (some view) choice member)

/-- Every intended profile has an extension whose decoded source policies
 disclose at every reveal. -/
theorem exists_disclosing_extension (admission : CommitmentInterface setup.program)
    (intended : Profile setup.intendedModel.behavioralSignature) :
    ∃ target : Profile (setup.informationModel admission).behavioralSignature,
      (setup.intendedRestriction admission).ExtendsProfile intended target ∧
        ∀ who, Disclosing setup.program (setup.decodeBehavioralProfile admission target who) :=
  ⟨setup.intendedSourceProfile admission intended,
    setup.intendedSourceProfile_extends admission intended,
    setup.intendedSourceProfile_disclosing admission intended⟩

private theorem submitOwnBinding_of_intendedMenu (who : Player) (info : setup.ProtocolView who)
    (action : Option (OwnAction Player L)) (legal : action ∈ setup.intendedMenu who info) :
    submitOwnBinding action = action := by
  cases info with
  | none =>
      change action = none at legal
      rw [legal]
      rfl
  | some view =>
      change ProtocolView.intendedMenu who setup.program view action at legal
      cases chosen : action with
      | none => rfl
      | some chosenAction =>
          rw [chosen] at legal
          exact submitOwnBinding_of_intendedAvailable who setup.program view chosenAction legal.2

/-- Repair binding omissions in a forfeiture profile without changing its information views. -/
def submittedSourceProfile
    (profile : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature) :
    Profile (setup.informationModel (CommitmentInterface.forfeiture
      setup.program)).behavioralSignature :=
  fun who => setup.toProtocolBehavioralPolicy (CommitmentInterface.forfeiture setup.program) who
    (BehavioralPolicy.submitBindings setup.program
      (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) profile who))
    (BehavioralPolicy.admitted_forfeiture setup.program _)

/-- Encoding and decoding retain the repaired source policy exactly. -/
theorem decodeBehavioralProfile_submittedSourceProfile
    (profile : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature) :
    setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
        (setup.submittedSourceProfile profile) =
      fun who => (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
        profile who).submitBindings setup.program := by
  funext who
  exact congrArg Subtype.val ((setup.behavioralPolicyEquiv
    (CommitmentInterface.forfeiture setup.program) who).symm_apply_apply
      ⟨(setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
        profile who).submitBindings setup.program, BehavioralPolicy.admitted_forfeiture
          setup.program _⟩)

private theorem submittedSourceProfile_map_val
    (profile : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (who : Player) (info : setup.ProtocolView who) :
    (setup.submittedSourceProfile profile who info).map Subtype.val =
      ((profile who info).map Subtype.val).map submitOwnBinding := by
  let admission := CommitmentInterface.forfeiture setup.program
  let raw := setup.decodeBehavioralProfile admission profile who
  have original : setup.toProtocolBehavioralPolicy admission who raw
      (BehavioralPolicy.admitted_forfeiture setup.program _) = profile who :=
    (setup.behavioralPolicyEquiv admission who).apply_symm_apply (profile who)
  have observed : (profile who info).map Subtype.val =
      info.elim (PMF.pure none) (raw.protocolAction setup.program) := by
    rw [← original, setup.toProtocolBehavioralPolicy_map_val]
  unfold submittedSourceProfile
  rw [setup.toProtocolBehavioralPolicy_map_val, observed]
  cases info with
  | none =>
      change PMF.pure (none : Option (OwnAction Player L)) =
        (PMF.pure none).map submitOwnBinding
      rw [PMF.pure_map]
      rfl
  | some view => exact BehavioralPolicy.protocolAction_submitBindings setup.program raw view

/-- Binding repair preserves every intended information site of an extending profile. -/
theorem submittedSourceProfile_extends
    (intended : Profile setup.intendedModel.behavioralSignature)
    (profile : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended profile) :
    (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended
        (setup.submittedSourceProfile profile) := by
  intro who site
  apply pmf_map_injective Subtype.val_injective
  rw [setup.submittedSourceProfile_map_val]
  have original := agrees who site
  rw [original]
  simp only [PMF.map_comp]
  apply map_congr_on_support
  intro choice _supported
  change submitOwnBinding choice.1 = choice.1
  exact setup.submitOwnBinding_of_intendedMenu who site.1 choice.1 choice.2

/-- The repaired extension submits at every abstract active binding view. -/
theorem submittedSourceProfile_submits
    (profile : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature) (who : Player) :
    SubmitsBindings setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) (setup.submittedSourceProfile profile) who) :=
        by
  rw [setup.decodeBehavioralProfile_submittedSourceProfile]
  exact submitsBindings_submitBindings setup.program _

/-- Binding repair leaves an owner's disclosure discipline intact. -/
theorem submittedSourceProfile_disclosing
    (profile : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature) (who : Player)
    (disclosing : Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) profile who)) :
    Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) (setup.submittedSourceProfile profile) who) :=
        by
  rw [setup.decodeBehavioralProfile_submittedSourceProfile]
  exact Disclosing.submitBindings setup.program _ disclosing

private theorem forceOwnReveal_of_intendedMenu (who : Player) (info : setup.ProtocolView who)
    (action : Option (OwnAction Player L)) (legal : action ∈ setup.intendedMenu who info) :
    forceOwnReveal action = action := by
  cases info with
  | none =>
      change action = none at legal
      rw [legal]
      rfl
  | some view =>
      change ProtocolView.intendedMenu who setup.program view action at legal
      cases chosen : action with
      | none => rfl
      | some chosenAction =>
          rw [chosen] at legal
          exact forceOwnReveal_of_intendedAvailable who setup.program view chosenAction legal.2

/-- Force disclosure throughout a forfeiture-admitted protocol profile. -/
def disclosingSourceProfile
    (profile : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature) :
    Profile (setup.informationModel (CommitmentInterface.forfeiture
      setup.program)).behavioralSignature :=
  fun who => setup.toProtocolBehavioralPolicy (CommitmentInterface.forfeiture setup.program) who
    (BehavioralPolicy.forceDisclose setup.program
      (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program) profile who))
    (BehavioralPolicy.admitted_forfeiture setup.program _)

/-- Encoding and decoding retain the forced source policy exactly. -/
theorem decodeBehavioralProfile_disclosingSourceProfile
    (profile : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature) :
    setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
        (setup.disclosingSourceProfile profile) =
      fun who => (setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
        profile who).forceDisclose setup.program := by
  funext who
  exact congrArg Subtype.val ((setup.behavioralPolicyEquiv
    (CommitmentInterface.forfeiture setup.program) who).symm_apply_apply
      ⟨(setup.decodeBehavioralProfile (CommitmentInterface.forfeiture setup.program)
        profile who).forceDisclose setup.program, BehavioralPolicy.admitted_forfeiture
          setup.program _⟩)

private theorem disclosingSourceProfile_map_val
    (profile : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (who : Player) (info : setup.ProtocolView who) :
    (setup.disclosingSourceProfile profile who info).map Subtype.val =
      ((profile who info).map Subtype.val).map forceOwnReveal := by
  let admission := CommitmentInterface.forfeiture setup.program
  let raw := setup.decodeBehavioralProfile admission profile who
  have original : setup.toProtocolBehavioralPolicy admission who raw
      (BehavioralPolicy.admitted_forfeiture setup.program _) = profile who :=
    (setup.behavioralPolicyEquiv admission who).apply_symm_apply (profile who)
  have observed : (profile who info).map Subtype.val =
      info.elim (PMF.pure none) (raw.protocolAction setup.program) := by
    rw [← original, setup.toProtocolBehavioralPolicy_map_val]
  unfold disclosingSourceProfile
  rw [setup.toProtocolBehavioralPolicy_map_val, observed]
  cases info with
  | none =>
      change PMF.pure (none : Option (OwnAction Player L)) =
        (PMF.pure none).map forceOwnReveal
      rw [PMF.pure_map]
      rfl
  | some view => exact BehavioralPolicy.protocolAction_forceDisclose setup.program raw view

/-- Forcing reveal flags preserves every intended information site. -/
theorem disclosingSourceProfile_extends
    (intended : Profile setup.intendedModel.behavioralSignature)
    (profile : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature)
    (agrees : (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended profile) :
    (setup.intendedRestriction
      (CommitmentInterface.forfeiture setup.program)).ExtendsProfile intended
        (setup.disclosingSourceProfile profile) := by
  intro who site
  apply pmf_map_injective Subtype.val_injective
  rw [setup.disclosingSourceProfile_map_val]
  have original := agrees who site
  rw [original]
  simp only [PMF.map_comp]
  apply map_congr_on_support
  intro choice _supported
  change forceOwnReveal choice.1 = choice.1
  exact setup.forceOwnReveal_of_intendedMenu who site.1 choice.1 choice.2

/-- The forced extension discloses at every abstract active reveal. -/
theorem disclosingSourceProfile_disclosing
    (profile : Profile (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).behavioralSignature) (who : Player) :
    Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.forfeiture setup.program) (setup.disclosingSourceProfile profile) who) :=
  by
  rw [setup.decodeBehavioralProfile_disclosingSourceProfile]
  exact disclosing_forceDisclose setup.program _

end Setup

end Vegas.SourceProgram
