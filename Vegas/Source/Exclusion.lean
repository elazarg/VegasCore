/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.FailedBindingDeviation
import Vegas.Source.DefaultControl
import Vegas.Source.PublicObservation

/-! # Public exclusion and available failure choices

Exclusion is membership in the authoritative public default set. Hidden
unusable bindings are handled by failed-binding debt and do not exclude an
owner before a public omission or failed publication. Every active decision
admits a public failure choice, independently of binding admission.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- An explicit public failure choice: omission of a binding or withholding a reveal. -/
def OwnAction.IsFailure : OwnAction Player L → Prop
  | .commit _ _ _ choice => choice = none
  | .reveal _ _ disclose => disclose = false

namespace ProtocolState

/-- Exclusion is read from the sole public default record at the current position. -/
def Excluded (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program) : Prop :=
  who ∈ defaulted program state

/-- A player's view determines what it observes of the cells of the program
point's entry context. -/
theorem sourceObserve_base_eq_of_observe_eq (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (left right : ProtocolState program) →
    observe who program left = observe who program right →
      sourceObserve who (base program left) = sourceObserve who (base program right)
  | _, _, .ret _, _, _, same => congrArg DecisionView.observation same
  | _, _, .sample _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact congrArg DecisionView.observation (Sum.inl.inj same)
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              exact sourceObserve_tail_eq
                (sourceObserve_base_eq_of_observe_eq who next first second (Sum.inr.inj same))
  | _, _, .commit _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact congrArg DecisionView.observation (Sum.inl.inj same)
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              exact sourceObserve_tail_eq
                (sourceObserve_base_eq_of_observe_eq who next first second (Sum.inr.inj same))
  | _, _, .reveal _ _ _ _ _ _ next, left, right, same => by
      cases left with
      | inl first =>
          cases right with
          | inl second => exact congrArg DecisionView.observation (Sum.inl.inj same)
          | inr _ => cases same
      | inr first =>
          cases right with
          | inl _ => cases same
          | inr second =>
              exact sourceObserve_tail_eq
                (sourceObserve_base_eq_of_observe_eq who next first second (Sum.inr.inj same))

/-- Every player's view determines the public exclusion of every player. -/
theorem excluded_iff_of_observe_eq (who observer : Player) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (left right : ProtocolState program)
    (same : observe observer program left = observe observer program right) :
    Excluded who program left ↔ Excluded who program right := by
  have status := congrArg (ProtocolView.defaulted observer program) same
  rw [defaulted_observe, defaulted_observe] at status
  simp only [Excluded, status]

/-- No position of intended play has a publicly defaulted player. -/
theorem not_excluded_of_intended (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    Intended program state → ¬ Excluded who program state
  | _, _, .ret _, _, intended => intended.not_defaulted who
  | _, _, .sample _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact intended.1.not_defaulted who
      | inr rest => exact not_excluded_of_intended who next rest intended
  | _, _, .commit _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact intended.1.not_defaulted who
      | inr rest => exact not_excluded_of_intended who next rest intended
  | _, _, .reveal _ _ _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact intended.1.not_defaulted who
      | inr rest => exact not_excluded_of_intended who next rest intended.2


/-- Every failed publication created by a completed instruction has its owner
in the current authoritative public default set. Setup publication cells are
not generated instructions and impose no initialization premise here. -/
def PublicationsDefaulted : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Prop
  | _, _, .ret _ => fun _ => True
  | _, _, .sample _ _ _ next => Sum.elim (fun _ => True) (PublicationsDefaulted next)
  | _, _, .commit _ _ _ _ next => Sum.elim (fun _ => True) (PublicationsDefaulted next)
  | _, _, .reveal _ owner _ _ _ _ next => Sum.elim (fun _ => True)
      (fun rest => ((base next rest).get .here = .failure → owner ∈ defaulted next rest) ∧
        PublicationsDefaulted next rest)

/-- No generated instruction has completed at entry, for any incoming configuration. -/
theorem publicationsDefaulted_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    PublicationsDefaulted program (entry program config) := by
  cases program <;> trivial

/-- Actual publication failure and absorbing default preserve the provenance invariant. -/
theorem publicationsDefaulted_step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (before after : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) →
    PublicationsDefaulted program before → after ∈ (step program before joint).support →
    PublicationsDefaulted program after
  | _, _, .ret _, _, _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, before, after, joint, valid, reached => by
      cases before with
      | inl config =>
          obtain ⟨value, _, rfl⟩ := PMF.support_map .. ▸ reached
          exact publicationsDefaulted_entry next _
      | inr rest =>
          obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
          exact publicationsDefaulted_step next rest target joint valid supported
  | _, _, .commit _ _ _ _ next, before, after, joint, valid, reached => by
      cases before with
      | inl config =>
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst after
          exact publicationsDefaulted_entry next _
      | inr rest =>
          obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
          exact publicationsDefaulted_step next rest target joint valid supported
  | _, _, .reveal published owner name _ selected _ next,
      before, after, joint, valid, reached => by
      cases before with
      | inl config =>
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst after
          refine ⟨?_, publicationsDefaulted_entry next _⟩
          rw [base_entry, defaulted_entry]
          intro failed
          rw [revealSuccessor_defaulted_of_failure published selected config _ failed]
          exact Finset.mem_insert_self owner _
      | inr rest =>
          obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
          refine ⟨?_, publicationsDefaulted_step next rest target joint valid.2 supported⟩
          intro failed
          have earlier : (base next rest).get .here = .failure := by
            rw [← base_step next rest joint target supported]
            exact failed
          exact defaulted_step next rest target joint supported (valid.1 earlier)

/-- All generated failed publications have public provenance on an actual source trace. -/
theorem publicationsDefaulted_trace {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) :
    ∀ {state} (_ : (executionProtocol program admission initial).Trace state),
      PublicationsDefaulted program state
  | _, .start => publicationsDefaulted_entry program initial
  | _, .extend (source := before) (target := after) prior joint _ reached =>
      publicationsDefaulted_step program before after joint
        (publicationsDefaulted_trace program admission initial prior) reached

/-- The complete terminal configuration retains the current public defaults. -/
theorem defaulted_eq_of_readout : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    {final : Config Player L program.terminalCtx} → readout program state = some final →
    defaulted program state = final.defaulted
  | _, _, .ret _, _, _, read => by cases read; rfl
  | _, _, .sample _ _ _ next, state, _, read => by
      cases state with
      | inl _ => cases read
      | inr rest => exact defaulted_eq_of_readout next rest read
  | _, _, .commit _ _ _ _ next, state, _, read => by
      cases state with
      | inl _ => cases read
      | inr rest => exact defaulted_eq_of_readout next rest read
  | _, _, .reveal _ _ _ _ _ _ next, state, _, read => by
      cases state with
      | inl _ => cases read
      | inr rest => exact defaulted_eq_of_readout next rest read

/-- An owed failure at a terminal point is a generated failed publication;
unresolved guard or binding debt cannot remain at the empty terminal obligation set. -/
theorem defaulted_of_owesFailure_of_publicationsDefaulted (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    PublicationsDefaulted program state → OwesFailure who program state →
    {final : Config Player L program.terminalCtx} → readout program state = some final →
    who ∈ final.defaulted
  | _, _, .ret _, _, _, owed, _, _ =>
      owed.elim (fun debt => (Config.Indebted.not_resolved debt).elim)
        (fun debt => (Config.FailedBinding.not_resolved debt).elim)
  | _, _, .sample _ _ _ next, state, valid, owed, _, read => by
      cases state with
      | inl _ => cases read
      | inr rest =>
          exact defaulted_of_owesFailure_of_publicationsDefaulted who next rest valid owed read
  | _, _, .commit _ _ _ _ next, state, valid, owed, _, read => by
      cases state with
      | inl _ => cases read
      | inr rest =>
          exact defaulted_of_owesFailure_of_publicationsDefaulted who next rest valid owed read
  | _, _, .reveal _ owner _ _ _ _ next, state, valid, owed, final, read => by
      cases state with
      | inl _ => cases read
      | inr rest =>
          have published : (owner = who ∧ (base next rest).get .here = .failure) →
              who ∈ final.defaulted := by
            rintro ⟨rfl, failed⟩
            rw [← defaulted_eq_of_readout next rest read]
            exact valid.1 failed
          rcases owed with (failed | debt) | (failed | debt)
          · exact published failed
          · exact defaulted_of_owesFailure_of_publicationsDefaulted who next rest valid.2
              (Or.inl debt) read
          · exact published failed
          · exact defaulted_of_owesFailure_of_publicationsDefaulted who next rest valid.2
              (Or.inr debt) read

/-- A terminal continuation carrying an owed failure defaults its owner on every
actual source trace, independently of admission and of all strategic choices. -/
theorem defaulted_of_owesFailure_trace {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) {state : ProtocolState program}
    (trace : (executionProtocol program admission initial).Trace state) (who : Player)
    (owed : OwesFailure who program state) {final : Config Player L program.terminalCtx}
    (read : readout program state = some final) : who ∈ final.defaulted :=
  defaulted_of_owesFailure_of_publicationsDefaulted who program state
    (publicationsDefaulted_trace program admission initial trace) owed read

end ProtocolState

namespace ProtocolView

/-- A publicly defaulted player never becomes the active actor again. -/
theorem actor_ne_of_defaulted (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (view : ProtocolView who program) →
    who ∈ defaulted who program view → actor who program view ≠ some who
  | _, _, .ret _, _, _ => by simp [actor]
  | _, _, .sample _ _ _ next, view, inactive => by
      cases view with
      | inl _ => simp [actor]
      | inr later => exact actor_ne_of_defaulted who next later inactive
  | _, _, .commit _ owner _ _ next, view, inactive => by
      cases view with
      | inl current =>
          by_cases own : owner = who
          · subst owner
            change who ∈ current.defaulted at inactive
            simp [actor, inactive]
          · simp [actor, own]
      | inr later => exact actor_ne_of_defaulted who next later inactive
  | _, _, .reveal _ owner _ _ _ _ next, view, inactive => by
      cases view with
      | inl current =>
          by_cases own : owner = who
          · subst owner
            change who ∈ current.defaulted at inactive
            simp [actor, inactive]
          · simp [actor, own]
      | inr later => exact actor_ne_of_defaulted who next later inactive

/-- Every legal choice of a publicly defaulted player is outer `none`, so no
strategic callback is needed at any later owned instruction. -/
theorem menu_iff_none_of_defaulted (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (view : ProtocolView who program) (inactive : who ∈ defaulted who program view)
    (choice : Option (OwnAction Player L)) :
    menu who program admission view choice ↔ choice = none := by
  have noActor := actor_ne_of_defaulted who program view inactive
  cases choice with
  | none => exact ⟨fun _ => rfl, fun _ => noActor⟩
  | some action =>
      constructor
      · rintro ⟨active, _⟩
        exact (noActor active).elim
      · intro impossible
        cases impossible

/-- Every view offers an admitted omission, withholding, or absence of an
active choice, independently of the binding admission interface. -/
theorem exists_failure_menu (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (view : ProtocolView who program) →
      ∃ choice, menu who program admission view choice ∧
        ∀ action, choice = some action → action.IsFailure
  | _, _, .ret _, _, _ =>
      ⟨none, by simp [menu, actor], fun _ chosen => by cases chosen⟩
  | _, _, .sample _ _ _ next, admission, view => by
      cases view with
      | inl _ => exact ⟨none, by simp [menu, actor], fun _ chosen => by cases chosen⟩
      | inr later => exact exists_failure_menu who next admission later
  | _, _, .commit (payload := payload) name owner _ _ next, admission, view => by
      cases view with
      | inl current =>
          by_cases inactive : owner ∈ current.defaulted
          · exact ⟨none, by simp [menu, actor, inactive], fun _ chosen => by cases chosen⟩
          · by_cases own : owner = who
            · subst owner
              refine ⟨some (.commit who name payload none), ?_, ?_⟩
              · simp [menu, actor, available, inactive, CommitmentAdmission.Admits]
              · rintro _ ⟨⟩
                rfl
            · exact ⟨none, by simp [menu, actor, inactive, own],
                fun _ chosen => by cases chosen⟩
      | inr later =>
          exact exists_failure_menu who next (fun site => admission (some site)) later
  | _, _, .reveal _ owner name _ _ _ next, admission, view => by
      cases view with
      | inl current =>
          by_cases inactive : owner ∈ current.defaulted
          · exact ⟨none, by simp [menu, actor, inactive], fun _ chosen => by cases chosen⟩
          · by_cases own : owner = who
            · subst owner
              refine ⟨some (.reveal who name false), ?_, ?_⟩
              · simp [menu, actor, available, inactive]
              · rintro _ ⟨⟩
                rfl
            · exact ⟨none, by simp [menu, actor, inactive, own],
                fun _ chosen => by cases chosen⟩
      | inr later => exact exists_failure_menu who next admission later

end ProtocolView


namespace Setup

/-- Every initialized source history records the public default of every failed
publication generated by the program; initial hidden cells need no such premise. -/
theorem publicationsDefaulted_trace (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) :
    ∀ {state} (_ : (setup.executionProtocol admission).Trace state),
      state.elim True (ProtocolState.PublicationsDefaulted setup.program)
  | _, .start => trivial
  | _, .extend (source := before) (target := after) prior joint _ reached => by
      have earlier := setup.publicationsDefaulted_trace admission prior
      cases before with
      | none =>
          change after ∈ (setup.initialLaw.map fun initial =>
            some (ProtocolState.entry setup.program (Config.initial initial))).support at reached
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ reached
          exact ProtocolState.publicationsDefaulted_entry setup.program _
      | some state =>
          change after ∈ ((ProtocolState.step setup.program state joint).map some).support
            at reached
          obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
          exact ProtocolState.publicationsDefaulted_step setup.program state target joint
            earlier supported

/-- Actual initialized terminal histories turn any owed failure into public
default, including hidden unusable bindings that only fail at their later reveal. -/
theorem defaulted_of_owesFailure_trace (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program)
    {state : SourceProgram.ProtocolState setup.program}
    (trace : (setup.executionProtocol admission).Trace (some state)) (who : Player)
    (owed : ProtocolState.OwesFailure who setup.program state)
    {final : Config Player L setup.program.terminalCtx}
    (read : ProtocolState.readout setup.program state = some final) : who ∈ final.defaulted :=
  ProtocolState.defaulted_of_owesFailure_of_publicationsDefaulted who setup.program state
    (setup.publicationsDefaulted_trace admission trace) owed read

end Setup

end Vegas.SourceProgram
