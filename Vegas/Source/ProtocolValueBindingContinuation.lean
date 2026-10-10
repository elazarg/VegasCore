/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ValueBindingContinuation
import Vegas.Source.InitialState
import Vegas.Source.SetupProtocolBehavioral
import GameTheory.Protocol.BehavioralAssessment

/-! # Value-binding mixtures at an actual source observation cursor

Only the unexecuted suffix is translated. Existing private bindings, deferred
guards, publications and original action recalls remain the continuation's data.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- One value-binding mixture serves every listed hidden state at the same
actual source observation cursor; it changes only the remaining policy suffix. -/
theorem exists_valueBinding_protocol_continuation_mixture (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → program.FiniteBindingTypes →
    (profile : BehavioralProfile program) → ValueBinding program (profile who) →
    (replacement : BehavioralPolicy who program) → (view : ProtocolView who program) →
    (states : List (ProtocolState program)) →
    (∀ state ∈ states, ProtocolState.observe who program state = view) →
    ∃ mixture : PMF (ValueBindingPolicy who program), mixture.support.Finite ∧
      ∀ state ∈ states,
      (ProtocolState.continuationLaw program (Function.update profile who replacement) state).map
        (publicOutcome program) =
      mixture.bind fun alternative =>
        (ProtocolState.continuationLaw program
          (Function.update profile who alternative.1) state).map
          (publicOutcome program)
  | _, _, .ret _, _, profile, values, _, _, _, _ => by
      refine ⟨PMF.pure ⟨profile who, values⟩, by simp, ?_⟩
      intro state _
      simp only [ProtocolState.continuationLaw, PMF.pure_bind]
  | _, _, .sample name fresh chance next, finite, profile, values,
      replacement, view, states, observed => by
      cases view with
      | inl view =>
          let configs := states.filterMap (fun state => state.elim some (fun _ => none))
          obtain ⟨mixture, mixtureFinite, law⟩ := exists_valueBinding_continuation_mixture
            (.sample name fresh chance next) finite profile replacement configs
          refine ⟨mixture, mixtureFinite, ?_⟩
          intro state member
          cases state with
          | inl config =>
              exact law config (List.mem_filterMap.mpr ⟨.inl config, member, rfl⟩)
          | inr state =>
              have same := observed (.inr state) member
              cases same
      | inr view =>
          let later := states.filterMap (fun state => state.elim (fun _ => none) some)
          have observedLater : ∀ state ∈ later, ProtocolState.observe who next state = view := by
            intro state member
            obtain ⟨original, originalMember, selected⟩ := List.mem_filterMap.mp member
            cases original with
            | inl config => cases selected
            | inr original =>
                cases Option.some.inj selected
                exact Sum.inr.inj (observed (.inr state) originalMember)
          obtain ⟨mixture, mixtureFinite, law⟩ :=
            exists_valueBinding_protocol_continuation_mixture who next finite
              (profile) values replacement view later observedLater
          refine ⟨mixture, mixtureFinite, ?_⟩
          intro state member
          cases state with
          | inl config =>
              have same := observed (.inl config) member
              cases same
          | inr state => exact law state (List.mem_filterMap.mpr ⟨.inr state, member, rfl⟩)
  | _, _, .commit name owner fresh guard next, finite, profile, values,
      replacement, view, states, observed => by
      cases view with
      | inl view =>
          let configs := states.filterMap (fun state => state.elim some (fun _ => none))
          obtain ⟨mixture, mixtureFinite, law⟩ := exists_valueBinding_continuation_mixture
            (.commit name owner fresh guard next) finite profile replacement configs
          refine ⟨mixture, mixtureFinite, ?_⟩
          intro state member
          cases state with
          | inl config =>
              exact law config (List.mem_filterMap.mpr ⟨.inl config, member, rfl⟩)
          | inr state =>
              have same := observed (.inr state) member
              cases same
      | inr view =>
          let later := states.filterMap (fun state => state.elim (fun _ => none) some)
          have observedLater : ∀ state ∈ later, ProtocolState.observe who next state = view := by
            intro state member
            obtain ⟨original, originalMember, selected⟩ := List.mem_filterMap.mp member
            cases original with
            | inl config => cases selected
            | inr original =>
                cases Option.some.inj selected
                exact Sum.inr.inj (observed (.inr state) originalMember)
          obtain ⟨mixture, mixtureFinite, law⟩ :=
            exists_valueBinding_protocol_continuation_mixture who next finite.2
              (afterCommit profile) values.2 replacement.2 view later observedLater
          let lift (alternative : ValueBindingPolicy who next) :
              ValueBindingPolicy who (.commit name owner fresh guard next) :=
            ⟨((profile who).1, alternative.1), ⟨values.1, alternative.2⟩⟩
          refine ⟨mixture.map lift, by rw [PMF.support_map]; exact mixtureFinite.image _, ?_⟩
          intro state member
          cases state with
          | inl config =>
              have same := observed (.inl config) member
              cases same
          | inr state =>
              rw [PMF.bind_map]
              change (ProtocolState.continuationLaw next
                (afterCommit (Function.update profile who replacement)) state).map
                  (publicOutcome next) =
                mixture.bind fun alternative => (ProtocolState.continuationLaw next
                  (afterCommit (Function.update profile who (lift alternative).1)) state).map
                    (publicOutcome next)
              simp only [afterCommit_update, lift]
              exact law state (List.mem_filterMap.mpr ⟨.inr state, member, rfl⟩)
  | _, _, .reveal published owner name fresh selected unresolved next, finite, profile, values,
      replacement, view, states, observed => by
      cases view with
      | inl view =>
          let configs := states.filterMap (fun state => state.elim some (fun _ => none))
          obtain ⟨mixture, mixtureFinite, law⟩ := exists_valueBinding_continuation_mixture
            (.reveal published owner name fresh selected unresolved next) finite
              profile replacement configs
          refine ⟨mixture, mixtureFinite, ?_⟩
          intro state member
          cases state with
          | inl config =>
              exact law config (List.mem_filterMap.mpr ⟨.inl config, member, rfl⟩)
          | inr state =>
              have same := observed (.inr state) member
              cases same
      | inr view =>
          let later := states.filterMap (fun state => state.elim (fun _ => none) some)
          have observedLater : ∀ state ∈ later, ProtocolState.observe who next state = view := by
            intro state member
            obtain ⟨original, originalMember, selected⟩ := List.mem_filterMap.mp member
            cases original with
            | inl config => cases selected
            | inr original =>
                cases Option.some.inj selected
                exact Sum.inr.inj (observed (.inr state) originalMember)
          obtain ⟨mixture, mixtureFinite, law⟩ :=
            exists_valueBinding_protocol_continuation_mixture who next finite
              (afterReveal profile) values replacement.2 view later observedLater
          let lift (alternative : ValueBindingPolicy who next) :
              ValueBindingPolicy who
                (.reveal published owner name fresh selected unresolved next) :=
            ⟨((profile who).1, alternative.1), alternative.2⟩
          refine ⟨mixture.map lift, by rw [PMF.support_map]; exact mixtureFinite.image _, ?_⟩
          intro state member
          cases state with
          | inl config =>
              have same := observed (.inl config) member
              cases same
          | inr state =>
              rw [PMF.bind_map]
              change (ProtocolState.continuationLaw next
                (afterReveal (Function.update profile who replacement)) state).map
                  (publicOutcome next) =
                mixture.bind fun alternative => (ProtocolState.continuationLaw next
                  (afterReveal (Function.update profile who (lift alternative).1)) state).map
                    (publicOutcome next)
              simp only [afterReveal_update, lift]
              exact law state (List.mem_filterMap.mpr ⟨.inr state, member, rfl⟩)


/-- Recover the original environment from an actual residual protocol state. -/
def ProtocolState.initialEnvironment : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → State L Γ
  | _, _, .ret _, config => config.state
  | _, _, .sample _ _ _ next, state => state.elim (fun config => config.state)
      (fun later => fun _ _ member =>
        (ProtocolState.initialEnvironment next later).get (.there member))
  | _, _, .commit _ _ _ _ next, state => state.elim (fun config => config.state)
      (fun later => fun _ _ member =>
        (ProtocolState.initialEnvironment next later).get (.there member))
  | _, _, .reveal _ _ _ _ _ _ next, state => state.elim (fun config => config.state)
      (fun later => fun _ _ member =>
        (ProtocolState.initialEnvironment next later).get (.there member))

/-- The terminal reader recovers the immutable origin at every actual cursor. -/
theorem ProtocolState.initialState_continuation {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (state : ProtocolState program) (terminal : State L program.terminalCtx)
    (supported : terminal ∈ (ProtocolState.continuationLaw program profile state).support) :
    initialState program terminal = ProtocolState.initialEnvironment program state := by
  induction program with
  | ret outputs =>
      simpa [ProtocolState.continuationLaw, ProtocolState.initialEnvironment, initialState]
        using supported
  | sample name fresh chance next ih =>
      cases state with
      | inl config => exact initialState_runFrom _ profile config terminal supported
      | inr state =>
          have same := ih profile state terminal supported
          funext name cell member
          exact congrArg (fun env => env.get (.there member)) same
  | commit name owner fresh guard next ih =>
      cases state with
      | inl config => exact initialState_runFrom _ profile config terminal supported
      | inr state =>
          have same := ih (afterCommit profile) state terminal supported
          funext name cell member
          exact congrArg (fun env => env.get (.there member)) same
  | reveal published owner name fresh selected unresolved next ih =>
      cases state with
      | inl config => exact initialState_runFrom _ profile config terminal supported
      | inr state =>
          have same := ih (afterReveal profile) state terminal supported
          funext name cell member
          exact congrArg (fun env => env.get (.there member)) same

/-- The mixture preserves any initial parameter jointly with public outcomes,
including at off-path cursors with arbitrary finite hidden-state beliefs. -/
theorem exists_valueBinding_protocol_belief_mixture {Parameter : Type}
    {Γ : SourceCtx Player L} {O : Finset VarId} (who : Player)
    (program : SourceProgram Player L Γ O) (finite : program.FiniteBindingTypes)
    (profile : BehavioralProfile program) (values : ValueBinding program (profile who))
    (replacement : BehavioralPolicy who program) (view : ProtocolView who program)
    (belief : PMF (ProtocolState program)) (beliefFinite : belief.support.Finite)
    (observed : ∀ state ∈ belief.support, ProtocolState.observe who program state = view)
    (parameter : State L Γ → Parameter) :
    ∃ mixture : PMF (ValueBindingPolicy who program), mixture.support.Finite ∧
      (belief.bind fun state =>
        (ProtocolState.continuationLaw program (Function.update profile who replacement) state).map
          (fun terminal => (parameter (initialState program terminal),
            publicOutcome program terminal))) =
      mixture.bind fun alternative => belief.bind fun state =>
        (ProtocolState.continuationLaw program
          (Function.update profile who alternative.1) state).map
          (fun terminal => (parameter (initialState program terminal),
            publicOutcome program terminal)) := by
  classical
  obtain ⟨mixture, mixtureFinite, law⟩ := exists_valueBinding_protocol_continuation_mixture who
    program finite profile values replacement view beliefFinite.toFinset.toList
    (fun state member => observed state
      (beliefFinite.mem_toFinset.mp (Finset.mem_toList.mp member)))
  refine ⟨mixture, mixtureFinite, ?_⟩
  have readout (policy : BehavioralPolicy who program) (state : ProtocolState program) :
      (ProtocolState.continuationLaw program (Function.update profile who policy) state).map
        (fun terminal => (parameter (initialState program terminal),
          publicOutcome program terminal)) =
      (ProtocolState.continuationLaw program (Function.update profile who policy) state).map
        (fun terminal => (parameter (ProtocolState.initialEnvironment program state),
          publicOutcome program terminal)) := by
    apply map_congr_on_support _
    intro terminal supported
    rw [ProtocolState.initialState_continuation program _ state terminal supported]
  rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro state supported
  rw [readout]
  have equality := congrArg (PMF.map fun outcome =>
    (parameter (ProtocolState.initialEnvironment program state), outcome))
    (law state (Finset.mem_toList.mpr (beliefFinite.mem_toFinset.mpr supported)))
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind] at equality
  rw [equality]
  apply bind_congr_on_support _
  intro alternative _
  exact (readout alternative.1 state).symm


/-- At an arbitrary finite belief with a common actual focal observation, some
value-binding continuation matches or improves any admitted source deviation. -/
theorem exists_valueBinding_protocol_continuation_ge {Parameter : Type}
    {Γ : SourceCtx Player L} {O : Finset VarId} (who : Player)
    (program : SourceProgram Player L Γ O) (finite : program.FiniteBindingTypes)
    (profile : BehavioralProfile program) (values : ValueBinding program (profile who))
    (replacement : BehavioralPolicy who program) (view : ProtocolView who program)
    (belief : PMF (ProtocolState program)) (beliefFinite : belief.support.Finite)
    (observed : ∀ state ∈ belief.support, ProtocolState.observe who program state = view)
    (parameter : State L Γ → Parameter)
    (utility : Parameter × PublicOutcome program → ℝ) :
    ∃ alternative : ValueBindingPolicy who program,
      expect (belief.bind fun state =>
        (ProtocolState.continuationLaw program (Function.update profile who replacement) state).map
          (fun terminal => (parameter (initialState program terminal),
            publicOutcome program terminal))) utility ≤
      expect (belief.bind fun state =>
        (ProtocolState.continuationLaw program
          (Function.update profile who alternative.1) state).map
          (fun terminal => (parameter (initialState program terminal),
            publicOutcome program terminal))) utility := by
  obtain ⟨mixture, _, law⟩ := exists_valueBinding_protocol_belief_mixture who program finite
    profile values replacement view belief beliefFinite observed parameter
  have lawFinite : (belief.bind fun state =>
      (ProtocolState.continuationLaw program (Function.update profile who replacement) state).map
        (fun terminal => (parameter (initialState program terminal),
          publicOutcome program terminal))).support.Finite := by
    rw [PMF.support_bind]
    exact beliefFinite.biUnion fun state _ => by
      rw [PMF.support_map]
      exact (ProtocolState.continuationLaw_support_finite program _
        (FiniteBindingTypes.profileFiniteSupport program finite _) state).image _
  rw [law] at lawFinite ⊢
  have integrable := payoffIntegrable_of_finite_support _ utility lawFinite
  rw [expect_bind_tower _ _ _ integrable]
  obtain ⟨alternative, _, bound⟩ := exists_expect_le_support mixture (fun alternative =>
    expect (belief.bind fun state =>
      (ProtocolState.continuationLaw program (Function.update profile who alternative.1) state).map
        (fun terminal => (parameter (initialState program terminal),
          publicOutcome program terminal))) utility)
    (payoffIntegrable_bind_conditionalExpectation _ _ _ integrable)
  exact ⟨alternative, bound⟩


namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- Every hidden history at a genuine value-game decision has an actual
source cursor, and all those cursors have the site's full focal observation. -/
theorem exists_values_site_cursor (who : Player)
    (site : (setup.informationModel
      (CommitmentInterface.values setup.program)).InformationSite who) :
    ∃ view : SourceProgram.ProtocolView who setup.program, site.1 = some view ∧
      ∀ history : (setup.informationModel
          (CommitmentInterface.values setup.program)).InformationHistory who site.1,
        ∃ state : SourceProgram.ProtocolState setup.program,
          history.1.state = some state ∧
            SourceProgram.ProtocolState.observe who setup.program state = view := by
  obtain ⟨witness, _, _⟩ := site.2
  have active := GameTheory.Protocol.InformationModel.InformationSite.active
    (setup.informationModel (CommitmentInterface.values setup.program)) site witness
  have observed := (setup.protocol_info (CommitmentInterface.values setup.program)
    who witness.1.trace).symm.trans witness.2
  cases selected : witness.1.state with
  | none =>
      have impossible : False := by
        change (setup.protocolObserve who witness.1.state).elim False
          (fun view => ProtocolView.actor who setup.program view = some who) at active
        simp only [selected, protocolObserve, Option.map_none, Option.elim_none] at active
      exact impossible.elim
  | some state =>
      refine ⟨SourceProgram.ProtocolState.observe who setup.program state, ?_, ?_⟩
      · simpa only [selected, protocolObserve, Option.map_some] using observed.symm
      · intro history
        have same := (setup.protocol_info (CommitmentInterface.values setup.program)
          who history.1.trace).symm.trans history.2
        have same := same.trans observed.symm
        cases current : history.1.state with
        | none =>
            simp only [current, selected, protocolObserve, Option.map_none, Option.map_some] at same
            cases same
        | some later =>
            refine ⟨later, rfl, ?_⟩
            exact Option.some.inj (by
              simpa only [current, selected, protocolObserve, Option.map_none, Option.map_some]
                using same)

/-- The residual source mixture is uniform over an actual decision site's
finite hidden-history belief, preserving initial parameters and all public results. -/
theorem exists_values_site_belief_mixture {Parameter : Type}
    (who : Player) (finite : setup.program.FiniteBindingTypes)
    (profile : BehavioralProfile setup.program)
    (values : ValueBinding setup.program (profile who))
    (replacement : BehavioralPolicy who setup.program)
    (site : (setup.informationModel
      (CommitmentInterface.values setup.program)).InformationSite who)
    (belief : PMF ((setup.informationModel
      (CommitmentInterface.values setup.program)).InformationHistory who site.1))
    (beliefFinite : belief.support.Finite)
    (parameter : State L setup.context → Parameter) :
    ∃ mixture : PMF (ValueBindingPolicy who setup.program), mixture.support.Finite ∧
      (belief.bind fun history =>
        (setup.continuationLaw (Function.update profile who replacement) history.1.state).map
          (setup.parameterOutcome parameter)) =
      mixture.bind fun alternative => belief.bind fun history =>
        (setup.continuationLaw (Function.update profile who alternative.1) history.1.state).map
          (setup.parameterOutcome parameter) := by
  classical
  obtain ⟨view, _, represented⟩ := setup.exists_values_site_cursor who site
  let cursor history := (represented history).choose
  have selected history : history.1.state = some (cursor history) :=
    (represented history).choose_spec.1
  have observed : ∀ state ∈ (belief.map cursor).support,
      SourceProgram.ProtocolState.observe who setup.program state = view := by
    intro state supported
    rw [PMF.support_map] at supported
    obtain ⟨history, _, rfl⟩ := supported
    exact (represented history).choose_spec.2
  obtain ⟨mixture, mixtureFinite, law⟩ := exists_valueBinding_protocol_belief_mixture who
    setup.program finite profile values replacement view (belief.map cursor)
    (by rw [PMF.support_map]; exact beliefFinite.image _) observed parameter
  refine ⟨mixture, mixtureFinite, ?_⟩
  simp only [PMF.bind_map, Function.comp_def] at law
  have convertLaw (policy : BehavioralPolicy who setup.program) :
      (belief.bind fun history =>
        (setup.continuationLaw (Function.update profile who policy) history.1.state).map
          (setup.parameterOutcome parameter)) =
      belief.bind fun history =>
        (SourceProgram.ProtocolState.continuationLaw setup.program
          (Function.update profile who policy) (cursor history)).map
            (fun terminal => (parameter (initialState setup.program terminal),
              publicOutcome setup.program terminal)) := by
    apply bind_congr_on_support _
    intro history _
    rw [selected history]
    rfl
  rw [convertLaw]
  erw [law]
  apply bind_congr_on_support _
  intro alternative _
  exact (convertLaw alternative.1).symm

/-- One legal value-binding policy dominates the larger source deviation
under an arbitrary finite belief at a retained decision, for any source utility. -/
theorem exists_values_site_continuation_ge {Parameter : Type}
    (who : Player) (finite : setup.program.FiniteBindingTypes)
    (profile : BehavioralProfile setup.program)
    (values : ValueBinding setup.program (profile who))
    (replacement : BehavioralPolicy who setup.program)
    (site : (setup.informationModel
      (CommitmentInterface.values setup.program)).InformationSite who)
    (belief : PMF ((setup.informationModel
      (CommitmentInterface.values setup.program)).InformationHistory who site.1))
    (beliefFinite : belief.support.Finite)
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → ℝ) :
    ∃ alternative : ValueBindingPolicy who setup.program,
      expect (belief.bind fun history =>
        (setup.continuationLaw (Function.update profile who replacement) history.1.state).map
          (setup.parameterOutcome parameter)) utility ≤
      expect (belief.bind fun history =>
        (setup.continuationLaw (Function.update profile who alternative.1) history.1.state).map
          (setup.parameterOutcome parameter)) utility := by
  obtain ⟨mixture, _, law⟩ := setup.exists_values_site_belief_mixture who finite profile values
    replacement site belief beliefFinite parameter
  have lawFinite : (belief.bind fun history =>
      (setup.continuationLaw (Function.update profile who replacement) history.1.state).map
        (setup.parameterOutcome parameter)).support.Finite := by
    obtain ⟨_, _, represented⟩ := setup.exists_values_site_cursor who site
    rw [PMF.support_bind]
    exact beliefFinite.biUnion fun history _ => by
      rw [PMF.support_map]
      obtain ⟨state, selected, _⟩ := represented history
      rw [selected]
      exact (SourceProgram.ProtocolState.continuationLaw_support_finite setup.program _
        (FiniteBindingTypes.profileFiniteSupport setup.program finite _) state).image _
  rw [law] at lawFinite ⊢
  have integrable := payoffIntegrable_of_finite_support _ utility lawFinite
  rw [expect_bind_tower _ _ _ integrable]
  obtain ⟨alternative, _, bound⟩ := exists_expect_le_support mixture (fun alternative =>
    expect (belief.bind fun history =>
      (setup.continuationLaw (Function.update profile who alternative.1) history.1.state).map
        (setup.parameterOutcome parameter)) utility)
    (payoffIntegrable_bind_conditionalExpectation _ _ _ integrable)
  exact ⟨alternative, bound⟩

end Setup

end Vegas.SourceProgram
