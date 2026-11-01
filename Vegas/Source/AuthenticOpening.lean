/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.DisclosureOpening
import Vegas.Source.IntendedPlay
import Vegas.Source.ProtocolBehavioralPolicy

/-! # Authentic source openings

An authentic opening retains every binding kernel and chooses each opening
whose guarded publication succeeds. At intended points carrying the program's
static metadata it agrees with an always-disclosing policy. The static registry
and revelation invariant follows the source syntax.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

private theorem admitted_forceDisclose {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : BehavioralPolicy who program) → policy.Admitted program admission →
    (policy.forceDisclose program).Admitted program admission
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, policy, permitted =>
      admitted_forceDisclose next admission policy permitted
  | _, _, .commit _ _ _ _ next, _, policy, permitted =>
      ⟨permitted.1, admitted_forceDisclose next _ policy.2 permitted.2⟩
  | _, _, .reveal _ _ _ _ _ _ next, admission, policy, permitted =>
      admitted_forceDisclose next admission policy.2 permitted

/-- Authentic openings retain the original binding admission guarantee. -/
theorem BehavioralPolicy.admitted_authenticOpening {who : Player}
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (policy : BehavioralPolicy who program) (permitted : policy.Admitted program admission) :
    (policy.authenticOpening program).Admitted program admission :=
  (normalizeDisclosures_admitted_iff program admission (policy.forceDisclose program)).mpr
    (admitted_forceDisclose program admission policy permitted)

namespace ProtocolState

/-- A source point carries, at its program point, the registry and
publication status the program carries there from `registry` and
`revelations`. -/
def StaticAt : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Registry Γ → Revelations Γ →
    ProtocolState program → Prop
  | _, _, .ret _, registry, revelations => fun config =>
      config.registry = registry ∧ @config.revelations = @revelations
  | _, _, .sample _ _ _ next, registry, revelations =>
      Sum.elim (fun config => config.registry = registry ∧ @config.revelations = @revelations)
        (StaticAt next registry.weaken revelations.weaken)
  | _, _, .commit (payload := payload) name owner _ guard next, registry, revelations =>
      Sum.elim (fun config => config.registry = registry ∧ @config.revelations = @revelations)
        (StaticAt next
          ({ owner := owner, subject := name, payload := payload, source := .here,
              guard := guard.weaken } :: registry.weaken) revelations.weaken)
  | _, _, .reveal published _ _ _ selected _ next, registry, revelations =>
      Sum.elim (fun config => config.registry = registry ∧ @config.revelations = @revelations)
        (StaticAt next registry.weaken (revelations.reveal (published := published) selected))

theorem staticAt_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) {registry : Registry Γ}
    {revelations : Revelations Γ} (config : Config Player L Γ)
    (registryEq : config.registry = registry) (revelationsEq : @config.revelations = @revelations) :
    StaticAt program registry revelations (entry program config) := by
  cases program <;> exact ⟨registryEq, revelationsEq⟩

/-- **The program carries the registry and publication status.** Every source
step keeps a point carrying the program's registry and publication status. -/
theorem staticAt_step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (registry : Registry Γ) →
    (revelations : Revelations Γ) → (state : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → (target : ProtocolState program) →
    StaticAt program registry revelations state → target ∈ (step program state joint).support →
    StaticAt program registry revelations target
  | _, _, .ret _, _, _, _, _, _, holds, reached => by
      rw [step, PMF.mem_support_pure_iff] at reached
      rw [reached]
      exact holds
  | _, _, .sample _ _ _ next, registry, revelations, state, joint, target, holds, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          obtain ⟨registryEq, revelationsEq⟩ := holds
          exact staticAt_entry next _ (by simp [sampleSuccessor, registryEq])
            (by simp [sampleSuccessor, revelationsEq])
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact staticAt_step next _ _ rest joint after holds supported
  | _, _, .commit _ _ _ _ next, registry, revelations, state, joint, target, holds, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          obtain ⟨registryEq, revelationsEq⟩ := holds
          exact staticAt_entry next _ (by simp [commitSuccessor, registryEq])
            (by simp [commitSuccessor, revelationsEq])
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact staticAt_step next _ _ rest joint after holds supported
  | _, _, .reveal _ _ _ _ _ _ next, registry, revelations, state, joint, target, holds,
      reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          obtain ⟨registryEq, revelationsEq⟩ := holds
          exact staticAt_entry next _ (by simp [revealSuccessor, registryEq])
            (by simp [revealSuccessor, revelationsEq])
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact staticAt_step next _ _ rest joint after holds supported

end ProtocolState

omit [IExpr.ResultTypes L] in
/-- Every binding is authentic at an intended source configuration. -/
theorem Config.Intended.binding_isSuccess {Γ : SourceCtx Player L}
    {unresolved : Finset VarId} {config : Config Player L Γ}
    (intended : config.Intended unresolved) {owner : Player} {payload : L.Ty} {name : VarId}
    (source : HasVar Γ name (.commitment owner payload)) :
    (config.state.get source).isSuccess = true := by
  obtain ⟨value, bound⟩ := intended.bound source
  rw [bound]
  rfl

private theorem protocolAction_openingFrom {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (registry : Registry Γ) →
    (revelations : Revelations Γ) → (policy : BehavioralPolicy who program) →
    Disclosing program policy → (state : ProtocolState program) →
    ProtocolState.StaticAt program registry revelations state →
    ProtocolState.Intended program state →
    BehavioralPolicy.protocolAction program
        ((policy.forceDisclose program).normalizeDisclosuresFrom program registry revelations)
          (ProtocolState.observe who program state) =
      policy.protocolAction program (ProtocolState.observe who program state)
  | _, _, .ret _, _, _, _, _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, _, _, policy, disclosing, state, static, intended => by
      cases state with
      | inl _ => rfl
      | inr rest =>
          exact protocolAction_openingFrom next _ _ policy disclosing rest static intended
  | _, _, .commit _ _ _ _ next, _, _, policy, disclosing, state, static, intended => by
      cases state with
      | inl _ => rfl
      | inr rest =>
          exact protocolAction_openingFrom next _ _ policy.2 disclosing rest static intended
  | _, _, .reveal published owner name _ selected _ next, registry, revelations,
      policy, disclosing, state, static, intended => by
      cases state with
      | inl config =>
          change config.registry = registry ∧ @config.revelations = @revelations at static
          rcases static with ⟨rfl, rfl⟩
          have effective : effectiveDisclosureView published selected config.registry
              config.revelations (config.view owner) true = true := by
            rw [effectiveDisclosureView_observe]
            unfold effectiveDisclosure disclosureResult
            rw [intended.1.reveal_state selected]
            obtain ⟨value, bound⟩ := intended.1.bound selected
            simp only [Env.cons_get_here, Config.bindingOf, bound]
          simp only [BehavioralPolicy.forceDisclose, BehavioralPolicy.normalizeDisclosuresFrom,
            BehavioralPolicy.protocolAction,
            ProtocolState.observe, Sum.elim_inl, PMF.pure_map]
          by_cases own : owner = who
          · subst who
            have active : owner ∉ (config.view owner).defaulted := intended.1.not_defaulted owner
            rw [dite_eq_left (show owner = owner from rfl),
              dite_eq_left (show owner = owner from rfl), dite_eq_left active, dite_eq_left active,
              effective, eq_pure_true_of_false_not_mem
                (disclosing.1 rfl (config.view owner) active), PMF.pure_map]
          · rw [dite_eq_right own, dite_eq_right own]
      | inr rest =>
          exact protocolAction_openingFrom next _ _ policy.2 disclosing.2 rest static intended.2

/-- At an intended source point carrying its static metadata, the canonical
opening has exactly the original always-disclosing action law. -/
theorem BehavioralPolicy.protocolAction_authenticOpening {who : Player}
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (policy : BehavioralPolicy who program) (disclosing : Disclosing program policy)
    (state : ProtocolState program)
    (static : ProtocolState.StaticAt program [] (Revelations.initial Γ) state)
    (intended : ProtocolState.Intended program state) :
    (policy.authenticOpening program).protocolAction program
        (ProtocolState.observe who program state) =
      policy.protocolAction program (ProtocolState.observe who program state) :=
  protocolAction_openingFrom program [] (Revelations.initial Γ) policy disclosing state static
    intended

end Vegas.SourceProgram
