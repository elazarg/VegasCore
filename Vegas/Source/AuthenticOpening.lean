/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.DisclosureOpening
import Vegas.Source.IntendedPlay
import Vegas.Source.ProtocolBehavioralPolicy

/-! # Authentic source openings

An authentic opening retains every binding kernel and opens every own binding
that contains a value, including attempts rejected by deferred guards. Its
source action law agrees with an always-disclosing policy at intended points.
The static registry and revelation invariant also follows the source syntax.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Authentic openings retain the original binding admission guarantee. -/
theorem BehavioralPolicy.admitted_authenticOpening {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (policy : BehavioralPolicy who program) → policy.Admitted program admission →
    (policy.authenticOpening program).Admitted program admission
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, policy, permitted =>
      admitted_authenticOpening next admission policy permitted
  | _, _, .commit _ _ _ _ next, _, policy, permitted =>
      ⟨permitted.1, admitted_authenticOpening next _ policy.2 permitted.2⟩
  | _, _, .reveal _ _ _ _ _ _ next, admission, policy, permitted =>
      admitted_authenticOpening next admission policy.2 permitted

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

/-- At an intended source point an authentic opening has the same action law
as the original always-disclosing policy. Static metadata agreement is unnecessary. -/
theorem BehavioralPolicy.protocolAction_authenticOpening {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (policy : BehavioralPolicy who program) →
    Disclosing program policy → (state : ProtocolState program) →
    ProtocolState.Intended program state →
    (policy.authenticOpening program).protocolAction program
        (ProtocolState.observe who program state) =
      policy.protocolAction program (ProtocolState.observe who program state)
  | _, _, .ret _, _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, policy, disclosing, state, intended => by
      cases state with
      | inl _ => rfl
      | inr rest => exact protocolAction_authenticOpening next policy disclosing rest intended
  | _, _, .commit _ _ _ _ next, policy, disclosing, state, intended => by
      cases state with
      | inl _ => rfl
      | inr rest =>
          exact protocolAction_authenticOpening next policy.2 disclosing rest intended
  | _, _, .reveal _ owner name _ selected _ next, policy, disclosing, state, intended => by
      cases state with
      | inl config =>
          simp only [authenticOpening, forceDisclose, normalizeDisclosures,
            PMF.pure_map, Bool.true_and]
          change (if own : owner = who then
              if active : who ∉ (config.view who).defaulted then
                (PMF.pure
                  (((config.view who).observation.cells.get (own ▸ selected)).getD
                    .failure).isSuccess).map
                  (fun disclose => some (OwnAction.reveal owner name disclose))
              else PMF.pure none
            else PMF.pure none) =
            (if own : owner = who then
              if active : who ∉ (config.view who).defaulted then
                (policy.1 own (config.view who) active).map
                  (fun disclose => some (OwnAction.reveal owner name disclose))
              else PMF.pure none
            else PMF.pure none)
          by_cases own : owner = who
          · subst who
            rw [dite_eq_left (show owner = owner from rfl),
              dite_eq_left (show owner = owner from rfl)]
            by_cases active : owner ∉ (config.view owner).defaulted
            · rw [dite_eq_left active, dite_eq_left active,
                eq_pure_true_of_false_not_mem (disclosing.1 rfl (config.view owner) active)]
              congr 2
              simpa only [Config.view, sourceObserve, Env.get, ite_true, Option.getD_some] using
                intended.1.binding_isSuccess selected
            · rw [dite_eq_right active, dite_eq_right active]
          · rw [dite_eq_right own, dite_eq_right own]
      | inr rest =>
          exact protocolAction_authenticOpening next policy.2 disclosing.2 rest intended.2

end Vegas.SourceProgram
