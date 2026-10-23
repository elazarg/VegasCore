/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.DisclosureOpening
import Vegas.Source.IntendedPlay
import Vegas.Source.ProtocolBehavioralPolicy

/-! # Effective openings

The effective opening of a source policy keeps its binding kernels and, at each
own reveal, discloses exactly when a disclosure is effective at the registry and
publication status the program carries to that point
(`Vegas.SourceProgram.BehavioralPolicy.effectiveOpening`). It opens effectively
by construction and keeps the policy's admission.

The registry and publication status of a source configuration are fixed by its
program point: a source point reached from an entry whose configuration
carries the given registry and publication status carries, at every program
point, the ones the program carries there
(`Vegas.SourceProgram.ProtocolState.staticAt_step`). At such a point that is
also a point of the intended game, the effective opening of a policy that
always discloses has the policy's own source action law
(`Vegas.SourceProgram.BehavioralPolicy.protocolAction_effectiveOpening`): every
disclosure there is effective.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **The effective opening.** Keep every binding kernel, and at every own
reveal disclose exactly when a disclosure is effective at the registry and
publication status carried by the program. -/
def BehavioralPolicy.effectiveOpening {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Registry Γ → Revelations Γ →
    BehavioralPolicy who program → BehavioralPolicy who program
  | _, _, .ret _, _, _, policy => policy
  | _, _, .sample _ _ _ next, registry, revelations, policy =>
      effectiveOpening next registry.weaken revelations.weaken policy
  | _, _, .commit (payload := payload) name owner _ guard next, registry, revelations,
      policy =>
      (policy.1, effectiveOpening next
        ({ owner := owner, subject := name, payload := payload, source := .here,
            guard := guard.weaken } :: registry.weaken) revelations.weaken policy.2)
  | _, _, .reveal published _ _ _ selected _ next, registry, revelations, policy =>
      (fun own view => PMF.pure
        (effectiveDisclosureView published selected registry revelations (own.symm ▸ view.1)
          true),
        effectiveOpening next registry.weaken
          (revelations.reveal (published := published) selected) policy.2)

/-- The effective opening keeps the policy's admission. -/
theorem BehavioralPolicy.admitted_effectiveOpening {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (registry : Registry Γ) → (revelations : Revelations Γ) →
    (policy : BehavioralPolicy who program) → policy.Admitted program admission →
    (policy.effectiveOpening program registry revelations).Admitted program admission
  | _, _, .ret _, _, _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, admission, _, _, policy, permitted =>
      admitted_effectiveOpening next admission _ _ policy permitted
  | _, _, .commit _ _ _ _ next, _, _, _, policy, permitted =>
      ⟨permitted.1, admitted_effectiveOpening next _ _ _ policy.2 permitted.2⟩
  | _, _, .reveal _ _ _ _ _ _ next, admission, _, _, policy, permitted =>
      admitted_effectiveOpening next admission _ _ policy.2 permitted

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
/-- A disclosure at an intended configuration is effective. -/
theorem Config.Intended.disclosure_effective {Γ : SourceCtx Player L}
    {unresolved : Finset VarId} {config : Config Player L Γ}
    (intended : config.Intended unresolved) {owner : Player} {payload : L.Ty} {name : VarId}
    (published : VarId) (source : HasVar Γ name (.commitment owner payload)) :
    effectiveDisclosure published source config true = true := by
  obtain ⟨value, bound⟩ := intended.bound source
  have state := intended.reveal_state (published := published) source
  unfold SourceProgram.effectiveDisclosure disclosureResult
  rw [state, Env.cons_get_here]
  change (match (bindingOf config source) with
    | .failure => false
    | .success _ => true) = true
  rw [show bindingOf config source = .success value from bound]

/-- **Effective openings agree at intended points.** At an intended source
point carrying the program's registry and publication status, the effective
opening of a policy that always discloses has the policy's source action law. -/
theorem BehavioralPolicy.protocolAction_effectiveOpening {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (registry : Registry Γ) →
    (revelations : Revelations Γ) → (policy : BehavioralPolicy who program) →
    Disclosing program policy → (state : ProtocolState program) →
    ProtocolState.StaticAt program registry revelations state →
    ProtocolState.Intended program state →
    (policy.effectiveOpening program registry revelations).protocolAction program
        (ProtocolState.observe who program state) =
      policy.protocolAction program (ProtocolState.observe who program state)
  | _, _, .ret _, _, _, _, _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, _, _, policy, disclosing, state, holds, intended => by
      cases state with
      | inl _ => rfl
      | inr rest =>
          exact protocolAction_effectiveOpening next _ _ policy disclosing rest holds intended
  | _, _, .commit _ _ _ _ next, _, _, policy, disclosing, state, holds, intended => by
      cases state with
      | inl _ => rfl
      | inr rest =>
          exact protocolAction_effectiveOpening next _ _ policy.2 disclosing rest holds intended
  | _, _, .reveal published owner name _ selected _ next, registry, revelations, policy,
      disclosing, state, holds, intended => by
      cases state with
      | inl config =>
          obtain ⟨registryEq, revelationsEq⟩ := holds
          change (if own : owner = who then
              (PMF.pure (effectiveDisclosureView published selected registry revelations
                (own.symm ▸ (config.view who).1) true)).map
                (fun disclose => some (OwnAction.reveal owner name disclose))
            else PMF.pure none) =
            (if own : owner = who then
              (policy.1 own (config.view who)).map
                (fun disclose => some (OwnAction.reveal owner name disclose))
            else PMF.pure none)
          by_cases own : owner = who
          · subst own
            rw [dite_eq_left (show owner = owner from rfl),
              dite_eq_left (show owner = owner from rfl),
              eq_pure_true_of_false_not_mem (disclosing.1 rfl (config.view owner))]
            congr 2
            rw [← registryEq, ← revelationsEq]
            change effectiveDisclosureView published selected config.registry config.revelations
              (sourceObserve owner config.state) true = true
            rw [effectiveDisclosureView_observe]
            exact intended.1.disclosure_effective published selected
          · rw [dite_eq_right own, dite_eq_right own]
      | inr rest =>
          exact protocolAction_effectiveOpening next _ _ policy.2 disclosing.2 rest holds
            intended.2

end Vegas.SourceProgram
