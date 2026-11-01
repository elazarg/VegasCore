/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Setup
import Vegas.Source.DisclosureAliases
import Vegas.Source.ProtocolBehavioralPolicy
import GameTheory.Math.Probability.Support

/-! # Normalizing ineffective disclosure intentions

The compiler withholds precisely the requests whose publication would fail.
The owner computes this choice from its view and the static guard obligations.
The joint terminal typed state and full public default record are preserved.
The private action history of an owner that defaults may differ, since that
owner has no later strategic callback.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [IExpr.ResultTypes L] in
private theorem active_history_update_eq
    (before after : DefaultHistory Player) (monotone : before.defaulted ⊆ after.defaulted)
    (left right : History Player L)
    (agree : ∀ who, who ∉ before.defaulted → left who = right who)
    (owner : Player) (action : OwnAction Player L) :
    ∀ who, who ∉ after.defaulted →
      Function.update left owner (left owner ++ [action]) who =
        Function.update right owner (right owner ++ [action]) who := by
  intro who active
  have prior : who ∉ before.defaulted := fun excluded => active (monotone excluded)
  by_cases same : who = owner
  · subst who
    simp only [Function.update_self, agree owner prior]
  · simp only [Function.update_of_ne same, agree who prior]

/-- Once an owner defaults its remembered intention cannot affect another
callback. Histories of precisely the still-active owners suffice for execution. -/
private theorem runFrom_active_histories_eq
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O) :
    ∀ (profile : BehavioralProfile program) (state : State L Γ) (registry : Registry Γ)
      (revelations : Revelations Γ) (defaults : DefaultHistory Player)
      (left right : History Player L),
      (∀ who, who ∉ defaults.defaulted → left who = right who) →
      (runFrom program profile ⟨state, registry, revelations, left, defaults⟩).map
          (fun final => (final.state, final.defaults)) =
        (runFrom program profile ⟨state, registry, revelations, right, defaults⟩).map
          (fun final => (final.state, final.defaults)) := by
  induction program with
  | ret payoffs =>
      intro profile state registry revelations defaults left right agree
      simp only [runFrom, PMF.pure_map]
  | sample name fresh law next ih =>
      intro profile state registry revelations defaults left right agree
      simp only [runFrom, PMF.map_bind]
      apply bind_congr_on_support _
      intro value _
      apply ih
      intro who active
      exact agree who (fun excluded => active (defaults.defaulted_mono none excluded))
  | commit name owner fresh guard next ih =>
      intro profile state registry revelations defaults left right agree
      by_cases inactive : owner ∈ defaults.defaulted
      · simp only [runFrom, Config.defaulted, inactive, dite_true, PMF.pure_bind,
          commitSuccessor, ite_true]
        apply ih
        intro who active
        exact agree who (fun excluded => active (defaults.defaulted_mono none excluded))
      · have ownerHistory := agree owner inactive
        simp only [runFrom, Config.defaulted, inactive, dite_false, Config.view, ownerHistory,
          PMF.map_bind]
        apply bind_congr_on_support _
        intro choice _
        simp only [commitSuccessor, Config.defaulted, inactive, ite_false]
        apply ih
        exact active_history_update_eq defaults _ (defaults.defaulted_mono _) left right agree
          owner (.commit owner name _ choice)
  | reveal published owner name fresh selected unresolved next ih =>
      intro profile state registry revelations defaults left right agree
      by_cases inactive : owner ∈ defaults.defaulted
      · simp only [runFrom, Config.defaulted, inactive, dite_true, PMF.pure_bind,
          revealSuccessor, ite_true]
        apply ih
        intro who active
        exact agree who (fun excluded => active (defaults.defaulted_mono none excluded))
      · have ownerHistory := agree owner inactive
        simp only [runFrom, Config.defaulted, inactive, dite_false, Config.view, ownerHistory,
          PMF.map_bind]
        apply bind_congr_on_support _
        intro disclose _
        simp only [revealSuccessor, Config.defaulted, inactive, ite_false]
        apply ih
        exact active_history_update_eq defaults _ (defaults.defaulted_mono _) left right agree
          owner (.reveal owner name disclose)

/-- Normalize disclosures using the static guard registry and publication positions
at this source instruction. Every callback reads only its owner's actual view. -/
def BehavioralPolicy.normalizeDisclosuresFrom {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Registry Γ → Revelations Γ →
    BehavioralPolicy who program → BehavioralPolicy who program
  | _, _, .ret _, _, _, _ => PUnit.unit
  | _, _, .sample _ _ _ next, registry, revelations, policy =>
      normalizeDisclosuresFrom next registry.weaken revelations.weaken policy
  | _, _, .commit (payload := payload) name owner _ guard next, registry, revelations, policy =>
      (policy.1, normalizeDisclosuresFrom next
        ({ owner := owner, subject := name, payload := payload, source := .here,
            guard := guard.weaken } :: registry.weaken) revelations.weaken policy.2)
  | _, _, .reveal published _ _ _ selected _ next, registry, revelations, policy =>
      (fun own view active => (policy.1 own view active).map fun disclose =>
        effectiveDisclosureView published (own ▸ selected) registry revelations view disclose,
        normalizeDisclosuresFrom next registry.weaken
          (revelations.reveal (published := published) selected) policy.2)

/-- Normalize a policy from the source initializer's empty guard registry. -/
def BehavioralPolicy.normalizeDisclosures {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (policy : BehavioralPolicy who program) : BehavioralPolicy who program :=
  policy.normalizeDisclosuresFrom program [] (Revelations.initial Γ)

/-- Normalize all players from the static metadata at the source instruction. -/
def normalizeDisclosureProfileFrom {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (registry : Registry Γ)
    (revelations : Revelations Γ) (profile : BehavioralProfile program) :
    BehavioralProfile program :=
  fun who => (profile who).normalizeDisclosuresFrom program registry revelations

/-- Normalize every player's ineffective disclosures from source initialization. -/
def normalizeDisclosureProfile {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program) :
    BehavioralProfile program :=
  normalizeDisclosureProfileFrom program [] (Revelations.initial Γ) profile

/-- Disclosure normalization leaves every commitment callback unchanged. -/
theorem BehavioralPolicy.normalizeDisclosuresFrom_admitted_iff {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (registry : Registry Γ) →
    (revelations : Revelations Γ) → (admission : CommitmentInterface program) →
    (policy : BehavioralPolicy who program) →
    (policy.normalizeDisclosuresFrom program registry revelations).Admitted program admission ↔
      policy.Admitted program admission
  | _, _, .ret _, _, _, _, _ => Iff.rfl
  | _, _, .sample _ _ _ next, _, _, admission, policy =>
      normalizeDisclosuresFrom_admitted_iff next _ _ admission policy
  | _, _, .commit _ _ _ _ next, _, _, admission, policy =>
      and_congr Iff.rfl
        (normalizeDisclosuresFrom_admitted_iff next _ _
          (fun site => admission (some site)) policy.2)
  | _, _, .reveal _ _ _ _ _ _ next, _, _, admission, policy =>
      normalizeDisclosuresFrom_admitted_iff next _ _ admission policy.2

/-- Initialized normalization preserves every commitment admission interface. -/
theorem BehavioralPolicy.normalizeDisclosures_admitted_iff {who : Player}
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (policy : BehavioralPolicy who program) :
    (policy.normalizeDisclosures program).Admitted program admission ↔
      policy.Admitted program admission :=
  normalizeDisclosuresFrom_admitted_iff program _ _ admission policy

/-- Suppressing ineffective disclosures twice changes nothing further. -/
theorem BehavioralPolicy.normalizeDisclosuresFrom_idempotent {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (registry : Registry Γ) →
    (revelations : Revelations Γ) → (policy : BehavioralPolicy who program) →
    (policy.normalizeDisclosuresFrom program registry revelations).normalizeDisclosuresFrom
        program registry revelations = policy.normalizeDisclosuresFrom program registry revelations
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, _, _, policy =>
      normalizeDisclosuresFrom_idempotent next _ _ policy
  | _, _, .commit _ _ _ _ next, _, _, policy =>
      Prod.ext rfl (normalizeDisclosuresFrom_idempotent next _ _ policy.2)
  | _, _, .reveal _ _ _ _ _ _ next, _, _, policy => by
      refine Prod.ext ?_ (normalizeDisclosuresFrom_idempotent next _ _ policy.2)
      funext own view active
      change ((policy.1 own view active).map _).map _ = (policy.1 own view active).map _
      rw [PMF.map_comp]
      congr 1
      funext disclose
      exact effectiveDisclosureView_idempotent ..

/-- Initialized normalization is idempotent. -/
theorem BehavioralPolicy.normalizeDisclosures_idempotent {who : Player}
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (policy : BehavioralPolicy who program) :
    (policy.normalizeDisclosures program).normalizeDisclosures program =
      policy.normalizeDisclosures program :=
  normalizeDisclosuresFrom_idempotent program _ _ policy

/-- Every supported reveal choice is fixed by suppressing unopenable bindings. -/
def BehavioralPolicy.AuthenticDisclosures {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → BehavioralPolicy who program → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample _ _ _ next, policy => AuthenticDisclosures next policy
  | _, _, .commit _ _ _ _ next, policy => AuthenticDisclosures next policy.2
  | _, _, .reveal _ _ _ _ selected _ next, policy =>
      (∀ own view active disclose, disclose ∈ (policy.1 own view active).support →
        (disclose && ((view.observation.cells.get (own ▸ selected)).getD .failure).isSuccess) =
          disclose) ∧
      AuthenticDisclosures next policy.2

/-- A supported true disclosure publishes successfully, using the static
obligations and the owner's view rather than hidden foreign cells. -/
def BehavioralPolicy.EffectiveDisclosures {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Registry Γ → Revelations Γ →
    BehavioralPolicy who program → Prop
  | _, _, .ret _, _, _, _ => True
  | _, _, .sample _ _ _ next, registry, revelations, policy =>
      EffectiveDisclosures next registry.weaken revelations.weaken policy
  | _, _, .commit (payload := payload) name owner _ guard next, registry, revelations, policy =>
      EffectiveDisclosures next
        ({ owner := owner, subject := name, payload := payload, source := .here,
            guard := guard.weaken } :: registry.weaken) revelations.weaken policy.2
  | _, _, .reveal published _ _ _ selected _ next, registry, revelations, policy =>
      (∀ own view active disclose, disclose ∈ (policy.1 own view active).support →
        effectiveDisclosureView published (own ▸ selected) registry revelations view disclose =
          disclose) ∧
      EffectiveDisclosures next registry.weaken
        (revelations.reveal (published := published) selected) policy.2

/-- Every normalized choice is an effective representative. -/
theorem BehavioralPolicy.normalizeDisclosuresFrom_effective {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (registry : Registry Γ) →
    (revelations : Revelations Γ) → (policy : BehavioralPolicy who program) →
    EffectiveDisclosures program registry revelations
      (policy.normalizeDisclosuresFrom program registry revelations)
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, _, _, policy =>
      normalizeDisclosuresFrom_effective next _ _ policy
  | _, _, .commit _ _ _ _ next, _, _, policy =>
      normalizeDisclosuresFrom_effective next _ _ policy.2
  | _, _, .reveal _ _ _ _ _ _ next, _, _, policy => by
      refine ⟨?_, normalizeDisclosuresFrom_effective next _ _ policy.2⟩
      intro own view active disclose supported
      obtain ⟨intended, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact effectiveDisclosureView_idempotent ..

/-- Initialized normalized policies never send a rejected opening. -/
theorem BehavioralPolicy.normalizeDisclosures_effective {who : Player}
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (policy : BehavioralPolicy who program) :
    EffectiveDisclosures program [] (Revelations.initial Γ)
      (policy.normalizeDisclosures program) :=
  normalizeDisclosuresFrom_effective program _ _ policy

/-- Effective choices are authentic choices. -/
theorem BehavioralPolicy.EffectiveDisclosures.authentic {who : Player}
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O) :
    ∀ (registry : Registry Γ) (revelations : Revelations Γ)
      (policy : BehavioralPolicy who program),
      EffectiveDisclosures program registry revelations policy →
        AuthenticDisclosures program policy := by
  induction program with
  | ret payoffs => intro registry revelations policy effective; trivial
  | sample name fresh law next ih =>
      intro registry revelations policy effective
      exact ih registry.weaken revelations.weaken policy effective
  | commit name owner fresh guard next ih =>
      intro registry revelations policy effective
      exact ih _ _ policy.2 effective
  | reveal published owner name fresh selected unresolved next ih =>
      intro registry revelations policy effective
      refine ⟨?_, ih _ _ policy.2 effective.2⟩
      intro own view active disclose supported
      cases own
      have fixed := effective.1 rfl view active disclose supported
      calc
        (disclose && ((view.observation.cells.get selected).getD .failure).isSuccess) =
            (effectiveDisclosureView published selected registry revelations view disclose &&
              ((view.observation.cells.get selected).getD .failure).isSuccess) :=
          congrArg (fun choice => choice &&
            ((view.observation.cells.get selected).getD .failure).isSuccess) fixed.symm
        _ = effectiveDisclosureView published selected registry revelations view disclose :=
          effectiveDisclosureView_authentic published selected registry revelations view disclose
        _ = disclose := fixed

/-- Every normalized policy remains authentic at every active view. -/
theorem BehavioralPolicy.normalizeDisclosures_authentic {who : Player}
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (policy : BehavioralPolicy who program) :
    (policy.normalizeDisclosures program).AuthenticDisclosures program :=
  (normalizeDisclosures_effective program policy).authentic program _ _ _

private theorem revealKernel_normalizeDisclosuresFrom
    {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {selected : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (profile : BehavioralProfile (.reveal published owner name fresh selected unresolved next))
    (config : Config Player L Γ) (active : owner ∉ config.defaulted) :
    revealKernel (normalizeDisclosureProfileFrom _ config.registry config.revelations profile)
        (config.view owner) active =
      (revealKernel profile (config.view owner) active).map fun disclose =>
        effectiveDisclosure published selected config disclose := by
  simp only [revealKernel, normalizeDisclosureProfileFrom,
    BehavioralPolicy.normalizeDisclosuresFrom, effectiveDisclosureView_observe]

/-- Normalization from actual static metadata preserves the joint law of every
cell and the complete public default record under the sole source evaluator. -/
theorem runFrom_normalizeDisclosures_eq
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O) :
    ∀ (profile : BehavioralProfile program) (config : Config Player L Γ),
      (runFrom program
        (normalizeDisclosureProfileFrom program config.registry config.revelations profile)
          config).map (fun final => (final.state, final.defaults)) =
        (runFrom program profile config).map (fun final => (final.state, final.defaults)) := by
  induction program with
  | ret payoffs =>
      intro profile config
      rfl
  | sample name fresh law next ih =>
      intro profile config
      simp only [runFrom, PMF.map_bind]
      apply bind_congr_on_support _
      intro value _
      exact ih (afterSample profile) (sampleSuccessor name config value)
  | commit name owner fresh guard next ih =>
      intro profile config
      change ((if inactive : owner ∈ config.defaulted then PMF.pure none
          else commitKernel profile (config.view owner) inactive).bind fun choice =>
        runFrom next (normalizeDisclosureProfileFrom next
          (commitSuccessor name guard config choice).registry
          (commitSuccessor name guard config choice).revelations (afterCommit profile))
          (commitSuccessor name guard config choice)).map _ = _
      rw [runFrom, PMF.map_bind, PMF.map_bind]
      apply bind_congr_on_support _
      intro choice _
      exact ih (afterCommit profile) (commitSuccessor name guard config choice)
  | reveal published owner name fresh selected unresolved next ih =>
      intro profile config
      by_cases inactive : owner ∈ config.defaulted
      · simp only [runFrom, inactive, dite_true, PMF.pure_bind]
        exact ih (afterReveal profile) (revealSuccessor published selected config false)
      · rw [runFrom, runFrom, dite_eq_right inactive, dite_eq_right inactive,
          revealKernel_normalizeDisclosuresFrom profile config inactive]
        simp only [PMF.bind_map, PMF.map_bind]
        apply bind_congr_on_support _
        intro disclose _
        change (runFrom next (normalizeDisclosureProfileFrom next
          (revealSuccessor published selected config
            (effectiveDisclosure published selected config disclose)).registry
          (revealSuccessor published selected config
            (effectiveDisclosure published selected config disclose)).revelations
          (afterReveal profile)) (revealSuccessor published selected config
            (effectiveDisclosure published selected config disclose))).map
              (fun final => (final.state, final.defaults)) = _
        rw [ih]
        cases disclose with
        | false => rw [effectiveDisclosure_false]
        | true =>
          cases result : disclosureResult published selected config true with
          | success value => simp only [effectiveDisclosure, result]
          | failure =>
            simp only [effectiveDisclosure, result]
            have expand (choice : Bool) : revealSuccessor published selected config choice =
                ⟨Env.cons (disclosureResult published selected config choice) config.state,
                  config.registry.weaken, Revelations.reveal config.revelations selected,
                  Function.update config.history owner
                    (config.history owner ++ [.reveal owner name choice]),
                  config.defaults.record (if
                    (disclosureResult published selected config choice).isFailure then
                      some owner else none)⟩ := by
              simp only [disclosureResult, revealSuccessor, inactive, ite_false, Env.cons_get_here]
            rw [expand false, expand true, disclosureResult_false, result]
            simp only [PublicationResult.isFailure, ite_true]
            apply runFrom_active_histories_eq
            intro who active
            have different : who ≠ owner := by
              intro same
              subst who
              exact active (by simp)
            simp only [Function.update_of_ne different]

/-- Initialized execution preserves all typed values and public defaults after
uniform behavioral disclosure normalization. -/
theorem run_normalizeDisclosures_eq
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (profile : BehavioralProfile program) (state : State L Γ) :
    (run program (normalizeDisclosureProfile program profile) state).map
        (fun final => (final.state, final.defaults)) =
      (run program profile state).map (fun final => (final.state, final.defaults)) :=
  runFrom_normalizeDisclosures_eq program profile (Config.initial state)

/-- Uniform normalization preserves the complete typed-state/default law for
an arbitrary initial source law. -/
theorem Setup.run_normalizeDisclosures_eq (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) :
    (setup.run (normalizeDisclosureProfile setup.program profile)).map
        (fun final => (final.state, final.defaults)) =
      (setup.run profile).map (fun final => (final.state, final.defaults)) := by
  simp only [Setup.run, PMF.map_bind]
  apply bind_congr_on_support _
  intro initial _
  exact SourceProgram.run_normalizeDisclosures_eq setup.program profile initial

/-- Normalizing only the opponents preserves every typed cell and the complete
public default record against an arbitrary unchanged replacement policy. -/
theorem Setup.run_update_normalizeDisclosures_eq
    (setup : Setup (Player := Player) (L := L)) (profile : BehavioralProfile setup.program)
    (who : Player) (policy : BehavioralPolicy who setup.program) :
    (setup.run (Function.update (normalizeDisclosureProfile setup.program profile) who policy)).map
        (fun final => (final.state, final.defaults)) =
      (setup.run (Function.update profile who policy)).map
        (fun final => (final.state, final.defaults)) := by
  have normalized : normalizeDisclosureProfile setup.program
        (Function.update (normalizeDisclosureProfile setup.program profile) who policy) =
      normalizeDisclosureProfile setup.program (Function.update profile who policy) := by
    funext player
    by_cases same : player = who
    · subst player
      simp only [normalizeDisclosureProfile, normalizeDisclosureProfileFrom, Function.update_self]
    · simp only [normalizeDisclosureProfile, normalizeDisclosureProfileFrom,
        Function.update_of_ne same, BehavioralPolicy.normalizeDisclosuresFrom_idempotent]
  rw [← setup.run_normalizeDisclosures_eq, normalized, setup.run_normalizeDisclosures_eq]

/-- Every public terminal observable has the same law after disclosure normalization. -/
theorem Setup.publicRun_normalizeDisclosures_eq (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) :
    setup.publicRun (normalizeDisclosureProfile setup.program profile) =
      setup.publicRun profile := by
  have joint := setup.run_normalizeDisclosures_eq profile
  have projected := congrArg
    (PMF.map fun pair : State L setup.program.terminalCtx × DefaultHistory Player =>
      (⟨sourcePublicEnv pair.1, pair.2⟩ : PublicOutcome setup.program)) joint
  change (setup.run _).map (fun final =>
      (⟨sourcePublicEnv final.state, final.defaults⟩ : PublicOutcome setup.program)) =
    (setup.run _).map (fun final =>
      (⟨sourcePublicEnv final.state, final.defaults⟩ : PublicOutcome setup.program))
  simpa only [PMF.map_comp, Function.comp_def] using projected

end Vegas.SourceProgram
