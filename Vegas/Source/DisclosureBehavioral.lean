/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Setup
import GameTheory.Math.Probability.Support

/-! # Normalizing unopenable disclosure intentions

The compiler suppresses only requests to open an unopenable own binding.
Authentic attempts remain unchanged when deferred guards reject publication.
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

/-- Suppress only a disclosure whose own binding is unopenable. Authentic
attempts remain unchanged even when their deferred guards reject publication. -/
def BehavioralPolicy.normalizeDisclosures {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → BehavioralPolicy who program →
      BehavioralPolicy who program
  | _, _, .ret _, _ => PUnit.unit
  | _, _, .sample _ _ _ next, policy => normalizeDisclosures next policy
  | _, _, .commit _ _ _ _ next, policy => (policy.1, normalizeDisclosures next policy.2)
  | _, _, .reveal _ _ _ _ selected _ next, policy =>
      (fun own view active => (policy.1 own view active).map fun disclose =>
        disclose && ((view.observation.cells.get (own ▸ selected)).getD .failure).isSuccess,
        normalizeDisclosures next policy.2)

/-- Normalize every player's unopenable disclosure decisions pointwise. -/
def normalizeDisclosureProfile {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program) :
    BehavioralProfile program :=
  fun who => (profile who).normalizeDisclosures program

/-- Suppressing unopenable disclosure choices twice changes nothing further. -/
theorem BehavioralPolicy.normalizeDisclosures_idempotent {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (policy : BehavioralPolicy who program) →
    (policy.normalizeDisclosures program).normalizeDisclosures program =
      policy.normalizeDisclosures program
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, policy => normalizeDisclosures_idempotent next policy
  | _, _, .commit _ _ _ _ next, policy =>
      Prod.ext rfl (normalizeDisclosures_idempotent next policy.2)
  | _, _, .reveal _ _ _ _ _ _ next, policy => by
      refine Prod.ext ?_ (normalizeDisclosures_idempotent next policy.2)
      funext own view active
      change ((policy.1 own view active).map _).map _ = (policy.1 own view active).map _
      rw [PMF.map_comp]
      congr 1
      funext disclose
      simp only [Function.comp_apply, Bool.and_assoc, Bool.and_self]

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

/-- Normalized policies suppress only unopenable intentions, at every active view. -/
theorem BehavioralPolicy.normalizeDisclosures_authentic {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (policy : BehavioralPolicy who program) →
    (policy.normalizeDisclosures program).AuthenticDisclosures program
  | _, _, .ret _, _ => trivial
  | _, _, .sample _ _ _ next, policy => normalizeDisclosures_authentic next policy
  | _, _, .commit _ _ _ _ next, policy => normalizeDisclosures_authentic next policy.2
  | _, _, .reveal _ _ _ _ selected _ next, policy => by
      refine ⟨?_, normalizeDisclosures_authentic next policy.2⟩
      intro own view active disclose supported
      obtain ⟨intended, _, rfl⟩ := PMF.support_map .. ▸ supported
      simp only [Bool.and_assoc, Bool.and_self]

private theorem revealKernel_normalizeDisclosures
    {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {selected : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    (profile : BehavioralProfile (.reveal published owner name fresh selected unresolved next))
    (config : Config Player L Γ) (active : owner ∉ config.defaulted) :
    revealKernel (normalizeDisclosureProfile _ profile) (config.view owner) active =
      (revealKernel profile (config.view owner) active).map fun disclose =>
        disclose && (config.state.get selected).isSuccess := by
  simp [revealKernel, normalizeDisclosureProfile, BehavioralPolicy.normalizeDisclosures,
    Config.view, sourceObserve, Env.get]

/-- Pointwise disclosure normalization preserves the joint law of every typed
cell and the complete public default record under the sole source evaluator. -/
theorem runFrom_normalizeDisclosures_eq
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O) :
    ∀ (profile : BehavioralProfile program) (config : Config Player L Γ),
      (runFrom program (normalizeDisclosureProfile program profile) config).map
          (fun final => (final.state, final.defaults)) =
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
        runFrom next (normalizeDisclosureProfile next (afterCommit profile))
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
          revealKernel_normalizeDisclosures profile config inactive]
        simp only [PMF.bind_map, PMF.map_bind]
        apply bind_congr_on_support _
        intro disclose _
        change (runFrom next (normalizeDisclosureProfile next (afterReveal profile))
          (revealSuccessor published selected config
            (disclose && (config.state.get selected).isSuccess))).map
              (fun final => (final.state, final.defaults)) = _
        have tail := ih (afterReveal profile)
          (revealSuccessor published selected config
            (disclose && (config.state.get selected).isSuccess))
        rw [tail]
        cases binding : config.state.get selected with
        | success value =>
            simp only [PublicationResult.isSuccess, Bool.and_true]
        | failure =>
            simp only [binding, PublicationResult.isSuccess, Bool.and_false,
              revealSuccessor, inactive, ite_false, Bool.false_eq_true, ite_self,
              PublicationResult.isFailure]
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
      simp only [normalizeDisclosureProfile, Function.update_self]
    · simp only [normalizeDisclosureProfile, Function.update_of_ne same,
        BehavioralPolicy.normalizeDisclosures_idempotent]
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
