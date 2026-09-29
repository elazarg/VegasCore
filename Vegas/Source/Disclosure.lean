/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.FiniteSupport
import GameTheory.Math.Probability.SelectiveStopping

/-! # Refusing to open, and when it is worth nothing

A source policy may withhold at its own reveal, publishing failure where it
could have published the value it bound. Unlike binding an unopenable candidate,
this is not publicly redundant: the two branches differ in what the program
produces, so no translation can remove the option and preserve the outcome law.

What can be removed is the *option's value*. A reveal is an informed stop-or-
continue decision, taken after the player has seen everything the program has
published so far, so the general statement applies: eliminating the stopping
branch is valid exactly when continuing is at least as good at every decision
state reached. That comparison is a hypothesis here, not a theorem — it is the
premise an honest-play layer has to carry, and the reason such a layer is
conditionally rather than unconditionally preserving.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A policy that never withholds what it bound. The dual of `ValueBinding`:
together they are what an honest profile means. -/
def Disclosing {who : Player} : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → BehavioralPolicy who p → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample _ _ _ k, policy => Disclosing k policy
  | _, _, .commit _ _ _ _ k, policy => Disclosing k policy.2
  | _, _, .reveal _ owner _ _ _ _ k, policy =>
      (∀ (own : owner = who) view, false ∉ (policy.1 own view).support) ∧
        Disclosing k policy.2

/-- Open at every own reveal, and leave every binding alone. -/
def BehavioralPolicy.forceDisclose {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    BehavioralPolicy who p → BehavioralPolicy who p
  | _, _, .ret _, _ => PUnit.unit
  | _, _, .sample _ _ _ k, policy => forceDisclose k policy
  | _, _, .commit _ _ _ _ k, policy => (policy.1, forceDisclose k policy.2)
  | _, _, .reveal _ _ _ _ _ _ k, policy =>
      (fun _ _ => PMF.pure true, forceDisclose k policy.2)

theorem disclosing_forceDisclose {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    (policy : BehavioralPolicy who p) → Disclosing p (policy.forceDisclose p)
  | _, _, .ret _, _ => trivial
  | _, _, .sample _ _ _ k, policy => disclosing_forceDisclose k policy
  | _, _, .commit _ _ _ _ k, policy => disclosing_forceDisclose k policy.2
  | _, _, .reveal _ _ _ _ _ _ k, policy =>
      ⟨fun _ _ => by simp [BehavioralPolicy.forceDisclose], disclosing_forceDisclose k policy.2⟩

/-- Opening is at least as good as refusing, at every decision this player could
face, measured against the continuation in which it opens from then on. This is
the premise, stated where the decision is taken rather than as a comparison of
unconditional expectations, which would not be a substitute. -/
def DisclosesProfitably {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    (State L (terminalCtx p) → ℝ) → BehavioralProfile p → BehavioralPolicy who p → Prop
  | _, _, .ret _, _, _, _ => True
  | _, _, .sample _ _ _ k, utility, profile, policy =>
      DisclosesProfitably k utility (afterSample profile) policy
  | _, _, .commit _ _ _ _ k, utility, profile, policy =>
      DisclosesProfitably k utility (afterCommit profile) policy.2
  | _, _, .reveal published owner _ _ source _ k, utility, profile, policy =>
      (∀ (_ : owner = who) (config : Config Player L _),
        expect (runFrom k (Function.update (afterReveal profile) who
            ((afterReveal profile who).forceDisclose k))
          (revealSuccessor published source config false)) utility ≤
        expect (runFrom k (Function.update (afterReveal profile) who
            ((afterReveal profile who).forceDisclose k))
          (revealSuccessor published source config true)) utility) ∧
        DisclosesProfitably k utility (afterReveal profile) policy.2

/-! ## Removing the refusal -/

/-- Forcing disclosure replaces only Boolean disclosure kernels, so the forced
profile branches finitely whenever the original does. -/
theorem forceDisclose_finiteSupport {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    (profile : BehavioralProfile p) → BehavioralProfile.FiniteSupport p profile →
    BehavioralProfile.FiniteSupport p
      (Function.update profile who ((profile who).forceDisclose p))
  | _, _, .ret _, _, _ => trivial
  | _, _, .sample _ _ _ k, profile, finite =>
      forceDisclose_finiteSupport (who := who) k (afterSample profile) finite
  | _, _, .commit cellName owner fresh guard k, profile, finite => by
      have hkernel : commitKernel (Function.update profile who
          ((profile who).forceDisclose (.commit cellName owner fresh guard k))) =
            commitKernel profile := by
        by_cases hown : owner = who
        · subst hown; simp [commitKernel, BehavioralPolicy.forceDisclose]
        · simp [commitKernel, Function.update_of_ne hown]
      refine ⟨fun view => by rw [hkernel]; exact finite.1 view, ?_⟩
      rw [afterCommit_update]
      exact forceDisclose_finiteSupport (who := who) k (afterCommit profile) finite.2
  | _, _, .reveal _ _ _ _ _ _ k, profile, finite => by
      simp only [BehavioralProfile.FiniteSupport, afterReveal_update]
      exact forceDisclose_finiteSupport (who := who) k (afterReveal profile) finite

/-- Forcing this player to open never lowers its expected value, provided
opening is at least as good at every decision it could face. The reveal is an
informed stop-or-continue decision, so this is the general selective-stopping
bound instantiated at the source reveal. Quantified over every configuration,
the premise is also necessary: `selective_stopping_le_iff` says eliminating the
stopping branch is valid for all state laws and stopping policies exactly when
continuing is at least as good at every decision state. -/
theorem forceDisclose_expect_le {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    (utility : State L (terminalCtx p) → ℝ) → (profile : BehavioralProfile p) →
    BehavioralProfile.FiniteSupport p profile →
    DisclosesProfitably p utility profile (profile who) →
    (config : Config Player L Γ) →
    expect (runFrom p profile config) utility ≤
      expect (runFrom p (Function.update profile who
        ((profile who).forceDisclose p)) config) utility
  | _, _, .ret _, _, _, _, _, _ => le_of_eq rfl
  | _, _, .sample _ _ _ k, utility, profile, finite, premise, config => by
      have before := runFrom_support_finite _ profile finite config
      have after := runFrom_support_finite _ _
        (forceDisclose_finiteSupport (who := who) _ profile finite) config
      simp only [runFrom_sample] at before after ⊢
      exact expect_bind_mono_on_support _ _ _ _
        (payoffIntegrable_of_finite_support _ _ before)
        (payoffIntegrable_of_finite_support _ _ after) fun value _ =>
          forceDisclose_expect_le k utility (afterSample profile) finite premise _
  | _, _, .commit cellName owner fresh guard k, utility, profile, finite, premise, config => by
      have hkernel : commitKernel (Function.update profile who
          ((profile who).forceDisclose (.commit cellName owner fresh guard k))) =
            commitKernel profile := by
        by_cases hown : owner = who
        · subst hown; simp [commitKernel, BehavioralPolicy.forceDisclose]
        · simp [commitKernel, Function.update_of_ne hown]
      have before := runFrom_support_finite _ profile finite config
      have after := runFrom_support_finite _ _
        (forceDisclose_finiteSupport (who := who) _ profile finite) config
      simp only [runFrom_commit, hkernel, afterCommit_update] at before after ⊢
      exact expect_bind_mono_on_support _ _ _ _
        (payoffIntegrable_of_finite_support _ _ before)
        (payoffIntegrable_of_finite_support _ _ after) fun choice _ =>
          forceDisclose_expect_le k utility (afterCommit profile) finite.2 premise _
  | _, _, .reveal published owner name fresh source unresolved k,
      utility, profile, finite, premise, config => by
      have step := fun (disclose : Bool) =>
        forceDisclose_expect_le k utility (afterReveal profile) finite premise.2
          (revealSuccessor published source config disclose)
      let forced := Function.update (afterReveal profile) who
        ((afterReveal profile who).forceDisclose k)
      have forcedFinite : BehavioralProfile.FiniteSupport k forced :=
        forceDisclose_finiteSupport (who := who) k (afterReveal profile) finite
      have before := runFrom_support_finite _ profile finite config
      have after := runFrom_support_finite _ _
        (forceDisclose_finiteSupport (who := who) _ profile finite) config
      simp only [runFrom_reveal, afterReveal_update] at before after ⊢
      by_cases hown : owner = who
      · subst hown
        have hforced : revealKernel (Function.update profile owner
            ((profile owner).forceDisclose
              (.reveal published owner name fresh source unresolved k))) =
              fun _ => PMF.pure true := by
          simp [revealKernel, BehavioralPolicy.forceDisclose]
        rw [hforced, PMF.pure_bind]
        have branches : ((revealKernel profile (Config.view owner config)).bind fun disclose =>
            runFrom k forced (revealSuccessor published source config disclose)).support.Finite :=
          by
            rw [PMF.support_bind]
            exact (Set.toFinite _).biUnion fun _ _ => runFrom_support_finite k forced
              forcedFinite _
        refine le_trans (expect_bind_mono_on_support _ _ _ _
          (payoffIntegrable_of_finite_support _ _ before)
          (payoffIntegrable_of_finite_support _ _ branches) fun disclose _ => step disclose) ?_
        have hshape : ∀ stops : Bool,
            (if stops then
              runFrom k forced (revealSuccessor published source config false)
            else
              runFrom k forced (revealSuccessor published source config true)) =
              runFrom k forced (revealSuccessor published source config !stops) := by
          intro stops; cases stops <;> rfl
        have proceedFinite := runFrom_support_finite k forced forcedFinite
          (revealSuccessor published source config true)
        have general := selective_stopping_le (PMF.pure (α := Unit) ())
          (fun _ => (revealKernel profile (Config.view owner config)).map not)
          (fun _ => runFrom k forced (revealSuccessor published source config false))
          (fun _ => runFrom k forced (revealSuccessor published source config true))
          utility
          (payoffIntegrable_of_finite_support _ _ (by
            simp only [PMF.pure_bind, PMF.bind_map, Function.comp_def, hshape, Bool.not_not]
            exact branches))
          (payoffIntegrable_of_finite_support _ _ (by
            simpa only [PMF.pure_bind] using proceedFinite))
          (fun _ _ _ _ _ => premise.1 rfl config)
        simp only [PMF.pure_bind, PMF.bind_map, Function.comp_def, hshape, Bool.not_not]
          at general
        exact general
      · have hkernel : revealKernel (Function.update profile who
            ((profile who).forceDisclose
              (.reveal published owner name fresh source unresolved k))) =
              revealKernel profile := by
          simp [revealKernel, Function.update_of_ne hown]
        rw [hkernel] at after ⊢
        exact expect_bind_mono_on_support _ _ _ _
          (payoffIntegrable_of_finite_support _ _ before)
          (payoffIntegrable_of_finite_support _ _ after) fun disclose _ => step disclose

/-- The same across a private setup law. The premise does not mention the draw,
so one comparison per decision serves every branch. -/
theorem forceDisclose_run_expect_le {who : Player} (setup : Setup (Player := Player) (L := L))
    (utility : State L (terminalCtx setup.program) → ℝ)
    (profile : BehavioralProfile setup.program)
    (initialFinite : setup.initialLaw.support.Finite)
    (finite : BehavioralProfile.FiniteSupport setup.program profile)
    (premise : DisclosesProfitably setup.program utility profile (profile who)) :
    expect (setup.run profile) utility ≤
      expect (setup.run (Function.update profile who
        ((profile who).forceDisclose setup.program))) utility := by
  have before := setup.run_support_finite initialFinite profile finite
  have after := setup.run_support_finite initialFinite _
    (forceDisclose_finiteSupport (who := who) setup.program profile finite)
  simp only [Setup.run] at before after ⊢
  exact expect_bind_mono_on_support _ _ _ _
    (payoffIntegrable_of_finite_support _ _ before)
    (payoffIntegrable_of_finite_support _ _ after) fun initial _ =>
      forceDisclose_expect_le setup.program utility profile finite premise
        ⟨initial, [], Revelations.initial setup.context, fun _ => []⟩

/-- So under that premise the player gives up nothing by joining the class that
never refuses. This is the conditional an honest-play layer states: not that
compilation preserves the class, which it cannot, but that a player who prefers
opening at every decision loses nothing by being held to it. -/
theorem exists_disclosing_expect_le {who : Player} (setup : Setup (Player := Player) (L := L))
    (utility : State L (terminalCtx setup.program) → ℝ)
    (profile : BehavioralProfile setup.program)
    (initialFinite : setup.initialLaw.support.Finite)
    (finite : BehavioralProfile.FiniteSupport setup.program profile)
    (premise : DisclosesProfitably setup.program utility profile (profile who)) :
    ∃ alternative : BehavioralPolicy who setup.program,
      Disclosing setup.program alternative ∧
        expect (setup.run profile) utility ≤
          expect (setup.run (Function.update profile who alternative)) utility :=
  ⟨(profile who).forceDisclose setup.program,
    disclosing_forceDisclose setup.program (profile who),
    forceDisclose_run_expect_le setup utility profile initialFinite finite premise⟩

end Vegas.SourceProgram
