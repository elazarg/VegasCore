/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Setup
import GameTheoryExtensions.Math.SelectiveStopping

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
      (fun _ _ => FinDist.pure true, forceDisclose k policy.2)

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
        (runFrom k (Function.update (afterReveal profile) who
            ((afterReveal profile who).forceDisclose k))
          (revealSuccessor published source config false)).expect utility ≤
        (runFrom k (Function.update (afterReveal profile) who
            ((afterReveal profile who).forceDisclose k))
          (revealSuccessor published source config true)).expect utility) ∧
        DisclosesProfitably k utility (afterReveal profile) policy.2

/-! ## Removing the refusal -/

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
    DisclosesProfitably p utility profile (profile who) →
    (config : Config Player L Γ) →
    (runFrom p profile config).expect utility ≤
      (runFrom p (Function.update profile who
        ((profile who).forceDisclose p)) config).expect utility
  | _, _, .ret _, _, _, _, _ => le_of_eq rfl
  | _, _, .sample _ _ _ k, utility, profile, premise, config => by
      rw [runFrom_sample, runFrom_sample, FinDist.expect_bind, FinDist.expect_bind]
      exact FinDist.expect_mono fun value _ =>
        forceDisclose_expect_le k utility (afterSample profile) premise _
  | _, _, .commit cellName owner fresh guard k, utility, profile, premise, config => by
      have hkernel : commitKernel (Function.update profile who
          ((profile who).forceDisclose (.commit cellName owner fresh guard k))) =
            commitKernel profile := by
        by_cases hown : owner = who
        · subst hown; simp [commitKernel, BehavioralPolicy.forceDisclose]
        · simp [commitKernel, Function.update_of_ne hown]
      rw [runFrom_commit, runFrom_commit, hkernel, afterCommit_update,
        FinDist.expect_bind, FinDist.expect_bind]
      exact FinDist.expect_mono fun choice _ =>
        forceDisclose_expect_le k utility (afterCommit profile) premise _
  | _, _, .reveal published owner name fresh source unresolved k,
      utility, profile, premise, config => by
      have step := fun (disclose : Bool) =>
        forceDisclose_expect_le k utility (afterReveal profile) premise.2
          (revealSuccessor published source config disclose)
      rw [runFrom_reveal, runFrom_reveal, afterReveal_update, FinDist.expect_bind,
        FinDist.expect_bind]
      by_cases hown : owner = who
      · subst hown
        have hforced : revealKernel (Function.update profile owner
            ((profile owner).forceDisclose
              (.reveal published owner name fresh source unresolved k))) =
              fun _ => FinDist.pure true := by
          simp [revealKernel, BehavioralPolicy.forceDisclose]
        rw [hforced]
        refine le_trans (FinDist.expect_mono fun disclose _ => step disclose) ?_
        simp only [FinDist.expect_pure]
        have hshape : ∀ stops : Bool,
            (if stops then
              runFrom k (Function.update (afterReveal profile) owner
                ((afterReveal profile owner).forceDisclose k))
                (revealSuccessor published source config false)
            else
              runFrom k (Function.update (afterReveal profile) owner
                ((afterReveal profile owner).forceDisclose k))
                (revealSuccessor published source config true)) =
              runFrom k (Function.update (afterReveal profile) owner
                ((afterReveal profile owner).forceDisclose k))
                (revealSuccessor published source config !stops) := by
          intro stops; cases stops <;> rfl
        have general := FinDist.selective_stopping_le (FinDist.pure (α := Unit) ())
          (fun _ => (revealKernel profile (Config.view owner config)).map not)
          (fun _ => runFrom k (Function.update (afterReveal profile) owner
            ((afterReveal profile owner).forceDisclose k))
            (revealSuccessor published source config false))
          (fun _ => runFrom k (Function.update (afterReveal profile) owner
            ((afterReveal profile owner).forceDisclose k))
            (revealSuccessor published source config true))
          utility (fun _ _ _ => premise.1 rfl config)
        simp only [FinDist.pure_bind, FinDist.bind_map, hshape, Bool.not_not,
          FinDist.expect_bind] at general
        exact general
      · have hkernel : revealKernel (Function.update profile who
            ((profile who).forceDisclose
              (.reveal published owner name fresh source unresolved k))) =
              revealKernel profile := by
          simp [revealKernel, Function.update_of_ne hown]
        rw [hkernel]
        exact FinDist.expect_mono fun disclose _ => step disclose

/-- The same across a private setup law. The premise does not mention the draw,
so one comparison per decision serves every branch. -/
theorem forceDisclose_run_expect_le {who : Player} (setup : Setup (Player := Player) (L := L))
    (utility : State L (terminalCtx setup.program) → ℝ)
    (profile : BehavioralProfile setup.program)
    (premise : DisclosesProfitably setup.program utility profile (profile who)) :
    (setup.run profile).expect utility ≤
      (setup.run (Function.update profile who
        ((profile who).forceDisclose setup.program))).expect utility := by
  simp only [Setup.run, FinDist.expect_bind]
  exact FinDist.expect_mono fun initial _ =>
    forceDisclose_expect_le setup.program utility profile premise
      ⟨initial, [], Revelations.initial setup.context, fun _ => []⟩

/-- So under that premise the player gives up nothing by joining the class that
never refuses. This is the conditional an honest-play layer states: not that
compilation preserves the class, which it cannot, but that a player who prefers
opening at every decision loses nothing by being held to it. -/
theorem exists_disclosing_expect_le {who : Player} (setup : Setup (Player := Player) (L := L))
    (utility : State L (terminalCtx setup.program) → ℝ)
    (profile : BehavioralProfile setup.program)
    (premise : DisclosesProfitably setup.program utility profile (profile who)) :
    ∃ alternative : BehavioralPolicy who setup.program,
      Disclosing setup.program alternative ∧
        (setup.run profile).expect utility ≤
          (setup.run (Function.update profile who alternative)).expect utility :=
  ⟨(profile who).forceDisclose setup.program,
    disclosing_forceDisclose setup.program (profile who),
    forceDisclose_run_expect_le setup utility profile premise⟩

end Vegas.SourceProgram
