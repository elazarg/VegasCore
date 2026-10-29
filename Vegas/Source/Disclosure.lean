/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Semantics
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

/-- A policy that never refuses an active disclosure. An honest policy also
submits a value at every active commitment. -/
def Disclosing {who : Player} : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → BehavioralPolicy who p → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample _ _ _ k, policy => Disclosing k policy
  | _, _, .commit _ _ _ _ k, policy => Disclosing k policy.2
  | _, _, .reveal _ owner _ _ _ _ k, policy =>
      (∀ (own : owner = who) view active, false ∉ (policy.1 own view active).support) ∧
        Disclosing k policy.2

/-- Open at every own reveal, and leave every binding alone. -/
def BehavioralPolicy.forceDisclose {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    BehavioralPolicy who p → BehavioralPolicy who p
  | _, _, .ret _, _ => PUnit.unit
  | _, _, .sample _ _ _ k, policy => forceDisclose k policy
  | _, _, .commit _ _ _ _ k, policy => (policy.1, forceDisclose k policy.2)
  | _, _, .reveal _ _ _ _ _ _ k, policy =>
      (fun _ _ _ => PMF.pure true, forceDisclose k policy.2)

theorem disclosing_forceDisclose {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    (policy : BehavioralPolicy who p) → Disclosing p (policy.forceDisclose p)
  | _, _, .ret _, _ => trivial
  | _, _, .sample _ _ _ k, policy => disclosing_forceDisclose k policy
  | _, _, .commit _ _ _ _ k, policy => disclosing_forceDisclose k policy.2
  | _, _, .reveal _ _ _ _ _ _ k, policy =>
      ⟨fun _ _ _ => by simp [BehavioralPolicy.forceDisclose], disclosing_forceDisclose k policy.2⟩

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
          (revealSuccessor published source config false)) (fun final => utility final.state) ≤
        expect (runFrom k (Function.update (afterReveal profile) who
            ((afterReveal profile who).forceDisclose k))
          (revealSuccessor published source config true)) (fun final => utility final.state)) ∧
        DisclosesProfitably k utility (afterReveal profile) policy.2


end Vegas.SourceProgram
