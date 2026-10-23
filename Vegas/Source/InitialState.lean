/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Setup
import GameTheoryExtensions.Math.Probability.Support

/-! # Initial parameters and public results

Execution extends an immutable source environment. Its initial fields can
therefore be recovered from the terminal store without retaining later private
commitment choices in the analysis outcome. Pairing those parameters with the
public result preserves their correlation; it grants no additional observations
to a policy and adds no publication to the program.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Recover the immutable initial environment from the complete terminal store. -/
def initialState : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (p : SourceProgram Player L Γ O) → State L p.terminalCtx → State L Γ
  | _, _, .ret _, state => state
  | _, _, .sample _ _ _ k, state => fun _ _ h => (initialState k state).get (.there h)
  | _, _, .commit _ _ _ _ k, state => fun _ _ h => (initialState k state).get (.there h)
  | _, _, .reveal _ _ _ _ _ _ k, state => fun _ _ h => (initialState k state).get (.there h)

/-- Every supported execution retains the initial environment exactly. -/
theorem initialState_runFrom {Γ : SourceCtx Player L} {O : Finset VarId}
    (p : SourceProgram Player L Γ O) (profile : BehavioralProfile p)
    (config : Config Player L Γ) (outcome : State L p.terminalCtx)
    (supported : outcome ∈ (runFrom p profile config).support) :
    initialState p outcome = config.state := by
  induction p with
  | ret payoffs =>
      simpa [runFrom, runWith, initialState] using supported
  | sample name fresh law k ih =>
      simp only [runFrom_sample, PMF.support_bind, Set.mem_iUnion] at supported
      obtain ⟨value, _, supported⟩ := supported
      have h := ih (afterSample profile) (sampleSuccessor name config value) outcome supported
      funext x cell member
      exact congrArg (fun env => env.get (.there member)) h
  | commit name owner fresh guard k ih =>
      simp only [runFrom_commit, PMF.support_bind, Set.mem_iUnion] at supported
      obtain ⟨value, _, supported⟩ := supported
      have h := ih (afterCommit profile) (commitSuccessor name guard config value) outcome supported
      funext x cell member
      exact congrArg (fun env => env.get (.there member)) h
  | reveal published owner name fresh source unresolved k ih =>
      simp only [runFrom_reveal, PMF.support_bind, Set.mem_iUnion] at supported
      obtain ⟨disclose, _, supported⟩ := supported
      have h := ih (afterReveal profile) (revealSuccessor published source config disclose)
        outcome supported
      funext x cell member
      exact congrArg (fun env => env.get (.there member)) h

namespace Setup

/-- The analysis outcome contains an exogenous parameter and the public result.
The parameter reader is fixed before play and never reads newly chosen bindings. -/
def parameterOutcome {Parameter : Type} (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (terminal : State L setup.program.terminalCtx) :
    Parameter × PublicOutcome setup.program :=
  (parameter (initialState setup.program terminal), publicOutcome setup.program terminal)

/-- Draw the initial state once and retain its parameter jointly with the result. -/
def parameterRun {Parameter : Type} (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (profile : BehavioralProfile setup.program) :
    PMF (Parameter × PublicOutcome setup.program) :=
  setup.initialLaw.bind fun initial =>
    (SourceProgram.run setup.program profile initial).map fun terminal =>
      (parameter initial, publicOutcome setup.program terminal)

/-- The joint law is a semantic projection of the full-store law. -/
theorem run_map_parameterOutcome {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (profile : BehavioralProfile setup.program) :
    (setup.run profile).map (setup.parameterOutcome parameter) =
      setup.parameterRun parameter profile := by
  simp only [run, parameterRun, PMF.map_bind]
  apply bind_congr_on_support _
  intro initial _
  apply map_congr_on_support _
  intro terminal supported
  unfold parameterOutcome
  rw [initialState_runFrom setup.program profile
    ⟨initial, [], Revelations.initial setup.context, fun _ => []⟩ terminal supported]

end Setup
end Vegas.SourceProgram
