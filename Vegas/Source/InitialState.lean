/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Setup

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
      simp only [runFrom_sample, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨value, _, supported⟩ := supported
      have h := ih (afterSample profile) (sampleSuccessor name config value) outcome supported
      funext x cell member
      exact congrArg (fun env => env.get (.there member)) h
  | commit name owner fresh guard k ih =>
      simp only [runFrom_commit, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨value, _, supported⟩ := supported
      have h := ih (afterCommit profile) (commitSuccessor name guard config value) outcome supported
      funext x cell member
      exact congrArg (fun env => env.get (.there member)) h
  | reveal published owner name fresh source unresolved k ih =>
      simp only [runFrom_reveal, FinDist.support_bind, Set.mem_iUnion] at supported
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
    FinDist (Parameter × PublicOutcome setup.program) :=
  setup.initialLaw.bind fun initial =>
    (SourceProgram.run setup.program profile initial).map fun terminal =>
      (parameter initial, publicOutcome setup.program terminal)

/-- Forgetting the analysis parameter recovers exactly the public source game. -/
theorem parameterRun_map_snd {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (profile : BehavioralProfile setup.program) :
    (setup.parameterRun parameter profile).map Prod.snd = setup.publicRun profile := by
  simp only [parameterRun, publicRun, run, FinDist.map_bind, FinDist.map_comp,
    Function.comp_def]

/-- The joint law is a semantic projection of the full-store law. -/
theorem run_map_parameterOutcome {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter)
    (profile : BehavioralProfile setup.program) :
    (setup.run profile).map (setup.parameterOutcome parameter) =
      setup.parameterRun parameter profile := by
  simp only [run, parameterRun, FinDist.map_bind]
  apply FinDist.bind_congr
  intro initial _
  apply FinDist.map_congr_of_eq_on_support
  intro terminal supported
  unfold parameterOutcome
  rw [initialState_runFrom setup.program profile
    ⟨initial, [], Revelations.initial setup.context, fun _ => []⟩ terminal supported]

/-- A game interpretation for utilities of private initial parameters and public
results. Its strategy space and information restrictions are unchanged. -/
@[reducible] def parameterGame {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (parameter : State L setup.context → Parameter) : GameForm Player where
  sig :=
    { Strategy := fun who => BehavioralPolicy who setup.program
      Outcome := Parameter × PublicOutcome setup.program }
  play := setup.parameterRun parameter

end Setup
end Vegas.SourceProgram
