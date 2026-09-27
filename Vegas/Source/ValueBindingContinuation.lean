/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ValueBinding
import Vegas.Source.Purification
import Vegas.Source.ProtocolBehavioralPolicy

/-! # Value-only binding from an arbitrary source continuation

The replacement of an unusable binding by a value plus later withholding works
from a residual configuration, with its existing registry, revelations and own
action histories intact. One mixture serves every configuration in an arbitrary
finite belief, preserving correlations with any parameter of that configuration.

These are conditional source deviation laws. They do not identify native
opponents' observations, construct consistent native beliefs, or prove a native
sequential-equilibrium extension.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId} {who : Player}

omit [IExpr.ResultTypes L] in
theorem Patched.refl (state : State L Γ) (history : History Player L) :
    Patched (who := who) id (fun _ _ => false) state state history history where
  publicEq := fun _ => rfl
  inputEq := fun _ => rfl
  publicationEq := fun _ => rfl
  foreignEq := fun _ _ => rfl
  replacedEq := fun _ impossible => by contradiction
  keptEq := fun _ _ => rfl
  historyEq := fun _ _ => rfl
  unpatchEq := rfl

/-- The repaired continuation is legal under every commitment interface. -/
theorem ValueBinding.admitted :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (policy : BehavioralPolicy who program) → ValueBinding program policy →
    (admission : CommitmentInterface program) → policy.Admitted program admission
  | _, _, .ret _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, policy, valid, admission =>
      valid.admitted next policy admission
  | _, _, .commit _ _ _ _ next, policy, valid, admission => by
      refine ⟨?_, valid.2.admitted next policy.2 (fun site => admission (some site))⟩
      intro owned view choice supported
      cases choice with
      | failure => exact (valid.1 owned view supported).elim
      | success value => trivial
  | _, _, .reveal _ _ _ _ _ _ next, policy, valid, admission =>
      valid.admitted next policy.2 admission

/-- No initialization or reset of the existing action histories is involved. -/
theorem bindValues_runFrom_publicOutcome_eq
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (policy : PurePolicy who program) (config : Config Player L Γ) :
    (runFrom program (Function.update profile who (PurePolicy.toBehavioral program
      (PurePolicy.bindValues program policy))) config).map (publicOutcome program) =
      (runFrom program (Function.update profile who (PurePolicy.toBehavioral program policy))
        config).map (publicOutcome program) :=
  bindValues_publicOutcome_eq program id (fun _ _ => false) policy _ _
    (fun other different => by simp only [Function.update_of_ne different])
    (Function.update_self ..) (Function.update_self ..)
    config.state config.state config.registry config.revelations config.history config.history
    (Patched.refl config.state config.history)

/-- Every behavioral continuation has one value-binding mixture shared across
all listed hidden configurations. Opponents' source policies remain unchanged. -/
theorem exists_valueBinding_continuation_mixture
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (replacement : BehavioralPolicy who program) (configs : List (Config Player L Γ)) :
    ∃ mixture : FinDist (ValueBindingPolicy who program), ∀ config ∈ configs,
      (runFrom program (Function.update profile who replacement) config).map
          (publicOutcome program) =
        mixture.bind fun alternative =>
          (runFrom program (Function.update profile who alternative.1) config).map
            (publicOutcome program) := by
  obtain ⟨mixture, law⟩ := exists_pureMixture program profile replacement configs
  refine ⟨mixture.map (fun policy =>
    ⟨PurePolicy.toBehavioral program (PurePolicy.bindValues program policy),
      valueBinding_bindValues program policy⟩), ?_⟩
  intro config member
  rw [law config member, FinDist.map_bind, FinDist.bind_map]
  exact FinDist.bind_congr fun policy _ =>
    (bindValues_runFrom_publicOutcome_eq program profile policy config).symm

/-- The mixing draw precedes the hidden configuration draw. The readout can
retain private types or any other initial parameter jointly with public results. -/
theorem exists_valueBinding_belief_mixture {Parameter : Type}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (replacement : BehavioralPolicy who program) (belief : FinDist (Config Player L Γ))
    (parameter : Config Player L Γ → Parameter) :
    ∃ mixture : FinDist (ValueBindingPolicy who program),
      (belief.bind fun config =>
        (runFrom program (Function.update profile who replacement) config).map
          (fun result => (parameter config, publicOutcome program result))) =
      mixture.bind fun alternative => belief.bind fun config =>
        (runFrom program (Function.update profile who alternative.1) config).map
          (fun result => (parameter config, publicOutcome program result)) := by
  classical
  obtain ⟨mixture, law⟩ := exists_valueBinding_continuation_mixture program profile replacement
    belief.supportFinset.toList
  refine ⟨mixture, ?_⟩
  rw [FinDist.bind_comm]
  apply FinDist.bind_congr
  intro config supported
  have equality := congrArg (FinDist.map fun result => (parameter config, result))
    (law config (Finset.mem_toList.mpr (FinDist.mem_supportFinset.mpr supported)))
  simpa only [FinDist.map_comp, Function.comp_def, FinDist.map_bind] using equality

/-- Hidden inability to open cannot increase the conditional best-response
value when opponents retain their source observations and policies. This is
stronger than an initial Nash comparison, and still weaker than native SE. -/
theorem exists_valueBinding_continuation_ge {Parameter : Type}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (replacement : BehavioralPolicy who program) (belief : FinDist (Config Player L Γ))
    (parameter : Config Player L Γ → Parameter)
    (utility : Parameter × PublicOutcome program → ℝ) :
    ∃ alternative : ValueBindingPolicy who program,
      (belief.bind fun config =>
        (runFrom program (Function.update profile who replacement) config).map
          (fun result => (parameter config, publicOutcome program result))).expect utility ≤
      (belief.bind fun config =>
        (runFrom program (Function.update profile who alternative.1) config).map
          (fun result => (parameter config, publicOutcome program result))).expect utility := by
  obtain ⟨mixture, law⟩ := exists_valueBinding_belief_mixture program profile replacement
    belief parameter
  rw [law, FinDist.expect_bind]
  obtain ⟨alternative, _, bound⟩ := mixture.exists_expect_le_support (fun alternative =>
    (belief.bind fun config =>
      (runFrom program (Function.update profile who alternative.1) config).map
        (fun result => (parameter config, publicOutcome program result))).expect utility)
  exact ⟨alternative, bound⟩

end Vegas.SourceProgram
