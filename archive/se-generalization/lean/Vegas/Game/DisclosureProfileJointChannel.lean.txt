/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.DisclosureProfileRetraction

/-! # Correlated initial parameters and the common source-prefix channel

The actual simultaneous memory lottery retains the initial parameter and the
same auxiliary channel draw together with all original private histories.
The law integrates the fixed-configuration source channel over the correlated
initial law; it makes no claim about a native input likelihood or posterior.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}

/-- The common source-prefix channel preserves the same initial parameter,
original state, and channel draw under an arbitrary correlated initial law.
Only the source normalizer's static registry and revelation positions are
fixed on initial support. The channel reads only the focal effective view. -/
theorem normalizeDisclosureProfile_prefix_channel_joint_law {Parameter Noise : Type}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (belief : PMF (Config Player L Γ))
    (registryEq : ∀ config ∈ belief.support, config.registry = registry)
    (revelationsEq : ∀ config ∈ belief.support, @config.revelations = @revelations)
    (parameter : Config Player L Γ → Parameter) (count : Nat) (focal : Player)
    (noise : ProtocolView focal program → PMF Noise) :
    (belief.bind fun config =>
      ((fun law => law.bind (ProtocolState.behavioralStateStep program
        (normalizeDisclosureProfile program registry revelations profile)))^[count]
          (PMF.pure (ProtocolState.entry program config))).bind fun state =>
            (noise (ProtocolState.observe focal program state)).bind
              fun extra => (profile.restoreDisclosureMemory program registry revelations
                state).map fun original => (parameter config, original, extra)) =
      belief.bind fun config =>
        ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count]
          (PMF.pure (ProtocolState.entry program config))).bind fun original =>
            (noise (ProtocolView.normalizeDisclosureRecall program (fun view => view.2)
              (ProtocolState.observe focal program original))).map
                  fun extra => (parameter config, original, extra) := by
  apply bind_congr_on_support _
  intro config supported
  have law := normalizeDisclosureProfile_prefix_channel program profile config count focal
    noise
  rw [registryEq config supported, revelationsEq config supported] at law
  have retained := congrArg
    (PMF.map (fun selected => (parameter config, selected.1, selected.2))) law
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def] using retained

end Vegas.SourceProgram
