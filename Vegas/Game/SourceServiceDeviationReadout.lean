/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceLaw

/-! # Typed outcome of a permitted deviation

Against the timed calendar profile of a source profile, every unilateral
deviation within the permitted menu has the typed terminal-state law of a
single source deviation of the same player, admitted at the commitment
interface. Private-intention normalization of the other players is undone by
the existing normalization theorem.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
/-- Replacing one player's policy commutes with the other players' private
intention normalization: the source law is unchanged. -/
theorem run_update_normalizeDisclosureProfile [Finite Player]
    (setup : Setup (Player := Player) (L := L)) (original : BehavioralProfile setup.program)
    (who : Player) (policy : BehavioralPolicy who setup.program) :
    setup.run (Function.update (normalizeDisclosureProfile setup.program []
      (Revelations.initial setup.context) original) who policy) =
      setup.run (Function.update original who policy) := by
  unfold Setup.run
  apply bind_congr_on_support _
  intro initial _
  let config := Config.initial initial
  let normalized := normalizeDisclosureProfile setup.program []
    (Revelations.initial setup.context) original
  have own := normalizeDisclosures_runFrom setup.program
    (Function.update normalized who policy) policy config
  rw [Function.update_idem, Function.update_idem] at own
  have profiles : Function.update normalized who
      (policy.normalizeDisclosures setup.program config.registry config.revelations) =
      normalizeDisclosureProfile setup.program config.registry config.revelations
        (Function.update original who policy) := by
    funext player
    by_cases same : player = who
    · subst player
      simp only [Function.update_self, normalizeDisclosureProfile]
    · simp only [Function.update_of_ne same, normalized, normalizeDisclosureProfile, config,
        Config.initial]
  change SourceProgram.run setup.program (Function.update normalized who policy) initial =
    SourceProgram.run setup.program (Function.update original who policy) initial
  unfold SourceProgram.run
  change runFrom setup.program (Function.update normalized who policy) config =
    runFrom setup.program (Function.update original who policy) config
  rw [← own, profiles, normalizeDisclosureProfile_runFrom]

end Vegas
