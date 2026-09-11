/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheoryExtensions.Core.QuitTransfer
import Vegas.Compile.SealedCompiler
import Vegas.Core.Strategy

/-! # Strategic certificates for sealed compilation

The operational sealed edge proves prefix and terminal correspondence for
arbitrary native actions. Strategic preservation has one additional, explicit
obligation: a runtime deviation must be backtranslated to a finite mixture of
source deviations. This module gives that obligation a single certificate and
delegates all equilibrium consequences to the generic GameTheory theorem.

The target game is deliberately a parameter. It may be the policy game of the
sealed message application, a timed adapter, or a future blockchain runtime.
The compiler does not silently choose an information model or identify runtime
observations with source outcomes.
-/

noncomputable section

namespace Vegas.SealedCompilation

open GameTheory GameTheory.GameForm GameTheory.Math.Probability

universe uObservation uTargetStrategy uTargetOutcome

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty}

/-- A checked strategic edge from the source game to a target runtime game.
`simulation` contains the exact honest law and the finite-mixture law for every
considered unilateral runtime deviation. -/
structure StrategicCertificate
    (compilation : SealedCompilation source ty)
    {Observation : Type uObservation}
    (target : GameForm.{0, uTargetStrategy, uTargetOutcome} Player)
    (sourceObserve :
      (Vegas.sourceGameForm source.core.prog source.core.env).sig.Outcome → Observation)
    (targetObserve : target.sig.Outcome → Observation)
    (Considered : (who : Player) → target.sig.Strategy who → Prop) where
  simulation : MixtureSimulationOn
    (Vegas.sourceGameForm source.core.prog source.core.env) target
    sourceObserve targetObserve Considered

namespace StrategicCertificate

variable {compilation : SealedCompilation source ty}
variable {Observation : Type uObservation}
variable {target : GameForm.{0, uTargetStrategy, uTargetOutcome} Player}
variable {sourceObserve :
  (Vegas.sourceGameForm source.core.prog source.core.env).sig.Outcome → Observation}
variable {targetObserve : target.sig.Outcome → Observation}
variable {Considered : (who : Player) → target.sig.Strategy who → Prop}
variable (certificate : StrategicCertificate (source := source) (ty := ty)
  (compilation := compilation) target sourceObserve targetObserve Considered)

@[simp] theorem compileProfile_apply
    (profile : Profile (Vegas.sourceGameForm source.core.prog source.core.env).sig)
    (who : Player) :
    certificate.simulation.compileProfile profile who =
      certificate.simulation.compileStrategy who (profile who) :=
  certificate.simulation.compileProfile_apply profile who

theorem expected_utility_guarantee
    (profile : Profile (Vegas.sourceGameForm source.core.prog source.core.env).sig)
    (who : Player) (value : Observation → ℝ) (bound : ℝ)
    (hbound : ∀ alternative :
      (Vegas.sourceGameForm source.core.prog source.core.env).sig.Strategy who,
      bound ≤
        ((Vegas.sourceGameForm source.core.prog source.core.env).play
          (Profile.update profile who alternative)).expect
          (value ∘ sourceObserve))
    (replacement : target.sig.Strategy who)
    (hconsidered : Considered who replacement) :
    bound ≤
      (target.play
        (Profile.update (certificate.simulation.compileProfile profile)
          who replacement)).expect (value ∘ targetObserve) :=
  certificate.simulation.guarantee profile who value bound hbound replacement hconsidered

/-- Exact preservation and reflection of epsilon-Nash equilibrium once the
runtime has supplied its deviation-mixture law. -/
theorem isεNash_compileProfile_iff
    (value : Observation → Player → ℝ) (ε : ℝ)
    (profile : Profile (Vegas.sourceGameForm source.core.prog source.core.env).sig)
    (hall : ∀ who strategy, Considered who strategy) :
    IsεNash target
      (fun outcome who => value (targetObserve outcome) who) ε
      (certificate.simulation.compileProfile profile) ↔
    IsεNash (Vegas.sourceGameForm source.core.prog source.core.env)
      (fun outcome who => value (sourceObserve outcome) who) ε profile :=
  certificate.simulation.isεNash_compileProfile_iff value ε profile hall

theorem isNash_compileProfile_iff
    (value : Observation → Player → ℝ)
    (profile : Profile (Vegas.sourceGameForm source.core.prog source.core.env).sig)
    (hall : ∀ who strategy, Considered who strategy) :
    IsNash target
      (euPreference (fun outcome who => value (targetObserve outcome) who))
      (certificate.simulation.compileProfile profile) ↔
    IsNash (Vegas.sourceGameForm source.core.prog source.core.env)
      (euPreference (fun outcome who => value (sourceObserve outcome) who)) profile :=
  certificate.simulation.isNash_compileProfile_iff value profile hall

/-- A runtime resolution of a quit (including a timeout after malformed traffic
or withholding) with the supplied source-level utility law cannot occur in a
target Nash profile when another source strategy is strictly better. In the
strict sealed kernel, rejection is a stutter; the surrounding resolution edge
is responsible for proving that this stutter has the same source-level law as
the programmer's explicit nullable quit.
-/
theorem compiled_quit_profile_not_isNash_of_quit_law
    (value : Observation → Player → ℝ)
    (profile : Profile (Vegas.sourceGameForm source.core.prog source.core.env).sig)
    (who : Player)
    (quit preferred : SourceBehavioralPolicy source.core.prog who)
    (quitTarget : target.sig.Strategy who)
    (hquit :
      (target.play (Profile.update (certificate.simulation.compileProfile profile)
        who quitTarget)).expect
          (fun outcome => value (targetObserve outcome) who) =
      ((Vegas.sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who quit)).expect
          (fun outcome => value (sourceObserve outcome) who))
    (hstrict :
      ((Vegas.sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who quit)).expect
          (fun outcome => value (sourceObserve outcome) who) <
      ((Vegas.sourceGameForm source.core.prog source.core.env).play
        (Profile.update profile who preferred)).expect
          (fun outcome => value (sourceObserve outcome) who)) :
    ¬ IsNash target
      (euPreference (fun outcome player => value (targetObserve outcome) player))
      (Profile.update (certificate.simulation.compileProfile profile)
        who quitTarget) := by
  intro hnash
  have htargetNash :=
    (isNash_iff (F := target) (weaklyPrefers :=
      euPreference (fun outcome player => value (targetObserve outcome) player))
      (Profile.update (certificate.simulation.compileProfile profile)
        who quitTarget)).1 hnash
  have hpreferredTarget :
      (target.play (Profile.update (certificate.simulation.compileProfile profile)
        who (certificate.simulation.compileStrategy who preferred))).expect
          (fun outcome => value (targetObserve outcome) who) =
        ((Vegas.sourceGameForm source.core.prog source.core.env).play
          (Profile.update profile who preferred)).expect
            (fun outcome => value (sourceObserve outcome) who) := by
    rw [certificate.simulation.compileProfile_update profile who preferred]
    exact certificate.simulation.expect_compile
      (Profile.update profile who preferred)
      (fun observation => value observation who)
  have htargetStrict :
      (target.play (Profile.update (certificate.simulation.compileProfile profile)
        who quitTarget)).expect
          (fun outcome => value (targetObserve outcome) who) <
      (target.play (Profile.update (certificate.simulation.compileProfile profile)
        who (certificate.simulation.compileStrategy who preferred))).expect
          (fun outcome => value (targetObserve outcome) who) := by
    rw [hquit, hpreferredTarget]
    exact hstrict
  have htargetWeak := htargetNash who
    (certificate.simulation.compileStrategy who preferred)
  rw [Profile.update_idem] at htargetWeak
  rw [euPreference_apply] at htargetWeak
  have htargetWeak' :
      (target.play (Profile.update (certificate.simulation.compileProfile profile)
        who (certificate.simulation.compileStrategy who preferred))).expect
          (fun outcome => value (targetObserve outcome) who) ≤
      (target.play (Profile.update (certificate.simulation.compileProfile profile)
        who quitTarget)).expect
          (fun outcome => value (targetObserve outcome) who) := by
    simpa only [expectedUtility] using htargetWeak
  exact (not_lt_of_ge htargetWeak') htargetStrict

end StrategicCertificate

end Vegas.SealedCompilation

/- Guard the public theorem surface against accidental new axioms. -/
/-- info: 'Vegas.SealedCompilation.StrategicCertificate.isεNash_compileProfile_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.StrategicCertificate.isεNash_compileProfile_iff

/-- info: 'Vegas.SealedCompilation.StrategicCertificate.compiled_quit_profile_not_isNash_of_quit_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SealedCompilation.StrategicCertificate.compiled_quit_profile_not_isNash_of_quit_law
