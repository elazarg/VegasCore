/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceContinuation
import GameTheory.Core.Approximate
import GameTheory.Protocol.Strategic

/-! # Nash correspondence between source policies and protocol strategies

The existing policy equivalence preserves payoff laws uniformly over the
initial draw. Restricting commitment admission preserves full-source equilibria;
when every source policy is admitted, the correspondence also reflects them.
The proofs retain extended expected utility and need no boundedness assumption.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (admission : CommitmentInterface setup.program)

/-- Encode admitted source policies without changing their observation-local laws. -/
def encodeBehavioralProfile (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission) :
    Profile (setup.informationModel admission).behavioralSignature :=
  fun who => setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who)

omit [Fintype Player] in
@[simp] theorem decodeBehavioralProfile_encodeBehavioralProfile
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission) :
    setup.decodeBehavioralProfile admission
      (setup.encodeBehavioralProfile admission profile permitted) = profile := by
  funext who
  exact congrArg Subtype.val ((setup.behavioralPolicyEquiv admission who).symm_apply_apply
    ⟨profile who, permitted who⟩)

omit [Fintype Player] in
/-- Arbitrary legal protocol deviations change exactly the corresponding source policy. -/
theorem decodeBehavioralProfile_protocol_update
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (who : Player) (replacement : (setup.informationModel admission).BehavioralPolicy who) :
    setup.decodeBehavioralProfile admission (Profile.update profile who replacement) =
      Function.update (setup.decodeBehavioralProfile admission profile) who
        (((setup.behavioralPolicyEquiv admission who).symm replacement).1) := by
  funext player
  by_cases same : player = who
  · subst player
    simp only [decodeBehavioralProfile, Profile.update, Function.update_self]
  · simp only [decodeBehavioralProfile, Profile.update, Function.update_of_ne same]

omit [Fintype Player] in
/-- An analysis projection of the existing typed execution; source strategies
and observations are unchanged. -/
def observedGameForm {Observation : Type}
    (readout : State L setup.program.terminalCtx → Observation) : GameForm Player where
  sig := (SourceProgram.gameSignature setup.program).mapOutcome Observation
  play profile := (setup.run profile).map readout

variable {Observation : Type}
  (readout : State L setup.program.terminalCtx → Observation)

/-- The whole utility-vector law agrees for every protocol profile, not only
encoded equilibria. Undefined and infinite expectations are therefore preserved. -/
theorem protocol_payoff_law
    (utility : Observation → Player → ℝ)
    (profile : Profile (setup.informationModel admission).behavioralSignature) :
    ((setup.informationModel admission).runBehavioral profile
      (instructionCount setup.program + 1)).map
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun terminal => utility (readout terminal) who)) =
    ((setup.observedGameForm readout).play
      (setup.decodeBehavioralProfile admission profile)).map utility := by
  have law :
      ((setup.informationModel admission).runBehavioral profile
        (instructionCount setup.program + 1)).map
        (fun final => setup.protocolReadout final.state) =
      (setup.run (setup.decodeBehavioralProfile admission profile)).map some :=
    setup.runBehavioralFrom_readout admission profile _ _ (Nat.le_refl _)
  have valued := congrArg (PMF.map (fun output : Option (State L setup.program.terminalCtx) =>
    fun who => output.elim 0 (fun terminal => utility (readout terminal) who)))
    law
  simpa only [PMF.map_comp, Function.comp_def, Option.elim_some, observedGameForm] using valued

/-- The existing policy equivalence transports the exact expected-utility
preference, including its expectation-existence guards and additive Nash error. -/
theorem protocol_euPreferenceWithin_iff
    (utility : Observation → Player → ℝ) (ε : ℝ) (who : Player)
    (first second : Profile (setup.informationModel admission).behavioralSignature) :
    euPreferenceWithin ε
      (fun final owner => (setup.protocolReadout final.state).elim 0
        (fun terminal => utility (readout terminal) owner)) who
      ((setup.informationModel admission).runBehavioral first
        (instructionCount setup.program + 1))
      ((setup.informationModel admission).runBehavioral second
        (instructionCount setup.program + 1)) ↔
    euPreferenceWithin ε utility who
      ((setup.observedGameForm readout).play (setup.decodeBehavioralProfile admission first))
      ((setup.observedGameForm readout).play (setup.decodeBehavioralProfile admission second)) := by
  have has (profile : Profile (setup.informationModel admission).behavioralSignature) :=
    hasExpectation_observed_law_iff _ _ _ _ (fun values : Player → ℝ => values who)
      (setup.protocol_payoff_law admission readout utility profile)
  have value (profile : Profile (setup.informationModel admission).behavioralSignature) :
      extendedExpectedUtility
        (fun final owner => (setup.protocolReadout final.state).elim 0
          (fun terminal => utility (readout terminal) owner)) who
        ((setup.informationModel admission).runBehavioral profile
          (instructionCount setup.program + 1)) =
      extendedExpectedUtility utility who
        ((setup.observedGameForm readout).play (setup.decodeBehavioralProfile admission profile)) :=
    extendedExpect_observed_law_eq _ _ _ _ (fun values : Player → ℝ => values who)
      (setup.protocol_payoff_law admission readout utility profile)
  exact and_congr (has first) (and_congr (has second) (by rw [value first, value second]))

/-- Admission may remove source deviations, so a full-source equilibrium remains
an equilibrium of the protocol whenever its own policies are admitted. -/
theorem protocol_isεNash_of_decoded
    (utility : Observation → Player → ℝ) (ε : ℝ)
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (equilibrium : IsεNash (setup.observedGameForm readout) utility ε
      (setup.decodeBehavioralProfile admission profile)) :
    IsεNash ((setup.informationModel admission).toBehavioralGameForm
        (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun terminal => utility (readout terminal) who)) ε profile := by
  rw [IsεNash, isNash_iff] at equilibrium ⊢
  intro who replacement
  apply (setup.protocol_euPreferenceWithin_iff admission readout utility ε who profile
    (Profile.update profile who replacement)).2
  rw [setup.decodeBehavioralProfile_protocol_update]
  exact equilibrium who _

/-- If admission permits every source policy, the same-error Nash correspondence
is an equivalence against all policies on both sides. -/
theorem protocol_isεNash_iff
    (allAdmitted : ∀ who (policy : BehavioralPolicy who setup.program),
      policy.Admitted setup.program admission)
    (utility : Observation → Player → ℝ) (ε : ℝ)
    (profile : Profile (setup.informationModel admission).behavioralSignature) :
    IsεNash ((setup.informationModel admission).toBehavioralGameForm
        (instructionCount setup.program + 1))
      (fun final who => (setup.protocolReadout final.state).elim 0
        (fun terminal => utility (readout terminal) who)) ε profile ↔
    IsεNash (setup.observedGameForm readout) utility ε
      (setup.decodeBehavioralProfile admission profile) := by
  constructor
  · intro equilibrium
    rw [IsεNash, isNash_iff] at equilibrium ⊢
    intro who replacement
    have compared := (setup.protocol_euPreferenceWithin_iff admission readout utility ε who profile
      (Profile.update profile who (setup.toProtocolBehavioralPolicy admission who replacement
        (allAdmitted who replacement)))).1 (equilibrium who _)
    have decoded := setup.decodeBehavioralProfile_update admission profile who replacement
      (allAdmitted who replacement)
    change setup.decodeBehavioralProfile admission
        (Profile.update profile who (setup.toProtocolBehavioralPolicy admission who replacement
          (allAdmitted who replacement))) = _ at decoded
    rw [decoded] at compared
    exact compared
  · exact setup.protocol_isεNash_of_decoded admission readout utility ε profile

end Vegas.SourceProgram.Setup
