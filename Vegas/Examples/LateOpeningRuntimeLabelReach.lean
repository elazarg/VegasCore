/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLabelKernels
import GameTheoryExtensions.Math.Probability.Support

/-! # Actual native execution laws along private-label history orbits -/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeLabelReach

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLabelTrace
open LateOpeningRuntimeLabelOrbits LateOpeningRuntimeLabelKernels

variable (horizon : Nat) (scheduler : app.Scheduler)
local notation "M" => rawMenu.information initial horizon scheduler
local notation "E" => rawMenu.protocol initial horizon scheduler

def permuteJoint (permutation : Equiv.Perm (Fin 3)) (history : (E).History)
    (joint : {joint : Player → Option app.Action // (E).Legal history.state joint}) :
    {joint : Player → Option app.Action //
      (E).Legal (permuteHistory horizon scheduler permutation history).state joint} :=
  ⟨joint.1, rawMenu_legal_permutation permutation horizon scheduler history.state joint.1 joint.2⟩

theorem behavioralJoint_permutation (permutation : Equiv.Perm (Fin 3))
    (profile : ∀ who, (M).BehavioralPolicy who)
    (uniformAlice : (profile alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice))
    (history : (E).History) (nonterminal : ¬ (E).terminal history.state) :
    ((M).behavioralJoint profile history.trace nonterminal).map
        (permuteJoint horizon scheduler permutation history) =
      (M).behavioralJoint profile
        (permuteHistory horizon scheduler permutation history).trace (by
          change ¬ app.terminal (permuteProtocolState permutation history.state)
          rw [permuteProtocolState_terminal]
          exact nonterminal) := by
  apply pmf_map_injective Subtype.val_injective
  rw [PMF.map_comp]
  change ((M).behavioralJoint profile history.trace nonterminal).map Subtype.val = _
  exact (behavioralJoint_raw_permutation horizon scheduler permutation profile uniformAlice
    history nonterminal).symm

theorem step_permutation (permutation : Equiv.Perm (Fin 3)) (history : (E).History)
    (joint : {joint : Player → Option app.Action // (E).Legal history.state joint}) :
    ((E).step history.state joint).map (permuteProtocolState permutation) =
      (E).step (permuteHistory horizon scheduler permutation history).state
        (permuteJoint horizon scheduler permutation history joint) :=
  permuteProtocolState_transition permutation horizon scheduler history.state joint.1


theorem stepHistory_permutation (permutation : Equiv.Perm (Fin 3)) (history : (E).History)
    (joint : {joint : Player → Option app.Action // (E).Legal history.state joint}) :
    (((E).step history.state joint).bindOnSupport fun _target supported =>
      PMF.pure (history.extend joint.2 supported)).map
        (permuteHistory horizon scheduler permutation) =
      ((E).step (permuteHistory horizon scheduler permutation history).state
        (permuteJoint horizon scheduler permutation history joint)).bindOnSupport
          fun _target supported => PMF.pure
            ((permuteHistory horizon scheduler permutation history).extend
              (permuteJoint horizon scheduler permutation history joint).2 supported) := by
  rw [map_bindOnSupport]
  simp only [PMF.pure_map]
  trans (((E).step history.state joint).map (permuteProtocolState permutation)).bindOnSupport
    (fun _target supported => PMF.pure
      ((permuteHistory horizon scheduler permutation history).extend
        (permuteJoint horizon scheduler permutation history joint).2 (by
          rw [step_permutation] at supported
          exact supported)))
  · rw [bindOnSupport_map]
    apply bindOnSupport_congr
    intro target supported
    rfl
  · apply bindOnSupport_congr_measure (step_permutation horizon scheduler permutation history joint)
    intro target firstSupport secondSupport
    rfl

theorem runBehavioralFrom_one_permutation (permutation : Equiv.Perm (Fin 3))
    (profile : ∀ who, (M).BehavioralPolicy who)
    (uniformAlice : (profile alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice)) (history : (E).History) :
    ((M).runBehavioralFrom profile 1 history).map
        (permuteHistory horizon scheduler permutation) =
      (M).runBehavioralFrom profile 1
        (permuteHistory horizon scheduler permutation history) := by
  unfold InformationModel.runBehavioralFrom
  by_cases stopped : (E).terminal history.state
  · have changed : (E).terminal
        (permuteHistory horizon scheduler permutation history).state := by
      change app.terminal (permuteProtocolState permutation history.state)
      rw [permuteProtocolState_terminal]
      exact stopped
    rw [ExecutionProtocol.runRandomizedFor_of_terminal _ _ stopped,
      ExecutionProtocol.runRandomizedFor_of_terminal _ _ changed, PMF.pure_map]
  · have changed : ¬ (E).terminal
        (permuteHistory horizon scheduler permutation history).state := by
      change ¬ app.terminal (permuteProtocolState permutation history.state)
      rw [permuteProtocolState_terminal]
      exact stopped
    rw [ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ 0 stopped,
      ExecutionProtocol.runRandomizedFor_succ_of_not_terminal _ 0 changed, PMF.map_bind]
    simp only [ExecutionProtocol.runRandomizedFor_zero, InformationModel.randomizedChooser]
    rw [← behavioralJoint_permutation horizon scheduler permutation profile uniformAlice
      history stopped, PMF.bind_map]
    apply bind_congr_on_support
    intro joint _
    exact stepHistory_permutation horizon scheduler permutation history joint

theorem runBehavioralFrom_permutation (permutation : Equiv.Perm (Fin 3))
    (profile : ∀ who, (M).BehavioralPolicy who)
    (uniformAlice : (profile alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice))
    (fuel : Nat) (history : (E).History) :
    ((M).runBehavioralFrom profile fuel history).map
        (permuteHistory horizon scheduler permutation) =
      (M).runBehavioralFrom profile fuel
        (permuteHistory horizon scheduler permutation history) :=
  (E).runRandomizedFor_map_of_oneStep ((M).randomizedChooser profile)
    ((M).randomizedChooser profile)
    (permuteHistory horizon scheduler permutation)
    (runBehavioralFrom_one_permutation horizon scheduler permutation profile uniformAlice)
    fuel history


theorem runBehavioral_permutation (permutation : Equiv.Perm (Fin 3))
    (profile : ∀ who, (M).BehavioralPolicy who)
    (uniformAlice : (profile alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice)) (fuel : Nat) :
    ((M).runBehavioral profile fuel).map (permuteHistory horizon scheduler permutation) =
      (M).runBehavioral profile fuel :=
  runBehavioralFrom_permutation horizon scheduler permutation profile uniformAlice fuel
    (E).initHistory

theorem historyReachWeight_permutation (permutation : Equiv.Perm (Fin 3))
    (profile : ∀ who, (M).BehavioralPolicy who)
    (uniformAlice : (profile alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice)) (history : (E).History) :
    (M).historyReachWeight profile (permuteHistory horizon scheduler permutation history) =
      (M).historyReachWeight profile history := by
  unfold InformationModel.historyReachWeight
  change ((M).runBehavioral profile
    ((permuteTrace permutation horizon scheduler history.trace).length))
      (permuteHistory horizon scheduler permutation history) = _
  rw [permuteTrace_length]
  have mass := pmf_map_apply_of_injective
    (f := permuteHistory horizon scheduler permutation)
    ((M).runBehavioral profile history.trace.length)
    (historyEquiv horizon scheduler permutation).injective history
  rw [runBehavioral_permutation horizon scheduler permutation profile uniformAlice] at mass
  exact mass

end Vegas.Examples.LateOpeningRuntimeLabelReach
