/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.FinDist

/-! # Decisions after retaining an observation

A policy may inspect more information than is retained by an observation map.
Conditioning the policy's action law on each observation gives a behavioral
policy on the retained information alone.  The resulting joint observation and
action law is exact.  Consequently, every fixed continuation kernel depending
only on the retained observation and action has the same outcome law.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {NativeInfo LogicalInfo Action Result : Type*}

/-- The behavioral policy obtained by averaging a native policy over the
native-information states carrying a given logical observation.  At an
off-support observation, `condOnFibre` supplies an irrelevant total fallback. -/
def conditionedPolicy (law : FinDist NativeInfo)
    (observe : NativeInfo → LogicalInfo)
    (policy : NativeInfo → FinDist Action) (observation : LogicalInfo) :
    FinDist Action :=
  (law.condOnFibre observe observation).bind policy

private theorem observe_eq_of_mem_support_condOnFibre
    (law : FinDist NativeInfo) (observe : NativeInfo → LogicalInfo)
    {observation : LogicalInfo}
    (hobservation : observation ∈ (law.map observe).support)
    {native : NativeInfo}
    (hnative : native ∈ (law.condOnFibre observe observation).support) :
    observe native = observation := by
  rw [support_map] at hobservation
  obtain ⟨witness, hwitness, rfl⟩ := hobservation
  have hfibre :
      ∃ value ∈ observe ⁻¹' {observe witness}, value ∈ law.support :=
    ⟨witness, rfl, hwitness⟩
  rw [condOnFibre, dif_pos hfibre] at hnative
  simpa using (support_condOn law _ hfibre hnative).1

/-- Conditioning a policy on the retained observation exactly reproduces the
joint law of that observation and the chosen action. -/
theorem joint_observation_action_eq_bind_conditionedPolicy
    (law : FinDist NativeInfo) (observe : NativeInfo → LogicalInfo)
    (policy : NativeInfo → FinDist Action) :
    law.bind (fun native =>
        (policy native).map fun action => (observe native, action)) =
      (law.map observe).bind fun observation =>
        (conditionedPolicy law observe policy observation).map fun action =>
          (observation, action) := by
  have hdecompose := law.eq_bind_condOnFibre observe
  calc
    law.bind (fun native =>
        (policy native).map fun action => (observe native, action)) =
        ((law.map observe).bind (law.condOnFibre observe)).bind
          (fun native =>
            (policy native).map fun action => (observe native, action)) := by
      rw [← hdecompose]
    _ = (law.map observe).bind fun observation =>
          (law.condOnFibre observe observation).bind fun native =>
            (policy native).map fun action => (observe native, action) := by
      rw [bind_bind]
    _ = (law.map observe).bind fun observation =>
          (conditionedPolicy law observe policy observation).map fun action =>
            (observation, action) := by
      apply bind_congr
      intro observation hobservation
      rw [conditionedPolicy, map_bind]
      apply bind_congr
      intro native hnative
      rw [observe_eq_of_mem_support_condOnFibre law observe hobservation hnative]

/-- Every fixed continuation kernel on retained observations and actions has
the same outcome law under the original and conditioned policies. -/
theorem bind_policy_logicalKernel_eq_bind_conditionedPolicy
    (law : FinDist NativeInfo) (observe : NativeInfo → LogicalInfo)
    (policy : NativeInfo → FinDist Action)
    (logicalKernel : LogicalInfo → Action → FinDist Result) :
    law.bind (fun native =>
        (policy native).bind (logicalKernel (observe native))) =
      (law.map observe).bind fun observation =>
        (conditionedPolicy law observe policy observation).bind
          (logicalKernel observation) := by
  have hjoint :=
    joint_observation_action_eq_bind_conditionedPolicy law observe policy
  have houtcomes := congrArg
    (fun joint : FinDist (LogicalInfo × Action) =>
      joint.bind fun pair => logicalKernel pair.1 pair.2)
    hjoint
  simpa only [bind_bind, bind_map] using houtcomes

/-- A native continuation may also be replaced by a fixed logical kernel when
they agree at every supported native-information state.  No condition is
needed at native states or logical observations carrying no mass. -/
theorem bind_policy_nativeKernel_eq_bind_conditionedPolicy
    (law : FinDist NativeInfo) (observe : NativeInfo → LogicalInfo)
    (policy : NativeInfo → FinDist Action)
    (nativeKernel : NativeInfo → Action → FinDist Result)
    (logicalKernel : LogicalInfo → Action → FinDist Result)
    (hfactor : ∀ native ∈ law.support, ∀ action,
      nativeKernel native action = logicalKernel (observe native) action) :
    law.bind (fun native =>
        (policy native).bind (nativeKernel native)) =
      (law.map observe).bind fun observation =>
        (conditionedPolicy law observe policy observation).bind
          (logicalKernel observation) := by
  calc
    law.bind (fun native => (policy native).bind (nativeKernel native)) =
        law.bind (fun native =>
          (policy native).bind (logicalKernel (observe native))) := by
      apply bind_congr
      intro native hnative
      apply bind_congr
      intro action _
      exact hfactor native hnative action
    _ = (law.map observe).bind fun observation =>
          (conditionedPolicy law observe policy observation).bind
            (logicalKernel observation) :=
      bind_policy_logicalKernel_eq_bind_conditionedPolicy law observe policy logicalKernel

end GameTheory.Math.Probability.FinDist

/-! The strategic probability boundary is proved without additional axioms. -/

/-- info: 'GameTheory.Math.Probability.FinDist.joint_observation_action_eq_bind_conditionedPolicy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.FinDist.joint_observation_action_eq_bind_conditionedPolicy

/-- info: 'GameTheory.Math.Probability.FinDist.bind_policy_nativeKernel_eq_bind_conditionedPolicy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GameTheory.Math.Probability.FinDist.bind_policy_nativeKernel_eq_bind_conditionedPolicy
