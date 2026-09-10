/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPlanSampleLaw
import Vegas.Compile.WindowedForwardLaw
import VegasTests.GeneratedApplicationSourceLaw

/-! # Fixed chance in the generated persistent-disclosure application -/

noncomputable section

namespace VegasTests.GeneratedApplicationChance

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure
open VegasTests.GeneratedPersistentDisclosure

theorem signal_mem (deadlineOf : Nat → Nat) :
    (ApplicationInstruction.sample (P := TestPlayer) signalCode) ∈
      (applicationPlan.image deadlineOf).instructions := by
  change _ ∈ [_, _, ApplicationInstruction.sample signalCode, _, _, _]
  simp

/-- Any policies and finite schedule preserve the source coin at the actual
generated signal site. The sole dynamic premise is that every supported final
state has resolved that site; the rest of the program may remain unfinished. -/
theorem arbitrary_policy_signal_law
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode TestPlayer simpleExpr) →
      Option (PublicFallbackCode simpleExpr code.ty))
    (choice : (code : PublicChoiceCode TestPlayer simpleExpr) →
      Option (PublicFallbackCode simpleExpr code.guard.ty))
    (windowOf : Nat → Nat)
    (players : TestPlayer →
      (applicationPlan.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (environment :
      (applicationPlan.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation TestPlayer))
    (execution :
      (applicationPlan.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hnotDone : execution.native.application.base.memory.done signalCode.node = false)
    (hresolved : ∀ next ∈
      ((applicationPlan.windowed deadlineOf binding choice windowOf).application.runPolicies
        players environment schedule execution).support,
      next.native.application.base.memory.done signalCode.node = true) :
    ((applicationPlan.windowed deadlineOf binding choice windowOf).application.runPolicies
      players environment schedule execution).map
        (fun next => signalCode.read? next.native.application.base.memory) =
      fairCoin.denote.map some := by
  exact applicationPlan.windowed_runPolicies_sample_law deadlineOf binding choice windowOf
    signalCode (signal_mem deadlineOf) fairCoin.denote (fun _ => rfl)
    players environment schedule execution hnotDone hresolved

def deadlineOf : Nat → Nat := fun _ => 10
def noBindingFallback : (code : BindingCode TestPlayer simpleExpr) →
    Option (PublicFallbackCode simpleExpr code.ty) := fun _ => none
def noChoiceFallback : (code : PublicChoiceCode TestPlayer simpleExpr) →
    Option (PublicFallbackCode simpleExpr code.guard.ty) := fun _ => none
def windowOf : Nat → Nat := fun _ => 10

def runtime : WindowedApplication TestPlayer simpleExpr :=
  applicationPlan.windowed deadlineOf noBindingFallback noChoiceFallback windowOf

def referencePlayers (profile : SourceBehavioralProfile source.prog) :
    TestPlayer → runtime.application.PlayerPolicy := fun who =>
  runtime.liftPlayerPolicy (applicationPlan.liftProfile deadlineOf profile who)

def referenceEnvironment : runtime.application.EnvironmentPolicy :=
  runtime.liftEnvironmentPolicy (applicationPlan.image deadlineOf).serialService

def referenceInitial : runtime.application.PolicyExecution :=
  PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application
      (runtime.initial (ApplicationImage.State.initial
        (ApplicationImage.Memory.initial (compile source).graph))) )

def referenceSchedule : List (@Invocation TestPlayer) :=
  (applicationPlan.image deadlineOf).serviceInvocations

/-- The generic resolution premise is inhabited by the compiler's actual
windowed lifted profile and serial service. It follows from their checked full
completion law, not from a progress or chance-law certificate. -/
theorem reference_signal_resolved (profile : SourceBehavioralProfile source.prog)
    (next : runtime.application.PolicyExecution)
    (hnext : next ∈ (runtime.application.runPolicies (referencePlayers profile)
      referenceEnvironment referenceSchedule referenceInitial).support) :
    next.native.application.base.memory.done signalCode.node = true := by
  have hlaw := applicationPlan.windowed_service_source_public_law
    DisclosureAccounting.persistentChecked deadlineOf noBindingFallback noChoiceFallback
    windowOf profile GeneratedApplicationSourceLaw.initial_reads_public
    ApplicationBindingOrigins.persistent_image_has_binding_origins
  have hresult :
      (next.native.application.base.memory.finished (compile source).graph.nodeCount,
        (compile source).readPublicTerminal? next.native.application.base.memory) ∈
      ((runtime.application.runPolicies (referencePlayers profile)
        referenceEnvironment referenceSchedule referenceInitial).map (fun out =>
          (out.native.application.base.memory.finished (compile source).graph.nodeCount,
            (compile source).readPublicTerminal? out.native.application.base.memory))).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  change
    (runtime.application.runPolicies (referencePlayers profile) referenceEnvironment
      referenceSchedule referenceInitial).map (fun out =>
        (out.native.application.base.memory.finished (compile source).graph.nodeCount,
          (compile source).readPublicTerminal? out.native.application.base.memory)) = _ at hlaw
  rw [hlaw, FinDist.support_map] at hresult
  obtain ⟨terminal, _, heq⟩ := hresult
  have hfinished :
      next.native.application.base.memory.finished (compile source).graph.nodeCount = true :=
    congrArg Prod.fst heq.symm
  apply List.all_eq_true.mp hfinished signalCode.node
  apply List.mem_range.mpr
  decide +kernel

/-- Consequently the actual compiled reference execution has the source coin
marginal at the emitted signal field. -/
theorem reference_signal_law (profile : SourceBehavioralProfile source.prog) :
    (runtime.application.runPolicies (referencePlayers profile) referenceEnvironment
      referenceSchedule referenceInitial).map
        (fun next => signalCode.read? next.native.application.base.memory) =
      fairCoin.denote.map some := by
  apply arbitrary_policy_signal_law deadlineOf noBindingFallback noChoiceFallback windowOf
    (referencePlayers profile) referenceEnvironment referenceSchedule referenceInitial
  · rfl
  · exact reference_signal_resolved profile

end VegasTests.GeneratedApplicationChance

/-- info: 'VegasTests.GeneratedApplicationChance.arbitrary_policy_signal_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedApplicationChance.arbitrary_policy_signal_law

/-- info: 'VegasTests.GeneratedApplicationChance.reference_signal_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedApplicationChance.reference_signal_law
