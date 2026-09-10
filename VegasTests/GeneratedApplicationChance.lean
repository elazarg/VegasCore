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

def witnessPlayers (secret : Bool) : TestPlayer → runtime.application.PlayerPolicy :=
    fun who history _ =>
  if who = 0 then FinDist.pure <| runtime.liftPlayerCommand <| match history.length with
    | 0 => .privateCommand (.register 0 ⟨.bool, secret⟩)
    | 1 => .submit (.binding 0 (0, 0))
    | _ => .submit (.choice 2 ⟨.bool, false⟩)
  else FinDist.pure .wait

def witnessEnvironment : runtime.application.EnvironmentPolicy := fun history _ =>
  FinDist.pure <| runtime.liftEnvironmentCommand <| match history.length with
    | 0 => .include (0, 0)
    | 1 => .include (0, 1)
    | _ => .application (.sample 3)

def witnessPrefix : List (@Invocation TestPlayer) :=
  [.player 0, .player 0, .environment, .player 0, .environment]

def witnessSuffix : List (@Invocation TestPlayer) := [.environment]

def witnessPrefixLaw (secret : Bool) : FinDist runtime.application.PolicyExecution :=
  runtime.application.runPolicies (witnessPlayers secret) witnessEnvironment witnessPrefix
    referenceInitial

private theorem witness_prefix_observation (secret : Bool) :
    (witnessPrefixLaw secret).map (fun execution =>
      (execution.native.application.base.memory.accepted 0,
        execution.native.application.base.memory.done signalCode.node,
        execution.native.application.base.frozen 0)) =
      FinDist.pure (some (.opaque ((0 : TestPlayer), 0)), false,
        some (⟨.bool, secret⟩ : TypedValue simpleExpr)) := by
  simp only [witnessPrefixLaw, witnessPrefix, MessageApplication.runPolicies,
    MessageApplication.invoke, MessageApplication.playerStep,
    MessageApplication.environmentPolicyStep,
    MessageApplication.advance, MessageApplication.step, PlayerCommand.toAction,
    EnvironmentPolicyCommand.toAction, WindowedApplication.liftPlayerCommand,
    WindowedApplication.liftEnvironmentCommand,
    witnessPlayers, witnessEnvironment, referenceInitial, FinDist.pure_bind,
    PolicyExecution.initial, List.length_nil, List.length_cons, List.length_append,
    Nat.zero_add, ↓reduceIte, FinDist.map_pure]
  rfl

private theorem witness_prefix_ready (secret : Bool)
    (execution : runtime.application.PolicyExecution)
    (hexecution : execution ∈ (witnessPrefixLaw secret).support) :
    execution.native.application.base.memory.accepted 0 = some (.opaque (0, 0)) ∧
      execution.native.application.base.memory.done signalCode.node = false := by
  have hmapped :
      (execution.native.application.base.memory.accepted 0,
        execution.native.application.base.memory.done signalCode.node,
        execution.native.application.base.frozen 0) ∈
      ((witnessPrefixLaw secret).map (fun next =>
        (next.native.application.base.memory.accepted 0,
          next.native.application.base.memory.done signalCode.node,
          next.native.application.base.frozen 0))).support := by
    rw [FinDist.support_map]
    exact ⟨execution, hexecution, rfl⟩
  rw [witness_prefix_observation secret, FinDist.mem_support_pure] at hmapped
  exact ⟨congrArg Prod.fst hmapped, congrArg (fun result => result.2.1) hmapped⟩

/-- A finite mixture of actual preparation/submission/inclusion prefixes.
The complete policy executions, including their histories, are retained. -/
def mixedPrefix (choices : FinDist Bool) : FinDist runtime.application.PolicyExecution :=
  choices.bind witnessPrefixLaw

/-- After a randomized real binding prefix, arbitrary suffix policies retain
the joint law of that frozen binding and the generated coin, whenever the
coin resolves throughout their run. -/
theorem arbitrary_suffix_snapshot_signal_law (choices : FinDist Bool)
    (players : TestPlayer → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation TestPlayer))
    (hresolved : ∀ next ∈ ((mixedPrefix choices).bind
      (runtime.application.runPolicies players environment schedule)).support,
      next.native.application.base.memory.done signalCode.node = true) :
    ((mixedPrefix choices).bind
      (runtime.application.runPolicies players environment schedule)).map (fun next =>
        ([next.native.application.base.frozen 0],
          signalCode.read? next.native.application.base.memory)) =
      FinDist.product
        ((mixedPrefix choices).map (fun next => [next.native.application.base.frozen 0]))
        (fairCoin.denote.map some) := by
  apply applicationPlan.windowed_runPolicies_snapshots_sample_law
    deadlineOf noBindingFallback noChoiceFallback windowOf signalCode (signal_mem deadlineOf)
    fairCoin.denote (fun _ => rfl) [0] (mixedPrefix choices) players environment schedule
  · intro execution hexecution field hfield
    have hzero : field = 0 := List.mem_singleton.mp hfield
    subst field
    rw [mixedPrefix, FinDist.support_bind] at hexecution
    obtain ⟨secret, hexecution⟩ := Set.mem_iUnion.mp hexecution
    obtain ⟨_, hexecution⟩ := Set.mem_iUnion.mp hexecution
    exact ⟨(0, 0), (witness_prefix_ready secret execution hexecution).1⟩
  · intro execution hexecution
    rw [mixedPrefix, FinDist.support_bind] at hexecution
    obtain ⟨secret, hexecution⟩ := Set.mem_iUnion.mp hexecution
    obtain ⟨_, hexecution⟩ := Set.mem_iUnion.mp hexecution
    exact (witness_prefix_ready secret execution hexecution).2
  · exact hresolved

private theorem mixedPrefix_snapshots (choices : FinDist Bool) :
    (mixedPrefix choices).map (fun next => [next.native.application.base.frozen 0]) =
      choices.map (fun secret => [some (⟨.bool, secret⟩ : TypedValue simpleExpr)]) := by
  rw [mixedPrefix, FinDist.map_bind]
  apply FinDist.bind_congr
  intro secret _
  have hprojection := congrArg (FinDist.map (fun result => [result.2.2]))
    (witness_prefix_observation secret)
  simpa only [FinDist.map_comp, FinDist.map_pure, Function.comp_def] using hprojection

private theorem witness_sample_done (secret : Bool) :
    ((witnessPrefixLaw secret).bind (runtime.application.runPolicies (witnessPlayers false)
      witnessEnvironment witnessSuffix)).map
        (fun next => next.native.application.base.memory.done signalCode.node) =
      FinDist.pure true := by
  simp only [witnessPrefixLaw, witnessPrefix, witnessSuffix, MessageApplication.runPolicies,
    MessageApplication.invoke, MessageApplication.playerStep,
    MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.step, PlayerCommand.toAction,
    EnvironmentPolicyCommand.toAction, WindowedApplication.liftPlayerCommand,
    WindowedApplication.liftEnvironmentCommand,
    witnessPlayers, witnessEnvironment, referenceInitial, FinDist.pure_bind,
    PolicyExecution.initial, List.length_nil, List.length_cons, List.length_append,
    Nat.zero_add, ↓reduceIte]
  simp only [FinDist.bind_map, FinDist.bind_bind, FinDist.pure_bind,
    FinDist.map_bind, FinDist.map_pure]
  change ((runtime.environmentStep (runtime.initial (checkpoint secret).application)
    (.sample 3)).map (fun next => next.base.memory.done signalCode.node)) = FinDist.pure true
  simp only [WindowedApplication.environmentStep, FinDist.map_comp]
  rw [ApplicationImage.ordered_sample_eq _ _ 3 (by rfl)]
  change (((image.withBindingTimeouts noBindingFallback).withChoiceTimeouts noChoiceFallback).sample
    (checkpoint secret).application 3).map (fun next => next.memory.done signalCode.node) = _
  rw [ApplicationImage.sample_withChoiceTimeouts, ApplicationImage.sample_withBindingTimeouts]
  rw [checkpoint_sample_law]
  rw [FinDist.map_comp]
  change (fairCoin.denote.map (fun _ => true)) = FinDist.pure true
  exact FinDist.map_const _ _

/-- The actual chance invocation resolves after every secret in the mixture;
this is proved on the operational runner rather than assumed as fairness. -/
private theorem mixedPrefix_sample_resolved (choices : FinDist Bool)
    (next : runtime.application.PolicyExecution)
    (hnext : next ∈ ((mixedPrefix choices).bind
      (runtime.application.runPolicies (witnessPlayers false)
        witnessEnvironment witnessSuffix)).support) :
    next.native.application.base.memory.done signalCode.node = true := by
  have hlaw : ((mixedPrefix choices).bind
      (runtime.application.runPolicies (witnessPlayers false)
        witnessEnvironment witnessSuffix)).map
          (fun next => next.native.application.base.memory.done signalCode.node) =
      FinDist.pure true := by
    rw [mixedPrefix, FinDist.bind_bind, FinDist.map_bind]
    exact (FinDist.bind_congr (fun secret _ => witness_sample_done secret)).trans
      (FinDist.bind_const _ _)
  have hmem : next.native.application.base.memory.done signalCode.node ∈
      (((mixedPrefix choices).bind
        (runtime.application.runPolicies (witnessPlayers false)
          witnessEnvironment witnessSuffix)).map
            (fun out => out.native.application.base.memory.done signalCode.node)).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  rwa [hlaw, FinDist.mem_support_pure] at hmem

/-- Two potentially nontrivial independent draws on the generated runtime:
an arbitrary randomized hidden binding, then its fixed public chance kernel. -/
theorem witness_snapshot_signal_law (choices : FinDist Bool) :
    (choices.bind (fun secret => runtime.application.runPolicies (witnessPlayers secret)
      witnessEnvironment (witnessPrefix ++ witnessSuffix) referenceInitial)).map (fun next =>
          ([next.native.application.base.frozen 0],
            signalCode.read? next.native.application.base.memory)) =
      FinDist.product
        (choices.map (fun secret => [some (⟨.bool, secret⟩ : TypedValue simpleExpr)]))
        (fairCoin.denote.map some) := by
  have hsplit : (choices.bind (fun secret =>
      runtime.application.runPolicies (witnessPlayers secret) witnessEnvironment
        (witnessPrefix ++ witnessSuffix) referenceInitial)) =
      (mixedPrefix choices).bind (runtime.application.runPolicies (witnessPlayers false)
        witnessEnvironment witnessSuffix) := by
    rw [mixedPrefix, FinDist.bind_bind]
    apply FinDist.bind_congr
    intro secret _
    rw [MessageApplication.runPolicies_append]
    apply FinDist.bind_congr
    intro execution _
    apply runtime.application.runPolicies_congr_on_schedule
    intro who hwho
    simp only [witnessSuffix, List.mem_singleton, reduceCtorEq] at hwho
  rw [hsplit, arbitrary_suffix_snapshot_signal_law choices (witnessPlayers false)
    witnessEnvironment witnessSuffix (mixedPrefix_sample_resolved choices), mixedPrefix_snapshots]

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

/-- info: 'VegasTests.GeneratedApplicationChance.arbitrary_suffix_snapshot_signal_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedApplicationChance.arbitrary_suffix_snapshot_signal_law

/-- info: 'VegasTests.GeneratedApplicationChance.witness_snapshot_signal_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedApplicationChance.witness_snapshot_signal_law

/-- info: 'VegasTests.GeneratedApplicationChance.arbitrary_policy_signal_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedApplicationChance.arbitrary_policy_signal_law

/-- info: 'VegasTests.GeneratedApplicationChance.reference_signal_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.GeneratedApplicationChance.reference_signal_law
