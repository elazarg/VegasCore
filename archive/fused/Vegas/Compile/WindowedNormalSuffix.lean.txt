/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedGatedExecution

/-! # Paired suffixes after actual normal service

Once normal service resolves the block's instruction, every remaining reference
poll and environment slot waits. The focal raw policy is still invoked with its
actual history and view. Schedule alignment follows from the supported prefix
and source checkpoints, not an additional policy restriction.
-/

noncomputable section

namespace Vegas.ApplicationPlan.WindowedCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {accounted : CommitmentAccounting pending prog}
variable {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
variable {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {focal : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {plan : ApplicationPlan accounted fresh state}
variable {profile : SourceBehavioralProfile prog}
variable {leftCurrent rightCurrent : CoupledAt (compileCore prog fresh state).graph state}
variable {left right :
  (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}

omit [DecidableEq P] in
private theorem normal_environment_count (roster : List P) :
    ((roster.flatMap fun actor => [Invocation.player actor, .player actor]) ++
      [Invocation.environment]).countP Invocation.isEnvironment = 1 := by
  induction roster with
  | nil => rfl
  | cons actor rest ih =>
      simpa [List.flatMap_cons, List.append_assoc, Invocation.isEnvironment] using ih

omit [DecidableEq P] in
private theorem normal_suffix_environment_count (roster : List P) :
    (Invocation.environment :: roster.flatMap
      (fun actor => [Invocation.player actor, .environment])).countP
        Invocation.isEnvironment = roster.length + 1 := by
  have hcount : ∀ entries : List P,
      (entries.flatMap fun actor => [Invocation.player actor, Invocation.environment]).countP
        Invocation.isEnvironment = entries.length := by
    intro entries
    induction entries with
    | nil => rfl
    | cons actor tail ih => simp [List.flatMap_cons, Invocation.isEnvironment, ih]
  simp only [List.countP_cons, Invocation.isEnvironment, ↓reduceIte, hcount]

/-- Once the actual normal service resolves the current instruction, its
remaining block slots preserve memory, activation, and frozen binding snapshots.
Private preparation and pending traffic may still change under arbitrary raw policies. -/
theorem after_normal_frame
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement blockIndex plan profile leftCurrent left)
    (instruction : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = instruction :: rest)
    (included final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hinactive : (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
      included.native.application.base.memory ≠ some instruction.address)
    (hincluded : included ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        ((roster.flatMap fun actor => [Invocation.player actor, .player actor]) ++ [.environment])
        left).support)
    (hfinal : final ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (.environment :: roster.flatMap fun actor => [Invocation.player actor, .environment])
        included).support) :
    (final.native.application.base.memory, final.native.application.active,
      final.native.application.base.frozen) =
      (included.native.application.base.memory, included.native.application.active,
        included.native.application.base.frozen) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let normal := (roster.flatMap fun actor => [Invocation.player actor, .player actor]) ++
    [Invocation.environment]
  let suffix := Invocation.environment ::
    roster.flatMap fun actor => [Invocation.player actor, .environment]
  let timed := (instruction.withBindingTimeouts binding).withChoiceTimeouts choice
  have haddress : timed.address = instruction.address := by cases instruction <;> rfl
  have hindexOriginal := checkpoint.instruction_at instruction rest hhead
  have hindex : runtime.image.instructions[blockIndex]? = some timed := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, timed]
  have henv : included.environmentHistory.length =
      blockIndex * (roster.length + 2) + 1 := by
    rw [runtime.application.runPolicies_environmentHistory_length players
      (runtime.blockEnvironment roster) normal left included hincluded,
      normal_environment_count, checkpoint.environmentHistory_length]
  have hremainingIndex : ∀ index, included.environmentHistory.length ≤ index →
      index < included.environmentHistory.length + suffix.countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some timed := by
    intro index hlo hhi
    rw [henv] at hlo hhi
    rw [normal_suffix_environment_count] at hhi
    have hquotient : index / (roster.length + 2) = blockIndex := by
      apply Nat.div_eq_of_lt_le
      · omega
      · nlinarith
    rw [hquotient]
    exact hindex
  apply runtime.runPolicies_block_inactive_invariant roster players suffix included final
    timed hremainingIndex (fun native => (native.base.memory, native.active, native.base.frozen) =
      (included.native.application.base.memory, included.native.application.active,
        included.native.application.base.frozen)) ?_ ?_ rfl hfinal
  · intro native actor command hnative
    cases command
    exact hnative
  · intro native hnative
    have hmemory : native.base.memory = included.native.application.base.memory :=
      congrArg Prod.fst hnative
    rw [hmemory, haddress]
    exact hinactive

/-- Paired actual normal-service prefixes extend to paired complete blocks
when the current instruction has resolved. This applies to every instruction
kind and does not require its owner to be the focal player. -/
theorem after_normal_agreement
    (leftCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement blockIndex plan profile leftCurrent left)
    (rightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement blockIndex plan profile rightCurrent right)
    (instruction : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = instruction :: rest)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
      (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (hroster : roster.Nodup)
    (includedLeft includedRight finalLeft finalRight :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (agreement : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal includedLeft includedRight)
    (hinactive : (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
      includedLeft.native.application.base.memory ≠ some instruction.address)
    (hincludedLeft : includedLeft ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        ((roster.flatMap fun actor => [Invocation.player actor, .player actor]) ++ [.environment])
        left).support)
    (hincludedRight : includedRight ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        ((roster.flatMap fun actor => [Invocation.player actor, .player actor]) ++ [.environment])
        right).support)
    (hfinalLeft : finalLeft ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (.environment :: roster.flatMap fun actor => [Invocation.player actor, .environment])
        includedLeft).support)
    (hfinalRight : finalRight ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (.environment :: roster.flatMap fun actor => [Invocation.player actor, .environment])
        includedRight).support) :
    WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal finalLeft finalRight := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let base := fun actor => runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile actor)
  let normal := (roster.flatMap fun actor => [Invocation.player actor, .player actor]) ++
    [Invocation.environment]
  let suffix := Invocation.environment ::
    roster.flatMap fun actor => [Invocation.player actor, .environment]
  let timed := (instruction.withBindingTimeouts binding).withChoiceTimeouts choice
  have haddress : timed.address = instruction.address := by cases instruction <;> rfl
  have hindexOriginal := leftCheckpoint.instruction_at instruction rest hhead
  have hindex : runtime.image.instructions[blockIndex]? = some timed := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, timed]
  have hfocal : players focal = fun history view => FinDist.pure (command history view) := by
    simp only [players, windowedPlayers, Function.update_self]
    exact hpure
  have hothers : ∀ actor, actor ≠ focal →
      players actor = runtime.blockPlayer actor (base actor) := by
    intro actor hactor
    simp only [players, base, windowedPlayers, Function.update_of_ne hactor,
      windowedReferencePlayers]
    rfl
  have hnormalPlayer (actor : P) : normal.countP
      (WindowedApplication.PolicyAgreement.playerCountFor actor) =
        if actor ∈ roster then 2 else 0 := by
    change normal.countP (fun call => match call with
      | .player who => decide (who = actor)
      | .environment => false) = _
    simp only [normal, List.countP_append, List.countP_cons, List.countP_nil,
      Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    convert WindowedApplication.ordinaryPolls_player_count roster hroster actor using 1
    rfl
  have hsuffixPlayer (actor : P) : suffix.countP
      (WindowedApplication.PolicyAgreement.playerCountFor actor) =
        if actor ∈ roster then 1 else 0 := by
    change suffix.countP (fun call => match call with
      | .player who => decide (who = actor)
      | .environment => false) = _
    simp only [suffix, List.countP_cons, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    convert WindowedApplication.relayInvocations_player_count roster hroster actor using 1
    rfl
  have hnormalCount : normal.countP Invocation.isEnvironment = 1 :=
    normal_environment_count roster
  have hsuffixCount : suffix.countP Invocation.isEnvironment = roster.length + 1 :=
    normal_suffix_environment_count roster
  have hcounts := runtime.application.runPolicies_principalHistory_length
  have henvCounts := runtime.application.runPolicies_environmentHistory_length
  have hleftEnv : includedLeft.environmentHistory.length =
      blockIndex * (roster.length + 2) + 1 := by
    rw [henvCounts players (runtime.blockEnvironment roster) normal left includedLeft hincludedLeft,
      hnormalCount, leftCheckpoint.environmentHistory_length]
  have hrightEnv : includedRight.environmentHistory.length =
      blockIndex * (roster.length + 2) + 1 := by
    rw [henvCounts players (runtime.blockEnvironment roster) normal right
      includedRight hincludedRight,
      hnormalCount, rightCheckpoint.environmentHistory_length]
  apply agreement.runPolicies_inactive roster command base players hfocal hothers timed suffix
    _ (hleftEnv.trans hrightEnv.symm) _ _ (by rwa [haddress])
    finalLeft finalRight hfinalLeft hfinalRight
  · intro actor
    rw [hcounts actor players (runtime.blockEnvironment roster) normal left
      includedLeft hincludedLeft,
      hcounts actor players (runtime.blockEnvironment roster) normal right
        includedRight hincludedRight]
    have hl := hcounts actor players (runtime.blockEnvironment roster)
      (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf) left leftCheckpoint.reached
    have hr := hcounts actor players (runtime.blockEnvironment roster)
      (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf) right
      rightCheckpoint.reached
    rw [hl, hr]
  · intro actor index hlo hhi
    have hlength := hcounts actor players (runtime.blockEnvironment roster) normal
      left includedLeft hincludedLeft
    change (includedLeft.principalHistory actor).length = (left.principalHistory actor).length +
      normal.countP (WindowedApplication.PolicyAgreement.playerCountFor actor) at hlength
    change index < (includedLeft.principalHistory actor).length +
      suffix.countP (WindowedApplication.PolicyAgreement.playerCountFor actor) at hhi
    rw [hsuffixPlayer] at hhi
    by_cases hactor : actor ∈ roster
    · rw [hnormalPlayer, if_pos hactor, (leftCheckpoint.historyAlignment hroster actor hactor).1]
        at hlength
      simp only [hactor, ↓reduceIte] at hhi
      have hquotient : index / 3 = blockIndex := by omega
      rw [hquotient]
      exact hindex
    · simp only [hactor, ↓reduceIte, Nat.add_zero] at hhi
      omega
  · intro index hlo hhi
    rw [hleftEnv] at hlo hhi
    rw [hsuffixCount] at hhi
    have hquotient : index / (roster.length + 2) = blockIndex := by
      apply Nat.div_eq_of_lt_le
      · omega
      · nlinarith
    rw [hquotient]
    exact hindex

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.after_normal_agreement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.after_normal_agreement

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.after_normal_frame'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.after_normal_frame
