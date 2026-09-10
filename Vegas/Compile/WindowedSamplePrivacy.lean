/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedOwnedBlock
import Vegas.Compile.WindowedGatedExecution
import Vegas.Compile.WindowedSampleCheckpoint

/-! # Paired information flow through source chance blocks -/

noncomputable section

namespace Vegas.WindowedApplication.PolicyAgreement

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {runtime : WindowedApplication P L} {focal : P}
variable {left right : runtime.application.PolicyExecution}

/-- Applying the same public chance draw to agreeing executions preserves the
focal policy input. The sample updates public memory identically and does not
change either message state or player history. -/
theorem sampleExecution_same (agreement : PolicyAgreement runtime focal left right)
    (code : SampleCode L) (value : L.Val code.dist.ty) :
    PolicyAgreement runtime focal (runtime.sampleExecution left code value)
      (runtime.sampleExecution right code value) := by
  refine ⟨?_, agreement.pool, agreement.receipts, agreement.history⟩
  change (runtime.advanceTo left.native.application
      (left.native.application.base.sample code value)).AgreesFor focal
    (runtime.advanceTo right.native.application
      (right.native.application.base.sample code value))
  exact agreement.state.advanceTo runtime (agreement.state.base.sample code value)

end Vegas.WindowedApplication.PolicyAgreement

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.sampleExecution_same' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.sampleExecution_same

namespace Vegas.ApplicationPlan.WindowedCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {focal : P}
variable {replacement :
  (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name : VarId} {ty : L.Ty}
variable {dist : L.DistExpr (erasePubVCtx Γ) ty}
variable {tail : VegasCore P L ((name, .pub ty) :: Γ)}
variable {accounted : CommitmentAccounting pending tail}
variable {fresh : FreshBindings (.sample name dist tail)} {state : BuildState P L Γ}

/-- Two actual generated chance blocks preserve focal information when their
source kernels take the same supported draw. The native focal policy is fixed
and pure but otherwise unrestricted. No equality of its output commands, or
of any nonfocal history, is assumed. -/
theorem sample_block_agreement_of_same_draw
    (nextPlan : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1)
    (profile : SourceBehavioralProfile (.sample name dist tail))
    (leftCurrent rightCurrent :
      CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (left right :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (leftCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex (.sample (fresh := fresh) nextPlan) profile
      leftCurrent left)
    (rightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex (.sample (fresh := fresh) nextPlan) profile
      rightCurrent right)
    (agreement : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal left right)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (hroster : roster.Nodup)
    (value : L.Val ty)
    (hvalueLeft : value ∈
      (L.evalDist dist leftCurrent.current.source.eraseSampleEnv).support)
    (hvalueRight : value ∈
      (L.evalDist dist rightCurrent.current.source.eraseSampleEnv).support)
    (middleLeft middleRight finalLeft finalRight :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hmiddleLeft : middleLeft ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap (fun actor => [Invocation.player actor, .player actor])) left).support)
    (hmiddleRight : middleRight ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (roster.flatMap (fun actor => [Invocation.player actor, .player actor])) right).support)
    (hfinalLeft : finalLeft ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (Invocation.environment :: roster.flatMap
          (fun actor => [Invocation.player actor, .environment]))
        ((root.windowed deadlineOf binding choice windowOf).sampleExecution middleLeft
          (headSampleCode fresh state) value)).support)
    (hfinalRight : finalRight ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (Invocation.environment :: roster.flatMap
          (fun actor => [Invocation.player actor, .environment]))
        ((root.windowed deadlineOf binding choice windowOf).sampleExecution middleRight
          (headSampleCode fresh state) value)).support) :
    WindowedApplication.PolicyAgreement
        (root.windowed deadlineOf binding choice windowOf) focal finalLeft finalRight ∧
      finalLeft ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) left).support ∧
      finalRight ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) right).support := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf
    focal replacement
  let base := fun actor => runtime.liftPlayerPolicy
    (root.liftProfile deadlineOf rootProfile actor)
  let code := headSampleCode fresh state
  let instruction : ApplicationInstruction P L := .sample code
  let before := roster.flatMap (fun actor => [Invocation.player actor, .player actor])
  let suffix := Invocation.environment ::
    roster.flatMap (fun actor => [Invocation.player actor, .environment])
  have hleftLaw :=
    (WindowedCheckpoint.sample_block nextPlan profile leftCurrent left leftCheckpoint).1
  have hrightLaw :=
    (WindowedCheckpoint.sample_block nextPlan profile rightCurrent right rightCheckpoint).1
  have hwholeLeft : finalLeft ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) (WindowedApplication.blockInvocations roster)
      left).support := by
    rw [hleftLaw]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨middleLeft, hmiddleLeft, value, hvalueLeft, hfinalLeft⟩
  have hwholeRight : finalRight ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) (WindowedApplication.blockInvocations roster)
      right).support := by
    rw [hrightLaw]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨middleRight, hmiddleRight, value, hvalueRight, hfinalRight⟩
  have hhead : (ApplicationPlan.sample (fresh := fresh) nextPlan).instructions deadlineOf =
      .sample code :: nextPlan.instructions deadlineOf := rfl
  have hindexOriginal := leftCheckpoint.instruction_at (.sample code) _ hhead
  have hindex : runtime.image.instructions[blockIndex]? = some instruction := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts, instruction]
  have hfocal : players focal = fun history view => FinDist.pure (command history view) := by
    simp only [players, windowedPlayers, Function.update_self]
    exact hpure
  have hothers : ∀ actor, actor ≠ focal →
      players actor = runtime.blockPlayer actor (base actor) := by
    intro actor hactor
    simp only [players, base, windowedPlayers, Function.update_of_ne hactor,
      windowedReferencePlayers]
    rfl
  have hlengths : ∀ actor, (left.principalHistory actor).length =
      (right.principalHistory actor).length := by
    intro actor
    have hl := runtime.application.runPolicies_principalHistory_length actor players
      (runtime.blockEnvironment roster)
      (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf) left
      leftCheckpoint.reached
    have hr := runtime.application.runPolicies_principalHistory_length actor players
      (runtime.blockEnvironment roster)
      (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf) right
      rightCheckpoint.reached
    exact hl.trans hr.symm
  have hbeforePlayers : ∀ invocation ∈ before,
      ∃ actor, invocation = Invocation.player actor := by
    intro invocation hinv
    simp only [before, List.mem_flatMap] at hinv
    obtain ⟨actor, _, hinv⟩ := hinv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hinv
    rcases hinv with rfl | rfl <;> exact ⟨actor, rfl⟩
  have hbeforeAgreement : WindowedApplication.PolicyAgreement runtime focal
      middleLeft middleRight := by
    apply agreement.runPolicies_players_gated command base players hfocal hothers instruction
      before hbeforePlayers _ (runtime.blockEnvironment roster) hlengths _
      middleLeft middleRight hmiddleLeft hmiddleRight
    · intro actor _ _
      change (none : Option P) ≠ some actor
      intro hsome
      cases hsome
    · intro actor index hlo hhi
      change index < (left.principalHistory actor).length + before.countP
        (fun invocation => match invocation with
          | .player who => decide (who = actor)
          | .environment => false) at hhi
      have hcount := WindowedApplication.ordinaryPolls_player_count roster hroster actor
      change before.countP (fun invocation => match invocation with
        | .player who => decide (who = actor)
        | .environment => false) = if actor ∈ roster then 2 else 0 at hcount
      by_cases hactor : actor ∈ roster
      · simp only [hactor, ↓reduceIte] at hcount
        rw [hcount] at hhi
        have hlength := (leftCheckpoint.historyAlignment hroster actor hactor).1
        have hquotient : index / 3 = blockIndex := by omega
        rw [hquotient]
        exact hindex
      · simp only [hactor, ↓reduceIte] at hcount
        rw [hcount, Nat.add_zero] at hhi
        omega
  let sampledLeft := runtime.sampleExecution middleLeft code value
  let sampledRight := runtime.sampleExecution middleRight code value
  have hsampledAgreement : WindowedApplication.PolicyAgreement runtime focal
      sampledLeft sampledRight :=
    hbeforeAgreement.sampleExecution_same code value
  have hmiddleLengths : ∀ actor, (middleLeft.principalHistory actor).length =
      (middleRight.principalHistory actor).length := by
    intro actor
    have hl := runtime.application.runPolicies_principalHistory_length actor players
      (runtime.blockEnvironment roster) before left middleLeft hmiddleLeft
    have hr := runtime.application.runPolicies_principalHistory_length actor players
      (runtime.blockEnvironment roster) before right middleRight hmiddleRight
    rw [hl, hr, hlengths]
  have hsampledLengths : ∀ actor, (sampledLeft.principalHistory actor).length =
      (sampledRight.principalHistory actor).length := by
    intro actor
    simpa only [sampledLeft, sampledRight, WindowedApplication.sampleExecution]
      using hmiddleLengths actor
  have hbeforeEnvironment : before.countP Invocation.isEnvironment = 0 := by
    apply List.countP_eq_zero.mpr
    intro invocation hinv
    obtain ⟨actor, hactor⟩ := hbeforePlayers invocation hinv
    subst invocation
    simp [Invocation.isEnvironment]
  have hmiddleEnvironmentLeft : middleLeft.environmentHistory.length =
      left.environmentHistory.length := by
    have hlength := runtime.application.runPolicies_environmentHistory_length players
      (runtime.blockEnvironment roster) before left middleLeft hmiddleLeft
    simpa only [hbeforeEnvironment, Nat.add_zero] using hlength
  have hmiddleEnvironmentRight : middleRight.environmentHistory.length =
      right.environmentHistory.length := by
    have hlength := runtime.application.runPolicies_environmentHistory_length players
      (runtime.blockEnvironment roster) before right middleRight hmiddleRight
    simpa only [hbeforeEnvironment, Nat.add_zero] using hlength
  have hsampledEnvironment : sampledLeft.environmentHistory.length =
      sampledRight.environmentHistory.length := by
    simp only [sampledLeft, sampledRight, WindowedApplication.sampleExecution,
      List.length_append, List.length_singleton]
    rw [hmiddleEnvironmentLeft, hmiddleEnvironmentRight,
      leftCheckpoint.environmentHistory_length, rightCheckpoint.environmentHistory_length]
  have hsuffixCount : suffix.countP Invocation.isEnvironment = roster.length + 1 := by
    have hcount : ∀ entries : List P,
        (entries.flatMap fun actor =>
          [Invocation.player actor, Invocation.environment]).countP
            Invocation.isEnvironment = entries.length := by
      intro entries
      induction entries with
      | nil => rfl
      | cons actor rest ih =>
          simp [List.flatMap_cons, Invocation.isEnvironment, ih]
    simp only [suffix, List.countP_cons, Invocation.isEnvironment, ↓reduceIte, hcount]
  have hinactive : runtime.image.activeAddress?
      sampledLeft.native.application.base.memory ≠ some code.node := by
    intro hstillActive
    have hnotDone := runtime.image.activeAddress?_not_done
      sampledLeft.native.application.base.memory code.node hstillActive
    have hdone : sampledLeft.native.application.base.memory.done code.node = true := by
      simp [sampledLeft, WindowedApplication.sampleExecution, WindowedApplication.advanceTo,
        ApplicationImage.State.sample]
    rw [hdone] at hnotDone
    contradiction
  refine ⟨?_, hwholeLeft, hwholeRight⟩
  apply hsampledAgreement.runPolicies_inactive_gated roster command base players hfocal hothers
    instruction _ suffix hsampledLengths hsampledEnvironment _ _ hinactive
    finalLeft finalRight hfinalLeft hfinalRight
  · intro actor _
    change (none : Option P) ≠ some actor
    intro hsome
    cases hsome
  · intro actor index hlo hhi
    have hhi' : index < (sampledLeft.principalHistory actor).length +
        suffix.countP (fun invocation => match invocation with
          | .player who => decide (who = actor)
          | .environment => false) := by
      convert hhi using 1
      rfl
    have hcount := WindowedApplication.relayInvocations_player_count roster hroster actor
    change (roster.flatMap fun actor =>
      [Invocation.player actor, Invocation.environment]).countP
        (fun invocation => match invocation with
          | .player who => decide (who = actor)
          | .environment => false) = if actor ∈ roster then 1 else 0 at hcount
    have hsuffixPlayerCount : suffix.countP (fun invocation => match invocation with
        | .player who => decide (who = actor)
        | .environment => false) = if actor ∈ roster then 1 else 0 := by
      simpa only [suffix, List.countP_cons, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero] using hcount
    by_cases hactor : actor ∈ roster
    · simp only [hactor, ↓reduceIte] at hsuffixPlayerCount
      rw [hsuffixPlayerCount] at hhi'
      have hmiddleLength : (middleLeft.principalHistory actor).length =
          (left.principalHistory actor).length + before.countP
            (fun invocation => match invocation with
              | .player who => decide (who = actor)
              | .environment => false) := by
        convert runtime.application.runPolicies_principalHistory_length actor players
          (runtime.blockEnvironment roster) before left middleLeft hmiddleLeft using 1
        rfl
      have hbeforeCount := WindowedApplication.ordinaryPolls_player_count roster hroster actor
      change before.countP (fun invocation => match invocation with
        | .player who => decide (who = actor)
        | .environment => false) = if actor ∈ roster then 2 else 0 at hbeforeCount
      simp only [hactor, ↓reduceIte] at hbeforeCount
      have hstart := (leftCheckpoint.historyAlignment hroster actor hactor).1
      have hsampledLength : (sampledLeft.principalHistory actor).length =
          3 * blockIndex + 2 := by
        simp only [sampledLeft, WindowedApplication.sampleExecution, hmiddleLength,
          hbeforeCount, hstart]
      rw [hsampledLength] at hlo hhi'
      have hquotient : index / 3 = blockIndex := by omega
      rw [hquotient]
      exact hindex
    · simp only [hactor, ↓reduceIte] at hsuffixPlayerCount
      rw [hsuffixPlayerCount, Nat.add_zero] at hhi'
      omega
  · intro index hlo hhi
    have hsampledLength : sampledLeft.environmentHistory.length =
        blockIndex * (roster.length + 2) + 1 := by
      simp only [sampledLeft, WindowedApplication.sampleExecution, List.length_append,
        List.length_singleton, hmiddleEnvironmentLeft,
        leftCheckpoint.environmentHistory_length]
    rw [hsampledLength] at hlo hhi
    rw [hsuffixCount] at hhi
    have hquotient : index / (roster.length + 2) = blockIndex := by
      have hpositive : 0 < roster.length + 2 := by omega
      apply Nat.div_eq_of_lt_le
      · omega
      · nlinarith
    rw [hquotient]
    exact hindex

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.sample_block_agreement_of_same_draw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.WindowedCheckpoint.sample_block_agreement_of_same_draw
