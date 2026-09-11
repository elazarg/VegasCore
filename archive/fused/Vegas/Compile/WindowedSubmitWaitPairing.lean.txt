/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedGatedExecution

/-! # Paired execution of identical nonfocal submit/wait polls -/

noncomputable section

namespace Vegas.WindowedApplication.PolicyAgreement

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {runtime : WindowedApplication P L} {focal : P}
variable {left right : runtime.application.PolicyExecution}

/-- After a paired gated prefix, a shared supported payload input gives equal
nonfocal submissions followed by waits. The kernels themselves may differ.
The result retains membership in both actual prefix executions. -/
theorem submit_wait_after_gated_prefix
    {A : Type}
    (agreement : PolicyAgreement runtime focal left right)
    (owner : P) (howner : owner ≠ focal)
    (payload : A → ApplicationImage.Payload P L)
    (replacement : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (base players : P → runtime.application.PlayerPolicy)
    (hfocal : players focal = fun history view => FinDist.pure (replacement history view))
    (hothers : ∀ actor, actor ≠ focal →
      players actor = runtime.blockPlayer actor (base actor))
    (instruction : ApplicationInstruction P L) (before : List (@Invocation P))
    (hplayers : ∀ invocation ∈ before, ∃ actor, invocation = .player actor)
    (hgate : ∀ actor, Invocation.player actor ∈ before → actor ≠ focal →
      instruction.submitter ≠ some actor)
    (environment : runtime.application.EnvironmentPolicy)
    (hplayerLengths : ∀ actor, (left.principalHistory actor).length =
      (right.principalHistory actor).length)
    (hplayerIndex : ∀ actor index, (left.principalHistory actor).length ≤ index →
      index < (left.principalHistory actor).length +
        before.countP (playerCountFor actor) →
      runtime.image.instructions[index / 3]? = some instruction)
    (leftKernel rightKernel : FinDist A)
    (hleftOwnerLaw : ∀ middle,
      middle ∈ (runtime.application.runPolicies players environment before left).support →
      runtime.application.runPolicies players environment
        [.player owner, .player owner] middle =
          leftKernel.bind fun value =>
            (runtime.application.playerStep owner middle
              (.submit (payload value))).bind fun submitted =>
                runtime.application.playerStep owner submitted .wait)
    (hrightOwnerLaw : ∀ middle,
      middle ∈ (runtime.application.runPolicies players environment before right).support →
      runtime.application.runPolicies players environment
        [.player owner, .player owner] middle =
          rightKernel.bind fun value =>
            (runtime.application.playerStep owner middle
              (.submit (payload value))).bind fun submitted =>
                runtime.application.playerStep owner submitted .wait)
    (value : A) (hleftValue : value ∈ leftKernel.support)
    (hrightValue : value ∈ rightKernel.support)
    (leftMiddle rightMiddle leftSubmitted rightSubmitted leftFinal rightFinal :
      runtime.application.PolicyExecution)
    (hleftMiddle : leftMiddle ∈
      (runtime.application.runPolicies players environment before left).support)
    (hrightMiddle : rightMiddle ∈
      (runtime.application.runPolicies players environment before right).support)
    (hleftSubmitted : leftSubmitted ∈
      (runtime.application.playerStep owner leftMiddle
        (.submit (payload value))).support)
    (hrightSubmitted : rightSubmitted ∈
      (runtime.application.playerStep owner rightMiddle
        (.submit (payload value))).support)
    (hleftFinal : leftFinal ∈
      (runtime.application.playerStep owner leftSubmitted .wait).support)
    (hrightFinal : rightFinal ∈
      (runtime.application.playerStep owner rightSubmitted .wait).support) :
    PolicyAgreement runtime focal leftFinal rightFinal ∧
      leftFinal ∈ (runtime.application.runPolicies players environment
        (before ++ [.player owner, .player owner]) left).support ∧
      rightFinal ∈ (runtime.application.runPolicies players environment
        (before ++ [.player owner, .player owner]) right).support := by
  have middleAgreement := agreement.runPolicies_players_gated replacement base players
    hfocal hothers instruction before hplayers hgate environment hplayerLengths
    hplayerIndex leftMiddle rightMiddle hleftMiddle hrightMiddle
  have submittedAgreement := middleAgreement.playerStep_submit_other owner howner
    (payload value) leftSubmitted rightSubmitted
    hleftSubmitted hrightSubmitted
  refine ⟨submittedAgreement.playerStep_wait_other owner howner leftFinal rightFinal
    hleftFinal hrightFinal, ?_, ?_⟩
  · rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    refine ⟨leftMiddle, hleftMiddle, ?_⟩
    rw [hleftOwnerLaw leftMiddle hleftMiddle]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨value, hleftValue, leftSubmitted,
      hleftSubmitted, hleftFinal⟩
  · rw [MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    refine ⟨rightMiddle, hrightMiddle, ?_⟩
    rw [hrightOwnerLaw rightMiddle hrightMiddle]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨value, hrightValue, rightSubmitted,
      hrightSubmitted, hrightFinal⟩

/-- A complete ordinary roster poll preserves focal information when the
distinguished nonfocal submitter takes the same supported input on both sides. -/
theorem ordinary_submit_wait_of_same_input
    {A : Type}
    (agreement : PolicyAgreement runtime focal left right)
    (owner : P) (hother : owner ≠ focal)
    (payload : A → ApplicationImage.Payload P L)
    (replacement : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (base players : P → runtime.application.PlayerPolicy)
    (hfocal : players focal = fun history view => FinDist.pure (replacement history view))
    (hothers : ∀ actor, actor ≠ focal →
      players actor = runtime.blockPlayer actor (base actor))
    (instruction : ApplicationInstruction P L)
    (hsubmitter : instruction.submitter = some owner)
    (roster : List P) (hroster : roster.Nodup)
    (beforeRoster afterRoster : List P)
    (hsplit : roster = beforeRoster ++ owner :: afterRoster)
    (environment : runtime.application.EnvironmentPolicy)
    (blockIndex : Nat)
    (hlengths : ∀ actor, (left.principalHistory actor).length =
      (right.principalHistory actor).length)
    (hstart : ∀ actor, actor ∈ roster →
      (left.principalHistory actor).length = 3 * blockIndex)
    (hindex : runtime.image.instructions[blockIndex]? = some instruction)
    (leftKernel rightKernel : FinDist A)
    (hleftOwnerLaw : ∀ middle,
      middle ∈ (runtime.application.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) left).support →
      runtime.application.runPolicies players environment
        [.player owner, .player owner] middle =
          leftKernel.bind fun value =>
            (runtime.application.playerStep owner middle
              (.submit (payload value))).bind fun submitted =>
                runtime.application.playerStep owner submitted .wait)
    (hrightOwnerLaw : ∀ middle,
      middle ∈ (runtime.application.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) right).support →
      runtime.application.runPolicies players environment
        [.player owner, .player owner] middle =
          rightKernel.bind fun value =>
            (runtime.application.playerStep owner middle
              (.submit (payload value))).bind fun submitted =>
                runtime.application.playerStep owner submitted .wait)
    (value : A) (hleftValue : value ∈ leftKernel.support)
    (hrightValue : value ∈ rightKernel.support)
    (polledLeft polledRight : runtime.application.PolicyExecution)
    (hleftBranch : polledLeft ∈
      ((runtime.application.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) left).bind fun middle =>
          (runtime.application.playerStep owner middle (.submit (payload value))).bind
            fun submitted =>
              (runtime.application.playerStep owner submitted .wait).bind fun waited =>
                runtime.application.runPolicies players environment
                  (afterRoster.flatMap fun actor => [.player actor, .player actor]) waited).support)
    (hrightBranch : polledRight ∈
      ((runtime.application.runPolicies players environment
        (beforeRoster.flatMap fun actor => [.player actor, .player actor]) right).bind fun middle =>
          (runtime.application.playerStep owner middle (.submit (payload value))).bind
            fun submitted =>
              (runtime.application.playerStep owner submitted .wait).bind fun waited =>
                runtime.application.runPolicies players environment
                  (afterRoster.flatMap fun actor => [.player actor, .player actor])
                    waited).support) :
    PolicyAgreement runtime focal polledLeft polledRight ∧
      polledLeft ∈ (runtime.application.runPolicies players environment
        (roster.flatMap fun actor => [.player actor, .player actor]) left).support ∧
      polledRight ∈ (runtime.application.runPolicies players environment
        (roster.flatMap fun actor => [.player actor, .player actor]) right).support := by
  let before := beforeRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  let after := afterRoster.flatMap fun actor => [Invocation.player actor, .player actor]
  have hsplitNodup := List.nodup_append.mp (hsplit ▸ hroster)
  have hbeforeNodup := hsplitNodup.1
  have hafterNodup := (List.nodup_cons.mp hsplitNodup.2.1).2
  have hbeforeOwnerSet : owner ∉ beforeRoster := by
    intro hmem
    exact hsplitNodup.2.2 owner hmem owner (by simp) rfl
  have hafterOwnerSet : owner ∉ afterRoster := (List.nodup_cons.mp hsplitNodup.2.1).1
  simp only [FinDist.support_bind, Set.mem_iUnion] at hleftBranch hrightBranch
  obtain ⟨leftMiddle, hleftMiddle, leftSubmitted, hleftSubmitted, leftWaited,
    hleftWaited, hleftAfter⟩ := hleftBranch
  obtain ⟨rightMiddle, hrightMiddle, rightSubmitted, hrightSubmitted, rightWaited,
    hrightWaited, hrightAfter⟩ := hrightBranch
  have hbeforePlayers : ∀ invocation ∈ before,
      ∃ actor, invocation = Invocation.player actor := by
    intro invocation hinv
    rcases List.mem_flatMap.mp hinv with ⟨actor, _, hpair⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
    rcases hpair with rfl | rfl <;> exact ⟨actor, rfl⟩
  have hbeforeOwner : Invocation.player owner ∉ before := by
    simp [before, hbeforeOwnerSet]
  have hpaired := agreement.submit_wait_after_gated_prefix owner hother payload replacement
    base players hfocal hothers instruction before hbeforePlayers (by
      intro actor hmem _
      have hne : actor ≠ owner := by
        intro heq; subst actor; exact hbeforeOwner hmem
      rw [hsubmitter]
      exact fun heq => hne (Option.some.inj heq).symm)
    environment hlengths (by
      intro actor index hlo hhi
      have hcount := WindowedApplication.ordinaryPolls_player_count beforeRoster
        hbeforeNodup actor
      change before.countP (PolicyAgreement.playerCountFor actor) =
        (if actor ∈ beforeRoster then 2 else 0) at hcount
      rw [hcount] at hhi
      split at hhi
      · rename_i hactor
        have hactorRoster : actor ∈ roster := by
          rw [hsplit]
          exact List.mem_append_left _ hactor
        rw [hstart actor hactorRoster] at hlo hhi
        have : index / 3 = blockIndex := by omega
        rw [this]
        exact hindex
      · omega)
    leftKernel rightKernel hleftOwnerLaw hrightOwnerLaw value hleftValue hrightValue
    leftMiddle rightMiddle leftSubmitted rightSubmitted leftWaited rightWaited
    hleftMiddle hrightMiddle hleftSubmitted hrightSubmitted hleftWaited hrightWaited
  have hwaitedLengths : ∀ actor, (leftWaited.principalHistory actor).length =
      (rightWaited.principalHistory actor).length := by
    intro actor
    have hl := runtime.application.runPolicies_principalHistory_length actor players environment
      (before ++ [.player owner, .player owner]) left leftWaited hpaired.2.1
    have hr := runtime.application.runPolicies_principalHistory_length actor players environment
      (before ++ [.player owner, .player owner]) right rightWaited hpaired.2.2
    rw [hl, hr, hlengths]
  have hafterAgreement := hpaired.1.runPolicies_players_gated replacement base players hfocal
    hothers instruction after (by
      intro invocation hinv
      rcases List.mem_flatMap.mp hinv with ⟨actor, _, hpair⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
      rcases hpair with rfl | rfl <;> exact ⟨actor, rfl⟩)
    (by
      intro actor hmem _
      have hne : actor ≠ owner := by
        intro heq; subst actor
        exact hafterOwnerSet (by simpa [after] using hmem)
      rw [hsubmitter]
      exact fun heq => hne (Option.some.inj heq).symm)
    environment hwaitedLengths (by
      intro actor index hlo hhi
      have hcount := WindowedApplication.ordinaryPolls_player_count afterRoster
        hafterNodup actor
      change after.countP (PolicyAgreement.playerCountFor actor) =
        (if actor ∈ afterRoster then 2 else 0) at hcount
      rw [hcount] at hhi
      split at hhi
      · rename_i hactor
        have hnotBefore : actor ∉ beforeRoster := by
          intro hmem
          exact hsplitNodup.2.2 actor hmem actor (List.mem_cons_of_mem _ hactor) rfl
        have hownerNe : owner ≠ actor := by
          intro heq
          exact hafterOwnerSet (heq ▸ hactor)
        have htotal : (leftWaited.principalHistory actor).length = 3 * blockIndex := by
          have hl := runtime.application.runPolicies_principalHistory_length actor players
            environment (before ++ [.player owner, .player owner]) left leftWaited hpaired.2.1
          rw [hl]
          have hcountBefore := WindowedApplication.ordinaryPolls_player_count beforeRoster
            hbeforeNodup actor
          change before.countP (PolicyAgreement.playerCountFor actor) = _ at hcountBefore
          simp only [List.countP_append, List.countP_cons, List.countP_nil,
            hownerNe, decide_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
          change (left.principalHistory actor).length +
            before.countP (PolicyAgreement.playerCountFor actor) = _
          rw [hcountBefore, if_neg hnotBefore, Nat.add_zero]
          have hactorRoster : actor ∈ roster := by
            rw [hsplit]
            exact List.mem_append_right _ (List.mem_cons_of_mem _ hactor)
          exact hstart actor hactorRoster
        rw [htotal] at hlo hhi
        have : index / 3 = blockIndex := by omega
        rw [this]
        exact hindex
      · omega)
    polledLeft polledRight hleftAfter hrightAfter
  have hschedule : roster.flatMap (fun actor => [Invocation.player actor, .player actor]) =
      (before ++ [.player owner, .player owner]) ++ after := by
    simp [hsplit, before, after, List.append_assoc]
  refine ⟨hafterAgreement, ?_, ?_⟩
  · rw [hschedule, MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨leftWaited, hpaired.2.1, hleftAfter⟩
  · rw [hschedule, MessageApplication.runPolicies_append]
    simp only [FinDist.support_bind, Set.mem_iUnion]
    exact ⟨rightWaited, hpaired.2.2, hrightAfter⟩

end Vegas.WindowedApplication.PolicyAgreement

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.submit_wait_after_gated_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.WindowedApplication.PolicyAgreement.submit_wait_after_gated_prefix

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.ordinary_submit_wait_of_same_input'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.WindowedApplication.PolicyAgreement.ordinary_submit_wait_of_same_input
