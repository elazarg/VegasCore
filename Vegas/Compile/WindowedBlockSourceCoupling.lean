/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockProgress
import Vegas.Compile.WindowedActivationFreshness

/-! # Source witnesses through an actual relay segment -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A latest-submission service edge can become inactive only by including a
successfully handled pending message. Consequently any constructor-specific
source witness supplied by that handler is inherited by the actual policy
execution. Waiting, a missing pending identifier, and handler rejection all
preserve the active address. -/
theorem environment_latest_source_witness
    (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (actor : P)
    (execution next : runtime.application.PolicyExecution)
    (address : Nat) {G : Graph P L} (Witness : Type)
    (target : Witness → Config G)
    (hpolicy : environment execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native) =
        FinDist.pure (runtime.liftEnvironmentCommand
          (runtime.image.application.latestSubmissionCommand actor
            (runtime.eraseEnvironmentView
              (MessageApplication.State.environmentView runtime.application execution.native)))))
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some address)
    (hinactive : runtime.image.activeAddress? next.native.application.base.memory ≠
      some address)
    (resolve : ∀ message resolved,
      runtime.handle execution.native.application message = some resolved →
      ∃ witness, resolved.base.Refines (target witness) ∧ resolved.FreshActivation)
    (hnext : next ∈ (runtime.application.invoke players environment execution
      .environment).support) :
    ∃ witness, next.native.application.base.Refines (target witness) ∧
      next.native.application.FreshActivation := by
  simp only [MessageApplication.invoke, hpolicy, FinDist.pure_bind] at hnext
  rcases runtime.image.application.latestSubmissionCommand_cases actor
    (runtime.eraseEnvironmentView
      (MessageApplication.State.environmentView runtime.application execution.native)) with
    hwait | ⟨id, hinclude⟩
  · rw [hwait] at hnext
    simp only [liftEnvironmentCommand] at hnext
    simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
      EnvironmentPolicyCommand.toAction, FinDist.pure_bind,
      FinDist.mem_support_pure] at hnext
    subst next
    exact False.elim (hinactive hactive)
  · rw [hinclude] at hnext
    simp only [liftEnvironmentCommand] at hnext
    simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
      EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
      FinDist.mem_support_pure] at hnext
    subst next
    cases hlookup : execution.native.pool.lookup id with
    | none =>
        rw [runtime.application.includePending_missing execution.native id hlookup]
          at hinactive
        exact False.elim (hinactive hactive)
    | some message =>
        cases hhandle : runtime.handle execution.native.application message with
        | none =>
            rw [runtime.application.includePending_reject execution.native id message
              hlookup hhandle] at hinactive
            exact False.elim (hinactive hactive)
        | some resolved =>
            have hincluded := runtime.application.includePending_accept execution.native id
              message resolved hlookup hhandle
            obtain ⟨witness, hresolved, hfresh⟩ := resolve message resolved hhandle
            refine ⟨witness, ?_, ?_⟩
            · rwa [hincluded]
            · rwa [hincluded]

omit [DecidableEq P] in
private theorem relayPairs_environment_count (relays : List P) :
    (relays.flatMap fun relay =>
      [Invocation.player relay, Invocation.environment]).countP
        Invocation.isEnvironment = relays.length := by
  induction relays with
  | nil => rfl
  | cons relay rest ih =>
      simp only [List.flatMap_cons, List.countP_append, List.countP_cons,
        List.countP_nil, Invocation.isEnvironment, Bool.false_eq_true,
        ↓reduceIte, Nat.add_zero, Nat.zero_add, List.length_cons]
      rw [ih]
      omega

/-- A relay segment transports any source witness produced by its first
resolving environment edge. The witness type and represented successor are
constructor-specific; all actual schedule, raw-player, active-prefix, and
inactive-suffix reasoning is shared here. -/
theorem runPolicies_relay_pairs_source_witness
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    (relays : List P) (rosterOffset : Nat)
    (instruction : ApplicationInstruction P L) (owner : P)
    {G : Graph P L} (cfg : Config G)
    (execution final : runtime.application.PolicyExecution)
    (activation : Activation Nat)
    (Witness : Type) (target : Witness → Config G)
    (hrelays : ∀ index actor, relays[index]? = some actor →
      roster[rosterOffset + index]? = some actor)
    (hbound : rosterOffset + relays.length ≤ roster.length)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + relays.length →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (hslot : execution.environmentHistory.length % (roster.length + 2) =
      rosterOffset + 2)
    (howner : instruction.submitter = some owner)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some instruction.address)
    (hactivation : execution.native.application.active = some activation)
    (hrefines : execution.native.application.base.Refines cfg)
    (hinactive : runtime.image.activeAddress? final.native.application.base.memory ≠
      some instruction.address)
    (resolve : ∀ actor index afterPlayer afterRelay,
      roster[index]? = some actor →
      runtime.image.instructions[afterPlayer.environmentHistory.length /
        (roster.length + 2)]? = some instruction →
      afterPlayer.environmentHistory.length % (roster.length + 2) = index + 2 →
      runtime.image.activeAddress? afterPlayer.native.application.base.memory =
        some instruction.address →
      afterPlayer.native.application.active = some activation →
      afterPlayer.native.application.base.Refines cfg →
      runtime.image.activeAddress? afterRelay.native.application.base.memory ≠
        some instruction.address →
      afterRelay ∈ (runtime.application.invoke players
        (runtime.blockEnvironment roster) afterPlayer .environment).support →
      ∃ witness, afterRelay.native.application.base.Refines (target witness) ∧
        afterRelay.native.application.FreshActivation)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster)
      (relays.flatMap fun actor => [Invocation.player actor, .environment])
      execution).support) :
    ∃ witness, final.native.application.base.Refines (target witness) ∧
      final.native.application.FreshActivation := by
  induction relays generalizing rosterOffset execution activation with
  | nil =>
      simp only [List.flatMap_nil, MessageApplication.runPolicies,
        FinDist.mem_support_pure] at hfinal
      subst final
      exact False.elim (hinactive hactive)
  | cons actor rest ih =>
      have hactor : roster[rosterOffset]? = some actor := by
        simpa using hrelays 0 actor rfl
      have hoffset : rosterOffset < roster.length :=
        List.getElem?_eq_some_iff.mp hactor |>.1
      have hpairIndex : ∀ index, execution.environmentHistory.length ≤ index →
          index < execution.environmentHistory.length +
            [Invocation.player actor, Invocation.environment].countP
              Invocation.isEnvironment →
          runtime.image.instructions[index / (roster.length + 2)]? = some instruction := by
        intro index hlo hhi
        apply hindex index hlo
        simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
          Bool.false_eq_true, ↓reduceIte] at hhi
        simp only [List.length_cons]
        omega
      rw [List.flatMap_cons, show
        [Invocation.player actor, Invocation.environment] ++
          rest.flatMap (fun relay => [Invocation.player relay, Invocation.environment]) =
        Invocation.player actor :: Invocation.environment ::
          rest.flatMap (fun relay => [Invocation.player relay, Invocation.environment]) by rfl,
        MessageApplication.runPolicies] at hfinal
      simp only [FinDist.support_bind, Set.mem_iUnion] at hfinal
      obtain ⟨afterPlayer, hplayer, hafterPlayer⟩ := hfinal
      simp only [MessageApplication.runPolicies, FinDist.support_bind,
        Set.mem_iUnion] at hafterPlayer
      obtain ⟨afterRelay, henvironment, hrest⟩ := hafterPlayer
      have hplayerRun : afterPlayer ∈ (runtime.application.runPolicies players
          (runtime.blockEnvironment roster) [Invocation.player actor] execution).support := by
        simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hplayer
      have hpair : afterRelay ∈ (runtime.application.runPolicies players
          (runtime.blockEnvironment roster)
          [Invocation.player actor, Invocation.environment] execution).support := by
        rw [show [Invocation.player actor, Invocation.environment] =
          [Invocation.player actor] ++ [Invocation.environment] by rfl,
          MessageApplication.runPolicies_append, FinDist.support_bind]
        exact Set.mem_iUnion.mpr ⟨afterPlayer, Set.mem_iUnion.mpr ⟨hplayerRun,
          by simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using henvironment⟩⟩
      have hpublic := runtime.runPolicies_players_publicState players
        (runtime.blockEnvironment roster) [Invocation.player actor] (by simp)
        execution afterPlayer hplayerRun
      have hplayerActive : runtime.image.activeAddress?
          afterPlayer.native.application.base.memory = some instruction.address := by
        have hmemory := congrArg Prod.fst hpublic
        change afterPlayer.native.application.base.memory =
          execution.native.application.base.memory at hmemory
        rw [hmemory]
        exact hactive
      have hplayerActivation : afterPlayer.native.application.active = some activation := by
        have hactiveEq := congrArg Prod.snd hpublic
        change afterPlayer.native.application.active = execution.native.application.active
          at hactiveEq
        exact hactiveEq.trans hactivation
      have hplayerRefines : afterPlayer.native.application.base.Refines cfg := by
        exact (runtime.runPolicies_refines_of_final_active roster players
          [Invocation.player actor] execution afterPlayer instruction owner cfg howner (by
            intro index hlo hhi
            simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
              Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hhi
            omega) hrefines hactive hplayerActive hplayerRun).1
      have hplayerLength := runtime.application.runPolicies_environmentHistory_length players
        (runtime.blockEnvironment roster) [Invocation.player actor] execution afterPlayer
        hplayerRun
      have hrelayLength := runtime.application.runPolicies_environmentHistory_length players
        (runtime.blockEnvironment roster) [Invocation.environment] afterPlayer afterRelay
        (by simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using henvironment)
      by_cases hafterActive : runtime.image.activeAddress?
          afterRelay.native.application.base.memory = some instruction.address
      · obtain ⟨hrelayRefines, hrelayActivation, _⟩ :=
          runtime.runPolicies_refines_of_final_active roster players
            [Invocation.player actor, Invocation.environment] execution afterRelay
            instruction owner cfg howner hpairIndex hrefines hactive hafterActive hpair
        cases rest with
        | nil =>
            simp only [List.flatMap_nil, MessageApplication.runPolicies,
              FinDist.mem_support_pure] at hrest
            subst final
            exact False.elim (hinactive hafterActive)
        | cons nextRelay remaining =>
            apply ih (rosterOffset := rosterOffset + 1) (execution := afterRelay)
              (activation := activation)
            · intro index candidate hcandidate
              have hshift : (actor :: nextRelay :: remaining)[index + 1]? =
                  some candidate := by
                simpa [List.getElem?_cons] using hcandidate
              simpa [Nat.add_assoc, Nat.add_comm 1 index, Nat.add_left_comm] using
                hrelays (index + 1) candidate hshift
            · simp only [List.length_cons] at hbound ⊢
              omega
            · intro index hlo hhi
              apply hindex index
              · simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                  Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength hrelayLength
                omega
              · simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                  Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength hrelayLength
                simp only [List.length_cons] at hhi ⊢
                omega
            · simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength hrelayLength
              rw [hrelayLength, hplayerLength]
              simp only [List.length_cons] at hbound
              have hlt : rosterOffset + 2 + 1 < roster.length + 2 := by omega
              have hone : 1 % (roster.length + 2) = 1 :=
                Nat.mod_eq_of_lt (by omega)
              rw [Nat.add_mod, hslot, hone, Nat.mod_eq_of_lt hlt]
            · exact hafterActive
            · exact hrelayActivation.trans hactivation
            · exact hrelayRefines
            · exact resolve
            · exact hrest
      · obtain ⟨witness, hnextRefines, hnextFresh⟩ := resolve actor rosterOffset
          afterPlayer afterRelay hactor
          (by
            rw [hplayerLength]
            apply hindex execution.environmentHistory.length
            · exact Nat.le_refl _
            · simp only [List.length_cons]
              omega)
          (by
            simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
              Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength
            rw [hplayerLength, hslot]) hplayerActive hplayerActivation hplayerRefines
          hafterActive
          (by simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using henvironment)
        refine ⟨witness, ?_, ?_⟩
        · apply runtime.runPolicies_block_inactive_refines (target witness) roster players
            (rest.flatMap fun relay => [Invocation.player relay, Invocation.environment])
            afterRelay final instruction
          · intro index hlo hhi
            apply hindex index
            · simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength hrelayLength
              omega
            · rw [relayPairs_environment_count] at hhi
              simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                  Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength hrelayLength
              simp only [List.length_cons]
              omega
          · exact hafterActive
          · exact hnextRefines
          · exact hrest
        · apply runtime.runPolicies_block_inactive_freshActivation roster players
            (rest.flatMap fun relay => [Invocation.player relay, Invocation.environment])
            afterRelay final instruction
          · intro index hlo hhi
            apply hindex index
            · simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength hrelayLength
              omega
            · rw [relayPairs_environment_count] at hhi
              simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                  Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength hrelayLength
              simp only [List.length_cons]
              omega
          · exact hafterActive
          · exact hnextFresh
          · exact hrest

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.environment_latest_source_witness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.environment_latest_source_witness

/-- info: 'Vegas.WindowedApplication.runPolicies_relay_pairs_source_witness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_relay_pairs_source_witness
