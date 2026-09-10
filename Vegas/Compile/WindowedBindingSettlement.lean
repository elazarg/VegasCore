/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockProgress
import Interaction.MessageApplicationHistoryCounts

/-! # Support-total settlement of a ready binding block -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem relayPrefix_player_count_eq_zero (before : List P) (who : P)
    (hnotmem : who ∉ before) :
    (before.flatMap fun actor =>
      [Invocation.player actor, Invocation.environment]).countP (fun invocation =>
        match invocation with
        | .player actor => decide (actor = who)
        | .environment => false) = 0 := by
  induction before with
  | nil => rfl
  | cons actor rest ih =>
      simp only [List.mem_cons, not_or] at hnotmem
      have hne : actor ≠ who := fun h => hnotmem.1 (h ▸ rfl)
      simp [List.flatMap_cons, hne, ih hnotmem.2]

omit [DecidableEq P] in
private theorem relayPrefix_environment_count (before : List P) :
    (before.flatMap fun actor =>
      [Invocation.player actor, Invocation.environment]).countP
        Invocation.isEnvironment = before.length := by
  induction before with
  | nil => rfl
  | cons actor rest ih =>
      simp [List.flatMap_cons, Invocation.isEnvironment, ih]

/-- A roster split identifies the unchanged relay pair. Every still-active
outcome before that pair has the concrete source-certified binding expiry;
an earlier accepting relay instead makes the remainder inactive. Thus every
supported outcome after the complete relay suffix has settled the binding. -/
theorem binding_relay_roster_inactive
    (runtime : WindowedApplication P L)
    (beforeRoster afterRoster : List P) (sourceOwner relay : P)
    (hroster : (beforeRoster ++ relay :: afterRoster).Nodup)
    (base : runtime.application.PlayerPolicy)
    (players : P → runtime.application.PlayerPolicy)
    (hrelay : players relay = runtime.blockPlayer relay base)
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx sourceOwner Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed sourceOwner ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name sourceOwner guard tail))
    (build : BuildState P L Γ) (deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name sourceOwner guard tail) fresh build).graph build)
    (instruction : ApplicationInstruction P L) (activation : Activation Nat)
    (execution final : runtime.application.PolicyExecution)
    (howner : instruction.submitter = some sourceOwner)
    (hplayerIndex : runtime.image.instructions[(execution.principalHistory relay).length /
      3]? = some instruction)
    (hplayerSlot : (execution.principalHistory relay).length % 3 = 2)
    (henvironmentSlot : execution.environmentHistory.length %
      ((beforeRoster ++ relay :: afterRoster).length + 2) = 1)
    (hindexRange : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length +
        (beforeRoster.length + afterRoster.length + 2) →
      runtime.image.instructions[index /
        ((beforeRoster ++ relay :: afterRoster).length + 2)]? = some instruction)
    (hactive : runtime.image.activeAddress?
      execution.native.application.base.memory = some instruction.address)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = instruction.address)
    (hcode : runtime.image.lookup activation.key = some (.bind
      (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hconsistent : runtime.Consistent execution.native.application)
    (hserials : execution.native.pool.SerialsBeforeNext)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment (beforeRoster ++ relay :: afterRoster))
      ([Invocation.environment] ++ beforeRoster.flatMap (fun actor =>
        [Invocation.player actor, Invocation.environment]) ++
          [Invocation.player relay, Invocation.environment] ++
          afterRoster.flatMap (fun actor =>
            [Invocation.player actor, Invocation.environment]))
      execution).support) :
    runtime.image.activeAddress? final.native.application.base.memory ≠
      some instruction.address := by
  let roster := beforeRoster ++ relay :: afterRoster
  let before : List (@Invocation P) := [Invocation.environment] ++
    beforeRoster.flatMap (fun actor =>
      [Invocation.player actor, Invocation.environment])
  let suffix : List (@Invocation P) := afterRoster.flatMap (fun actor =>
    [Invocation.player actor, Invocation.environment])
  have hrelayIndex : roster[beforeRoster.length]? = some relay := by
    simp [roster]
  apply runtime.runPolicies_relay_segment_inactive roster players relay base hrelay
    instruction beforeRoster.length hrelayIndex before suffix execution
  · intro middle hmiddle index hlo hhi
    have henvironmentLength := runtime.application.runPolicies_environmentHistory_length players
      (runtime.blockEnvironment roster) before execution middle hmiddle
    apply hindexRange index
    · simp only [before, List.countP_append, List.countP_cons, List.countP_nil,
        Invocation.isEnvironment, ↓reduceIte, relayPrefix_environment_count]
        at henvironmentLength
      omega
    · simp only [before, suffix, List.countP_append, List.countP_cons,
        List.countP_nil, Invocation.isEnvironment, ↓reduceIte,
        Bool.false_eq_true, relayPrefix_environment_count] at hhi henvironmentLength ⊢
      omega
  · intro middle hmiddle hmiddleActive
    have hnotmem : relay ∉ beforeRoster := by
      intro hmem
      exact (List.nodup_append.mp hroster).2.2 relay hmem relay (by simp) rfl
    have hplayerLength := runtime.application.runPolicies_principalHistory_length relay
      players (runtime.blockEnvironment roster) before execution middle hmiddle
    have henvironmentLength := runtime.application.runPolicies_environmentHistory_length players
      (runtime.blockEnvironment roster) before execution middle hmiddle
    simp only [before, List.countP_append, List.countP_cons, List.countP_nil,
      Invocation.isEnvironment, ↓reduceIte] at hplayerLength henvironmentLength
    have hplayerLength' : (middle.principalHistory relay).length =
        (execution.principalHistory relay).length := by
      rw [hplayerLength]
      simp only [Nat.add_eq_left]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      apply List.countP_eq_zero.mpr
      intro invocation hmem
      cases invocation with
      | environment => simp
      | player actor =>
          simp only [List.mem_flatMap] at hmem
          obtain ⟨candidate, hcandidate, hpair⟩ := hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
          rcases hpair with heq | hfalse
          · have hactor : actor = candidate := Invocation.player.inj heq
            subst actor
            intro h
            have heq : candidate = relay := of_decide_eq_true h
            exact hnotmem (heq ▸ hcandidate)
          · simp at hfalse
    rw [relayPrefix_environment_count] at henvironmentLength
    obtain ⟨payload, resolved, hdue, hfresh, hhandle, _⟩ :=
      runtime.binding_source_relay_eligibility_after_clock roster players guard tail
        fallback fresh build deadline current instruction activation execution middle
        (beforeRoster.flatMap fun actor =>
          [Invocation.player actor, Invocation.environment]) relay howner
        (by
          intro index hlo hhi
          apply hindexRange index hlo
          simp only [List.countP_cons, Invocation.isEnvironment, ↓reduceIte,
            relayPrefix_environment_count] at hhi
          omega) henvironmentSlot hactive hactivation hkey hcode hrefines hconsistent
        hserials hmiddleActive (by simpa [before] using hmiddle)
    refine ⟨payload, resolved, ?_, ?_, ?_, ?_, hdue, hfresh, hhandle, ?_⟩
    · rwa [hplayerLength']
    · rwa [hplayerLength']
    · apply hindexRange middle.environmentHistory.length
      · omega
      · omega
    · have hslot' : execution.environmentHistory.length % (roster.length + 2) = 1 := by
        simpa [roster] using henvironmentSlot
      have hlt : 1 + beforeRoster.length < roster.length + 2 := by
        simp [roster]
        omega
      have hwhole : 1 + (1 + beforeRoster.length) < roster.length + 2 := by
        simp [roster]
        omega
      rw [henvironmentLength, Nat.add_mod, hslot', Nat.mod_eq_of_lt hlt,
        Nat.mod_eq_of_lt hwhole]
      omega
    · intro index hlo hhi
      apply hindexRange index
      · omega
      · simp only [suffix, relayPrefix_environment_count] at hhi ⊢
        omega
  · simpa [before, suffix, List.append_assoc] using hfinal

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.binding_relay_roster_inactive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.binding_relay_roster_inactive
