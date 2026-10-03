/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.DisclosureProfilePrefix
import Vegas.Game.DisclosureRetraction

/-! # The common original-source lottery retracts to the effective prefix

Simultaneous deterministic recall compression reverses the same finite owner
restoration used by the behavioral normalizer. Every supported original source
state compresses to its actual effective prefix. Its focal observation is read
by the existing observation-local recall map, so ancillary source-view traffic
can be carried through restoration without an assumed information-fiber law.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}

private def normalizeDisclosureRecallList
    (program : SourceProgram Player L Γ O) : List Player → ProtocolState program →
      ProtocolState program
  | [], state => state
  | who :: others, state =>
      ProtocolState.normalizeDisclosureRecall (who := who) program (fun view => view.2)
        (normalizeDisclosureRecallList program others state)

/-- Compress every player's private disclosure recall using the same finite
enumeration as the common original-memory lottery, in reverse restoration
order. Typed game data and protocol position remain unchanged. -/
def ProtocolState.normalizeDisclosureProfileRecall
    (program : SourceProgram Player L Γ O) (state : ProtocolState program) :
    ProtocolState program := normalizeDisclosureRecallList program Finset.univ.toList state

omit [Fintype Player] in
private theorem observe_normalizeDisclosureRecallList
    (program : SourceProgram Player L Γ O) (owners : List Player) (distinct : owners.Nodup)
    (focal : Player) (state : ProtocolState program) :
    ProtocolState.observe focal program (normalizeDisclosureRecallList program owners state) =
      if focal ∈ owners then
        ProtocolView.normalizeDisclosureRecall program (fun view => view.2)
          (ProtocolState.observe focal program state)
      else ProtocolState.observe focal program state := by
  classical
  induction owners generalizing state with
  | nil => simp only [normalizeDisclosureRecallList, List.not_mem_nil, ite_false]
  | cons who others ih =>
      obtain ⟨absent, distinct⟩ := List.nodup_cons.mp distinct
      by_cases own : focal = who
      · subst focal
        rw [normalizeDisclosureRecallList, ProtocolState.observe_normalizeDisclosureRecall,
          ih distinct, ite_eq_right absent]
        simp only [List.mem_cons_self, ite_true]
      · rw [normalizeDisclosureRecallList,
          ProtocolState.foreign_observe_normalizeDisclosureRecall focal own,
          ih distinct]
        simp only [List.mem_cons, own, false_or]

/-- The complete simultaneous compression is information-local for every
player: its focal view is exactly the existing own-recall compression. -/
theorem ProtocolState.observe_normalizeDisclosureProfileRecall
    (program : SourceProgram Player L Γ O) (focal : Player) (state : ProtocolState program) :
    observe focal program (normalizeDisclosureProfileRecall program state) =
      ProtocolView.normalizeDisclosureRecall program (fun view => view.2)
        (observe focal program state) := by
  classical
  simpa only [normalizeDisclosureProfileRecall, Finset.mem_toList, Finset.mem_univ,
    ite_true] using observe_normalizeDisclosureRecallList program Finset.univ.toList
      (Finset.nodup_toList _) focal state

private theorem disclosure_list_prefix_retracts
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (config : Config Player L Γ) (count : Nat) (owners : List Player)
    (distinct : owners.Nodup) (state : ProtocolState program)
    (reached : state ∈ ((fun law => law.bind (ProtocolState.behavioralStateStep program
      (fun who => if who ∈ owners then
        (profile who).normalizeDisclosures program config.registry config.revelations
      else profile who)))^[count]
        (PMF.pure (ProtocolState.entry program config))).support)
    (original : ProtocolState program)
    (restored : original ∈ (restoreDisclosureList program config.registry config.revelations
      profile owners state).support) :
    normalizeDisclosureRecallList program owners original = state := by
  classical
  induction owners generalizing state original with
  | nil =>
      change original ∈ (PMF.pure state).support at restored
      cases (PMF.mem_support_pure_iff _ _).mp restored
      rfl
  | cons who others ih =>
      obtain ⟨absent, distinct⟩ := List.nodup_cons.mp distinct
      let translated := normalizeDisclosureProfile program config.registry config.revelations
        profile
      let previous : BehavioralProfile program := fun player =>
        if player ∈ others then translated player else profile player
      let current : BehavioralProfile program := fun player =>
        if player ∈ who :: others then translated player else profile player
      have unchanged : Function.update previous who (profile who) = previous := by
        funext player
        by_cases same : player = who
        · subst player
          simp only [Function.update_self, previous, absent, ite_false]
        · exact Function.update_of_ne same _ _
      have added : Function.update previous who (translated who) = current := by
        funext player
        by_cases same : player = who
        · subst player
          simp only [Function.update_self, current, List.mem_cons_self, ite_true]
        · simp only [Function.update_of_ne same, current, previous, List.mem_cons,
            same, false_or]
      have expanded := normalized_disclosure_prefix program previous (profile who) config count
      rw [unchanged] at expanded
      change (fun law => law.bind (ProtocolState.behavioralStateStep program previous))^[count]
          (PMF.pure (ProtocolState.entry program config)) =
        ((fun law => law.bind (ProtocolState.behavioralStateStep program
          (Function.update previous who (translated who))))^[count]
            (PMF.pure (ProtocolState.entry program config))).bind
              ((profile who).disclosureMemory program config.registry config.revelations
                (fun view => PMF.pure view.2)) at expanded
      rw [added] at expanded
      change original ∈ (((profile who).disclosureMemory program config.registry
          config.revelations (fun view => PMF.pure view.2) state).bind
        (restoreDisclosureList program config.registry config.revelations profile others)).support
        at restored
      obtain ⟨middle, remembered, originalSupport⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ restored)
      have middleReached : middle ∈ ((fun law => law.bind
          (ProtocolState.behavioralStateStep program previous))^[count]
            (PMF.pure (ProtocolState.entry program config))).support := by
        rw [expanded, PMF.support_bind]
        exact Set.mem_iUnion₂.mpr ⟨state, reached, remembered⟩
      have before := ih distinct middle middleReached original originalSupport
      have retract := disclosure_prefix_retracts program previous (profile who)
        (fun view => PMF.pure view.2) (fun view => view.2) config
        (fun past member => (PMF.mem_support_pure_iff _ _).mp member) count state
        (by
          change state ∈ ((fun law => law.bind (ProtocolState.behavioralStateStep program
            (Function.update previous who (translated who))))^[count]
              (PMF.pure (ProtocolState.entry program config))).support
          rw [added]
          exact reached)
        middle remembered
      rw [normalizeDisclosureRecallList, before]
      exact retract

/-- Every supported output of the actual common memory lottery compresses
back to the same normalized source prefix from which it was sampled. -/
theorem normalizeDisclosureProfile_prefix_retracts
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (config : Config Player L Γ) (count : Nat) (state : ProtocolState program)
    (reached : state ∈ ((fun law => law.bind (ProtocolState.behavioralStateStep program
      (normalizeDisclosureProfile program config.registry config.revelations profile)))^[count]
        (PMF.pure (ProtocolState.entry program config))).support)
    (original : ProtocolState program)
    (restored : original ∈ (profile.restoreDisclosureMemory program config.registry
      config.revelations state).support) :
    ProtocolState.normalizeDisclosureProfileRecall program original = state := by
  classical
  exact disclosure_list_prefix_retracts program profile config count Finset.univ.toList
    (Finset.nodup_toList _) state (by
      unfold normalizeDisclosureProfile at reached
      simpa only [Finset.mem_toList, Finset.mem_univ, ite_true] using reached) original restored

/-- The simultaneously normalized source prefix is the deterministic common
recall compression of the complete original source prefix. -/
theorem normalizeDisclosureProfile_prefix_map
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (config : Config Player L Γ) (count : Nat) :
    ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count]
      (PMF.pure (ProtocolState.entry program config))).map
        (ProtocolState.normalizeDisclosureProfileRecall program) =
      (fun law => law.bind (ProtocolState.behavioralStateStep program
        (normalizeDisclosureProfile program config.registry config.revelations profile)))^[count]
          (PMF.pure (ProtocolState.entry program config)) := by
  rw [normalizeDisclosureProfile_prefix_disintegration, PMF.map_bind]
  trans ((fun law => law.bind (ProtocolState.behavioralStateStep program
    (normalizeDisclosureProfile program config.registry config.revelations profile)))^[count]
      (PMF.pure (ProtocolState.entry program config))).bind PMF.pure
  · apply bind_congr_on_support _
    intro state reached
    calc
      _ = (profile.restoreDisclosureMemory program config.registry config.revelations state).map
          (fun _ => state) := by
        apply map_congr_on_support _
        intro original restored
        exact normalizeDisclosureProfile_prefix_retracts program profile config count state
          reached original restored
      _ = PMF.pure state := PMF.map_const _ _
  · exact PMF.bind_pure _

/-- An arbitrary ancillary channel that reads the effective source view is
preserved through the actual all-owner original-memory lottery. Its weights at
an original source state are obtained by the proved observation compression,
with no assumed posterior or information-fiber equation. -/
theorem normalizeDisclosureProfile_prefix_channel {Noise : Type}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (config : Config Player L Γ) (count : Nat) (focal : Player)
    (noise : ProtocolView focal program → PMF Noise) :
    let normalized := (fun law => law.bind (ProtocolState.behavioralStateStep program
      (normalizeDisclosureProfile program config.registry config.revelations profile)))^[count]
        (PMF.pure (ProtocolState.entry program config))
    (normalized.bind fun state => (noise (ProtocolState.observe focal program state)).bind
      fun extra => (profile.restoreDisclosureMemory program config.registry config.revelations
        state).map fun original => (original, extra)) =
      ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count]
        (PMF.pure (ProtocolState.entry program config))).bind fun original =>
          (noise (ProtocolView.normalizeDisclosureRecall program (fun view => view.2)
            (ProtocolState.observe focal program original))).map
              fun extra => (original, extra) := by
  intro normalized
  rw [normalizeDisclosureProfile_prefix_disintegration, PMF.bind_bind]
  apply bind_congr_on_support _
  intro state reached
  trans (profile.restoreDisclosureMemory program config.registry config.revelations state).bind
    (fun original => (noise (ProtocolState.observe focal program state)).map
      fun extra => (original, extra))
  · simpa only [← PMF.bind_pure_comp, Function.comp_def] using
      PMF.bind_comm (noise (ProtocolState.observe focal program state))
        (profile.restoreDisclosureMemory program config.registry config.revelations state)
        (fun extra original => PMF.pure (original, extra))
  apply bind_congr_on_support _
  intro original restored
  have retracted := normalizeDisclosureProfile_prefix_retracts program profile config count state
    reached original restored
  have observed := ProtocolState.observe_normalizeDisclosureProfileRecall program focal original
  rw [retracted] at observed
  rw [observed]

end Vegas.SourceProgram
