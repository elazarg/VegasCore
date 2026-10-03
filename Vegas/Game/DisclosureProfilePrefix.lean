/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.DisclosurePrefix

/-! # A common original source carrier at every normalized prefix

Each player's actual disclosure-memory kernel restores its private intentions
and retains the other players' histories. Composing those kernels recovers the
complete original source prefix under simultaneous behavioral normalization.
The proof telescopes the one-player realization against arbitrary opponents;
it assumes no independence between the restored memories or initial types.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}

private def restoreDisclosureList
    (program : SourceProgram Player L Γ O) (registry : Registry Γ)
    (revelations : Revelations Γ) (profile : BehavioralProfile program) :
    List Player → ProtocolState program → PMF (ProtocolState program)
  | [], state => PMF.pure state
  | who :: others, state =>
      ((profile who).disclosureMemory program registry revelations
        (fun view => PMF.pure view.2) state).bind
          (restoreDisclosureList program registry revelations profile others)

/-- Restore all original private intention lists at this actual source
protocol state. A finite enumeration is derived from the player type. Each
restoration retains the memories restored by earlier coordinates. -/
def BehavioralProfile.restoreDisclosureMemory
    (program : SourceProgram Player L Γ O) (registry : Registry Γ)
    (revelations : Revelations Γ) (profile : BehavioralProfile program)
    (state : ProtocolState program) : PMF (ProtocolState program) :=
  restoreDisclosureList program registry revelations profile Finset.univ.toList state

private theorem normalize_disclosure_list_prefix
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (config : Config Player L Γ) (count : Nat) (owners : List Player)
    (distinct : owners.Nodup) :
    (fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count]
        (PMF.pure (ProtocolState.entry program config)) =
      ((fun law => law.bind (ProtocolState.behavioralStateStep program
        (fun who => if who ∈ owners then
          (profile who).normalizeDisclosures program config.registry config.revelations
        else profile who)))^[count]
          (PMF.pure (ProtocolState.entry program config))).bind
            (restoreDisclosureList program config.registry config.revelations profile owners) := by
  classical
  induction owners with
  | nil => simp only [List.not_mem_nil, ite_false, restoreDisclosureList, PMF.bind_pure]
  | cons who others ih =>
      obtain ⟨absent, distinct⟩ := List.nodup_cons.mp distinct
      let translated := normalizeDisclosureProfile program config.registry config.revelations
        profile
      let previous : BehavioralProfile program := fun player =>
        if player ∈ others then translated player else profile player
      let current : BehavioralProfile program := fun player =>
        if player ∈ who :: others then translated player else profile player
      have original : Function.update previous who (profile who) = previous := by
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
      have one := normalized_disclosure_prefix program previous (profile who) config count
      rw [original] at one
      change (fun law => law.bind (ProtocolState.behavioralStateStep program previous))^[count]
          (PMF.pure (ProtocolState.entry program config)) =
        ((fun law => law.bind (ProtocolState.behavioralStateStep program
          (Function.update previous who (translated who))))^[count]
            (PMF.pure (ProtocolState.entry program config))).bind
              ((profile who).disclosureMemory program config.registry config.revelations
                (fun view => PMF.pure view.2)) at one
      rw [added] at one
      rw [ih distinct]
      change (((fun law => law.bind (ProtocolState.behavioralStateStep program previous))^[count]
        (PMF.pure (ProtocolState.entry program config))).bind _) = _
      rw [one, PMF.bind_bind]
      rfl

/-- Simultaneous disclosure normalization has an exact common original
protocol-state law at every finite prefix, including intermediate private
histories. The restoration uses the actual normalizer's memory kernels. -/
theorem normalizeDisclosureProfile_prefix_disintegration
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (config : Config Player L Γ) (count : Nat) :
    (fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count]
        (PMF.pure (ProtocolState.entry program config)) =
      ((fun law => law.bind (ProtocolState.behavioralStateStep program
        (normalizeDisclosureProfile program config.registry config.revelations profile)))^[count]
          (PMF.pure (ProtocolState.entry program config))).bind
            (profile.restoreDisclosureMemory program config.registry config.revelations) := by
  classical
  have law := normalize_disclosure_list_prefix program profile config count Finset.univ.toList
    (Finset.nodup_toList _)
  unfold BehavioralProfile.restoreDisclosureMemory normalizeDisclosureProfile
  simpa only [Finset.mem_toList, Finset.mem_univ, ite_true] using law

/-- The same common original-prefix law retains arbitrary correlated initial
parameters. Static registry and revelation positions are fixed; no independent
initial-type or private-memory hypothesis is required. -/
theorem normalizeDisclosureProfile_prefix_joint_law {Parameter : Type}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (belief : PMF (Config Player L Γ))
    (registryEq : ∀ config ∈ belief.support, config.registry = registry)
    (revelationsEq : ∀ config ∈ belief.support, @config.revelations = @revelations)
    (parameter : Config Player L Γ → Parameter) (count : Nat) :
    (belief.bind fun config =>
      (((fun law => law.bind (ProtocolState.behavioralStateStep program
        (normalizeDisclosureProfile program registry revelations profile)))^[count]
          (PMF.pure (ProtocolState.entry program config))).bind
            (profile.restoreDisclosureMemory program registry revelations)).map
              (fun state => (parameter config, state))) =
      belief.bind fun config =>
        ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count]
          (PMF.pure (ProtocolState.entry program config))).map
            (fun state => (parameter config, state)) := by
  apply bind_congr_on_support _
  intro config supported
  have law := normalizeDisclosureProfile_prefix_disintegration program profile config count
  rw [registryEq config supported, revelationsEq config supported] at law
  exact congrArg (PMF.map (fun state => (parameter config, state))) law.symm

end Vegas.SourceProgram
