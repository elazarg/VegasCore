/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.MessageApplicationRounds
import Interaction.MessageApplicationCheckpoints
import Interaction.MessageApplicationEnvironmentPhases

/-! # Stopped rounds as native trace readouts

A round driver's own boundary command is selected using the environment's
invocation history. All wire decisions still receive the actual observation
and history. Reading the first completed round boundary of the full trace has
exactly the driver's early-stopping law, without an application-specific
clock, completion-persistence, or service assumption.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal}

/-- Player opportunities, wire-service opportunities, then one boundary call. -/
def roundInvocations (principals : List Principal) (serviceSlots : Nat) :
    List (@Invocation Principal) :=
  (principals.map Invocation.player ++ List.replicate serviceSlots .environment) ++
    [.environment]

/-- A bounded invocation schedule, before selecting its stopping boundary. -/
def roundSchedule (principals : List Principal) (serviceSlots : Nat) :
    Nat → List (@Invocation Principal)
  | 0 => []
  | count + 1 => roundInvocations principals serviceSlots ++
      roundSchedule principals serviceSlots count

theorem roundSchedule_length (principals : List Principal) (serviceSlots count : Nat) :
    (roundSchedule principals serviceSlots count).length =
      count * (roundInvocations principals serviceSlots).length := by
  induction count with
  | zero => simp [roundSchedule]
  | succ count ih => simp only [roundSchedule, List.length_append, ih, Nat.succ_mul, Nat.add_comm]

theorem roundSchedule_add (principals : List Principal) (serviceSlots left right : Nat) :
    roundSchedule principals serviceSlots (left + right) =
      roundSchedule principals serviceSlots left ++
        roundSchedule principals serviceSlots right := by
  induction left with
  | zero => simp only [Nat.zero_add, roundSchedule, List.nil_append]
  | succ left ih => simp only [Nat.succ_add, roundSchedule, ih, List.append_assoc]

theorem roundSchedule_take (principals : List Principal) (serviceSlots total count : Nat)
    (hcount : count ≤ total) :
    (roundSchedule principals serviceSlots total).take
        (count * (roundInvocations principals serviceSlots).length) =
      roundSchedule principals serviceSlots count := by
  rw [← Nat.add_sub_of_le hcount,
    roundSchedule_add principals serviceSlots count (total - count),
    ← roundSchedule_length principals serviceSlots count, List.take_left]

theorem roundSchedule_drop (principals : List Principal) (serviceSlots total count : Nat)
    (hcount : count ≤ total) :
    (roundSchedule principals serviceSlots total).drop
        (count * (roundInvocations principals serviceSlots).length) =
      roundSchedule principals serviceSlots (total - count) := by
  rw [← Nat.add_sub_of_le hcount,
    roundSchedule_add principals serviceSlots count (total - count),
    ← roundSchedule_length principals serviceSlots count, List.drop_left]
  simp

/-- Roster membership supplies the same actual player invocation in every
recorded round. Repeated roster entries are permitted. -/
theorem roundSchedule_player (principals : List Principal) (serviceSlots total round slot : Nat)
    (who : Principal) (hround : round < total) (hslot : principals[slot]? = some who) :
    (roundSchedule principals serviceSlots total)[
      round * (roundInvocations principals serviceSlots).length + slot]? = some (.player who) := by
  rw [← List.getElem?_drop, roundSchedule_drop principals serviceSlots total round (by omega)]
  have hremaining : total - round = (total - round - 1) + 1 := by omega
  rw [hremaining, roundSchedule]
  have hslotLength : slot < principals.length := (List.getElem?_eq_some_iff.mp hslot).1
  have hblock : slot < (roundInvocations principals serviceSlots).length := by
    simp only [roundInvocations, List.length_append, List.length_map,
      List.length_replicate, List.length_singleton]
    omega
  have hservice : slot < (principals.map Invocation.player ++
      List.replicate serviceSlots Invocation.environment).length := by
    simp only [List.length_append, List.length_map, List.length_replicate]
    omega
  rw [List.getElem?_append_left hblock, roundInvocations,
    List.getElem?_append_left hservice,
    List.getElem?_append_left (by simpa only [List.length_map] using hslotLength),
    List.getElem?_map, hslot]
  rfl

namespace RoundDriver

variable {app : MessageApplication Principal} [DecidableEq Principal]

/-- The boundary phase uses only the environment's own invocation count. Wire
decisions still receive the complete real history and current observation. -/
def environmentPolicy (driver : RoundDriver app) (serviceSlots : Nat)
    (wire : app.WirePolicy) : app.EnvironmentPolicy :=
  fun history view =>
    if history.length % (serviceSlots + 1) = serviceSlots
    then FinDist.pure (.application driver.boundary)
    else app.wireEnvironment wire history view

omit [DecidableEq Principal] in
private theorem service_invocations_count (principals : List Principal) (serviceSlots : Nat) :
    (principals.map Invocation.player ++ List.replicate serviceSlots Invocation.environment).countP
      Invocation.isEnvironment = serviceSlots := by
  simp [List.countP_replicate, Invocation.isEnvironment, Function.comp_def]

private theorem service_phase (start current slots : Nat)
    (hstart : start % (slots + 1) = 0) (hlo : start ≤ current)
    (hhi : current < start + slots) : current % (slots + 1) ≠ slots := by
  have heq : current = start + (current - start) := by omega
  have hlt : current - start < slots + 1 := by omega
  rw [heq, Nat.add_mod, hstart, Nat.zero_add, Nat.mod_mod,
    Nat.mod_eq_of_lt hlt]
  omega

/-- One round is exactly one invocation block. The phase premise holds at
initialization and is preserved at each successive round boundary. -/
theorem round_eq_runPolicies (driver : RoundDriver app)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → app.PlayerPolicy)
    (wire : app.WirePolicy)
    (execution : app.PolicyExecution)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0) :
    driver.round principals serviceSlots players wire execution =
      app.runPolicies players (driver.environmentPolicy serviceSlots wire)
        (roundInvocations principals serviceSlots) execution := by
  have hservice := app.runPolicies_environment_congr players
    (driver.environmentPolicy serviceSlots wire) (app.wireEnvironment wire)
    (principals.map Invocation.player ++ List.replicate serviceSlots .environment) execution
    (fun history view hlo hhi => by
      rw [service_invocations_count] at hhi
      exact if_neg (service_phase _ _ _ hphase hlo hhi))
  rw [roundInvocations, app.runPolicies_append, hservice]
  unfold MessageApplication.RoundDriver.round
  apply FinDist.bind_congr
  intro next hnext
  have hlength := app.runPolicies_environmentHistory_length players (app.wireEnvironment wire)
    _ execution next hnext
  rw [service_invocations_count] at hlength
  have hboundary : next.environmentHistory.length % (serviceSlots + 1) = serviceSlots := by
    rw [hlength, Nat.add_mod, hphase]
    simp
  simp only [runPolicies, invoke, environmentPolicy, hboundary, ↓reduceIte,
    FinDist.pure_bind, FinDist.bind_pure]

theorem round_environmentHistory_length (driver : RoundDriver app)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → app.PlayerPolicy)
    (wire : app.WirePolicy)
    (execution next : app.PolicyExecution)
    (hnext : next ∈ (driver.round
      principals serviceSlots players wire execution).support) :
    next.environmentHistory.length = execution.environmentHistory.length + (serviceSlots + 1) := by
  simp only [MessageApplication.RoundDriver.round, FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨middle, hmiddle, hnext⟩ := hnext
  have hlength := app.runPolicies_environmentHistory_length
    players (app.wireEnvironment wire) _ execution middle hmiddle
  rw [service_invocations_count] at hlength
  rw [app.environmentStep_history_length middle _ next hnext, hlength]
  omega

/-- Early stopping selects an actual round-boundary snapshot of the same
native run. The equality retains all private and public execution data, not
merely the completed application state. -/
theorem runRounds_eq_tracePolicies (driver : RoundDriver app)
    (principals : List Principal) (serviceSlots : Nat)
    (players : Principal → app.PlayerPolicy)
    (wire : app.WirePolicy) (count : Nat)
    (execution : app.PolicyExecution)
    (hphase : execution.environmentHistory.length % (serviceSlots + 1) = 0) :
    driver.runRounds principals serviceSlots players wire count execution =
      (app.tracePolicies players (driver.environmentPolicy serviceSlots wire)
        (roundSchedule principals serviceSlots count) execution).map
          (PolicyTrace.firstReleaseEvery (roundInvocations principals serviceSlots).length
            (fun state : app.PolicyExecution =>
              driver.complete state.native.application) count) := by
  induction count generalizing execution with
  | zero =>
      simp [MessageApplication.RoundDriver.runRounds, roundSchedule, tracePolicies,
        PolicyTrace.firstReleaseEvery, PolicyTrace.last]
  | succ count ih =>
      rw [roundSchedule, app.tracePolicies_firstReleaseEvery_block
        players (driver.environmentPolicy serviceSlots wire) _ _ execution _ count
        (by simp [roundInvocations])]
      unfold MessageApplication.RoundDriver.runRounds
      split
      · rfl
      · rw [← driver.round_eq_runPolicies principals serviceSlots players wire execution hphase]
        apply FinDist.bind_congr
        intro next hnext
        apply ih next
        rw [driver.round_environmentHistory_length principals serviceSlots players wire
          execution next hnext, Nat.add_mod, hphase]
        simp

end RoundDriver

end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.RoundDriver.runRounds_eq_tracePolicies'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.RoundDriver.runRounds_eq_tracePolicies
