/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkSource
import Vegas.Game.SourceServiceWaitRiskConfounding
import Vegas.Game.ServiceRosterAsync
import Interaction.ReactiveRawRoundTrace

/-! # A public command-order fork before Alice's resolution

The builder includes the clean second call certainly. Only after the actual
tick-before-activation order does it randomize between including the last
Alice packet and including only withholding. The order is read from genuine
public scheduler command recall, which is absent from Bob's player input.
An all-history asynchronous service certificate is a separate obligation.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

def leaks : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph) :=
  fun _ _ => PMF.pure ∅

abbrev app := application setup leaks

def lastTick (history : List app.EnvironmentEntry) : Bool :=
  history.getLast?.any (fun entry => match entry.command with
    | .application .advanceClock => true
    | _ => false)

def latestAliceWithhold (view : app.EnvironmentView) : app.Command := by
  classical
  exact match view.network.pending.reverse.find? (fun message =>
    decide (message.sender = alice ∧ message.payload.call = .withhold aliceResolution ∧
      view.Unpublished app message.id)) with
  | none => .wait
  | some message => .include message.id

def stageCommand (stage : Nat) (history : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : app.Command :=
  match stage with
  | 0 => .application (.executeSample sample0)
  | 1 => .application (.executeSample sample1)
  | 2 => .activate alice
  | 3 | 6 => (runtime setup).reactiveLatest leaks aliceResolution alice view
  | 5 => if lastTick history then .activate alice else .application .advanceClock
  | 7 | 8 => .application .advanceClock
  | 9 => .application (.expire aliceResolution)
  | 10 => .activate bob
  | 11 => (runtime setup).reactiveLatest leaks bobResolution bob view
  | 12 | 13 | 14 | 15 => .application .advanceClock
  | 16 => .application (.expire bobResolution)
  | _ => .wait

def scheduler : app.Scheduler := fun history view =>
  if history.length = 4 then mix (9 / 10) (by norm_num) (by norm_num)
    (PMF.pure (.activate alice)) (PMF.pure (.application .advanceClock))
  else if history.length = 6 ∧ lastTick history = false then
    mix (3 / 4) (by norm_num) (by norm_num)
      (PMF.pure ((runtime setup).reactiveLatest leaks aliceResolution alice view))
      (PMF.pure (latestAliceWithhold view))
  else PMF.pure (stageCommand history.length history view)

def horizon : Nat := 17

def delay (event : nativeGraph.EventId) : Nat := if event = bobResolution then 3 else 0

def bound (event : nativeGraph.EventId) : Nat := if event = aliceResolution then 2 else 0

theorem timely : AsyncTimely (runtime setup) delay bound := by
  intro event owned
  change Fin 4 at event
  fin_cases event
  · change false = true at owned
    contradiction
  · change false = true at owned
    contradiction
  · change 0 + 2 < 3
    decide
  · change 3 + 0 < 4
    decide

theorem scheduler_clean_second (history : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (stage : history.length = 6)
    (clean : lastTick history = true) :
    scheduler history view =
      PMF.pure ((runtime setup).reactiveLatest leaks aliceResolution alice view) := by
  simp [scheduler, stage, clean, stageCommand]

theorem scheduler_risky_second (history : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (stage : history.length = 6)
    (risky : lastTick history = false) :
    scheduler history view = mix (3 / 4) (by norm_num) (by norm_num)
      (PMF.pure ((runtime setup).reactiveLatest leaks aliceResolution alice view))
      (PMF.pure (latestAliceWithhold view)) := by
  simp [scheduler, stage, risky]

theorem clean_second_command_record (execution : app.Execution) (response : app.Action) :
    lastTick (WaitRiskConfounding.advance (runtime setup) leaks
      ((WaitRiskConfounding.activate (runtime setup) leaks execution alice).respond app alice
        response)).environmentRecall = true := by
  simp [lastTick, WaitRiskConfounding.advance]

theorem risky_second_command_record (execution : app.Execution) (response : app.Action) :
    lastTick ((WaitRiskConfounding.activate (runtime setup) leaks
      (WaitRiskConfounding.advance (runtime setup) leaks execution) alice).respond app alice
        response).environmentRecall = false := by
  rw [app.respond_environmentRecall]
  simp [lastTick, WaitRiskConfounding.activate]

theorem post_inclusion_second_bob_input (execution : app.Execution) (response : app.Action)
    (id : MessageId Player) :
    let clean := (WaitRiskConfounding.advance (runtime setup) leaks
      ((WaitRiskConfounding.activate (runtime setup) leaks execution alice).respond app alice
        response)).includePending app id
    let risky := ((WaitRiskConfounding.activate (runtime setup) leaks
      (WaitRiskConfounding.advance (runtime setup) leaks execution) alice).respond app alice
        response).includePending app id
    (clean.recall bob, clean.observe app bob) = (risky.recall bob, risky.observe app bob) :=
  WaitRiskConfounding.response_advance_foreign_input (runtime setup) leaks execution alice bob
    (by decide) response id

end Vegas.PrivateResolutionFork
