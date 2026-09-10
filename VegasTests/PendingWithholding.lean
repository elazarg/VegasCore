/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.PendingRelease
import VegasTests.PendingSnapshots

/-! # Informed withholding after the compiled release boundary

This deterministic control uses the actual checked pending-choice application.
Player one binds `some false` before release, but after observing player zero's
included opening submits its own opening only when that value is `some false`.
The other branch remains pending; it is not reinterpreted as source `none`.
-/

namespace VegasTests.PendingWithholding

open Interaction Interaction.SealedProgram GameTheory GameTheory.Math.Probability
open Interaction.MessageApplication
open VegasTests.PendingSource VegasTests.PendingExecution
open VegasTests.PendingPolicies VegasTests.PendingSnapshots

noncomputable section

def withholding : Application.PlayerPolicy := fun history view =>
  match history.length with
  | 0 => FinDist.pure (.privateCommand ⟨(1, some false)⟩)
  | 1 => FinDist.pure (.submit (.commitment 1 (1, 1)))
  | _ + 2 =>
      match view.messages.inbox with
      | ⟨_, .opening 2 (0, 0) (some false)⟩ :: _ =>
          FinDist.pure (.submit (.opening 3 (1, 1) (some false)))
      | _ => FinDist.pure .wait

def profile (value : Value) :
    Profile (MessageApplication.policySignature Player Application) :=
  Profile.update (fun _ => withholding) 0 (commitOpenPolicy program 0 0 2 value)

def environment : Application.EnvironmentPolicy := fun history _ =>
  match history.length with
  | 0 => FinDist.pure (.include (0, 0))
  | 1 => FinDist.pure (.include (1, 0))
  | 2 => FinDist.pure (.deliver 1 (0, 1))
  | 3 => FinDist.pure (.include (0, 1))
  | 4 => FinDist.pure (.include (1, 1))
  | _ => FinDist.pure .wait

def schedule : List (@MessageApplication.Invocation Player) :=
  [.player 0, .player 0, .player 1, .player 1,
   .environment, .environment, .player 0, .environment,
   .environment, .player 1, .environment]

def law (value : Value) : FinDist Application.PolicyExecution :=
  (Application.policyGame environment schedule applicationInitial).play (profile value)

def responseCommand : Value → Application.PlayerCommand
  | some false => .submit (.opening 3 (1, 1) (some false))
  | _ => .wait

def s0 : Application.PolicyExecution := initialExecution
def s1 (v : Value) := playerSnapshot 0 s0 (.privateCommand ⟨(0, v)⟩)
  { s0.native with application := Application.privateStep s0.native.application 0 ⟨(0, v)⟩ }
def s2 (v : Value) := playerSnapshot 0 (s1 v) (.submit (.commitment 0 (0, 0)))
  { (s1 v).native with pool := ((s1 v).native.pool.submit 0 (.commitment 0 (0, 0))).2 }
def s3 (v : Value) := playerSnapshot 1 (s2 v) (.privateCommand ⟨(1, some false)⟩)
  { (s2 v).native with application :=
      Application.privateStep (s2 v).native.application 1 ⟨(1, some false)⟩ }
def s4 (v : Value) := playerSnapshot 1 (s3 v) (.submit (.commitment 1 (1, 1)))
  { (s3 v).native with pool := ((s3 v).native.pool.submit 1 (.commitment 1 (1, 1))).2 }
def s5 (v : Value) := environmentSnapshot (s4 v) (.include (0, 0))
  (Application.includePending (s4 v).native (0, 0))
def s6 (v : Value) := environmentSnapshot (s5 v) (.include (1, 0))
  (Application.includePending (s5 v).native (1, 0))
def s7 (v : Value) := playerSnapshot 0 (s6 v) (.submit (.opening 2 (0, 0) v))
  { (s6 v).native with pool := ((s6 v).native.pool.submit 0 (.opening 2 (0, 0) v)).2 }
def s8 (v : Value) := environmentSnapshot (s7 v) (.deliver 1 (0, 1))
  { (s7 v).native with pool := ((s7 v).native.pool.deliver 1 (0, 1)).state }
def s9 (v : Value) := environmentSnapshot (s8 v) (.include (0, 1))
  (Application.includePending (s8 v).native (0, 1))

def responseNative (v : Value) : Application.State :=
  match v with
  | some false =>
      { (s9 v).native with pool :=
        ((s9 v).native.pool.submit 1 (.opening 3 (1, 1) (some false))).2 }
  | _ => (s9 v).native

def s10 (v : Value) := playerSnapshot 1 (s9 v) (responseCommand v) (responseNative v)
def s11 (v : Value) := environmentSnapshot (s10 v) (.include (1, 1))
  (Application.includePending (s10 v).native (1, 1))

private theorem invokePlayerPure (v : Value) (execution : Application.PolicyExecution)
    (who : Player) (command : Application.PlayerCommand) (native : Application.State)
    (hpolicy : profile v who (execution.principalHistory who)
      (MessageApplication.State.observe Application execution.native who) =
        FinDist.pure command)
    (hnative : (match command.toAction Application who with
      | none => FinDist.pure execution.native
      | some action => Application.step execution.native action) = FinDist.pure native) :
    Application.invoke (profile v) environment execution (.player who) =
      FinDist.pure (playerSnapshot who execution command native) := by
  rw [MessageApplication.invoke, hpolicy, FinDist.pure_bind]
  exact playerStep_snapshot who execution command native hnative

private theorem invokeEnvironmentPure (v : Value) (execution : Application.PolicyExecution)
    (command : Application.EnvironmentPolicyCommand) (native : Application.State)
    (hpolicy : environment execution.environmentHistory
      (MessageApplication.State.environmentView Application execution.native) =
        FinDist.pure command)
    (hnative : (match command.toAction with
      | none => FinDist.pure execution.native
      | some action => Application.step execution.native action) = FinDist.pure native) :
    Application.invoke (profile v) environment execution .environment =
      FinDist.pure (environmentSnapshot execution command native) := by
  rw [MessageApplication.invoke, hpolicy, FinDist.pure_bind]
  exact environmentStep_snapshot execution command native hnative

private theorem i0 (v : Value) :
    Application.invoke (profile v) environment s0 (.player 0) = FinDist.pure (s1 v) := by
  apply invokePlayerPure <;> cases v <;> rfl
private theorem i1 (v : Value) :
    Application.invoke (profile v) environment (s1 v) (.player 0) = FinDist.pure (s2 v) := by
  apply invokePlayerPure <;> cases v <;> rfl
private theorem i2 (v : Value) :
    Application.invoke (profile v) environment (s2 v) (.player 1) = FinDist.pure (s3 v) := by
  apply invokePlayerPure <;> cases v <;> rfl
private theorem i3 (v : Value) :
    Application.invoke (profile v) environment (s3 v) (.player 1) = FinDist.pure (s4 v) := by
  apply invokePlayerPure <;> cases v <;> rfl
private theorem i4 (v : Value) :
    Application.invoke (profile v) environment (s4 v) .environment = FinDist.pure (s5 v) := by
  apply invokeEnvironmentPure <;> cases v <;> rfl
private theorem i5 (v : Value) :
    Application.invoke (profile v) environment (s5 v) .environment = FinDist.pure (s6 v) := by
  apply invokeEnvironmentPure <;> cases v <;> rfl
private theorem i6 (v : Value) :
    Application.invoke (profile v) environment (s6 v) (.player 0) = FinDist.pure (s7 v) := by
  apply invokePlayerPure <;> rcases v with _ | (_ | _) <;> rfl
private theorem i7 (v : Value) :
    Application.invoke (profile v) environment (s7 v) .environment = FinDist.pure (s8 v) := by
  apply invokeEnvironmentPure <;> cases v <;> rfl
private theorem i8 (v : Value) :
    Application.invoke (profile v) environment (s8 v) .environment = FinDist.pure (s9 v) := by
  apply invokeEnvironmentPure <;> cases v <;> rfl
private theorem i9 (v : Value) :
    Application.invoke (profile v) environment (s9 v) (.player 1) = FinDist.pure (s10 v) := by
  apply invokePlayerPure <;> rcases v with _ | (_ | _) <;> rfl
private theorem i10 (v : Value) :
    Application.invoke (profile v) environment (s10 v) .environment = FinDist.pure (s11 v) := by
  apply invokeEnvironmentPure <;> cases v <;> rfl

theorem law_eq_final (v : Value) : law v = FinDist.pure (s11 v) := by
  change Application.runPolicies (profile v) environment schedule s0 = _
  simp only [schedule, MessageApplication.runPolicies, i0, i1, i2, i3, i4, i5, i6,
    i7, i8, i9, i10, FinDist.pure_bind]

theorem false_events :
    (law (some false)).map (fun execution => execution.native.application.events) =
      FinDist.pure [.accepted 0 (0, 0), .accepted 1 (1, 1),
        .opened 2 (some false), .opened 3 (some false)] := by
  rw [law_eq_final, FinDist.map_pure]
  rfl

theorem true_events :
    (law (some true)).map (fun execution => execution.native.application.events) =
      FinDist.pure [.accepted 0 (0, 0), .accepted 1 (1, 1), .opened 2 (some true)] := by
  rw [law_eq_final, FinDist.map_pure]
  rfl

/-- Player one's earlier binding remains `some false` in both worlds, including
the branch where it later withholds its opening. -/
theorem bound_lookup (v : Value) :
    (law v).map (fun execution => execution.native.application.service.lookup (1, 1)) =
      FinDist.pure (some (some false)) := by
  rw [law_eq_final, FinDist.map_pure]
  rcases v with _ | (_ | _) <;> rfl

def hasPlayerOneOpening : List (Event Player Value) → Bool
  | [] => false
  | .opened 3 (some false) :: _ => true
  | _ :: rest => hasPlayerOneOpening rest

def hasPlayerZeroTrueOpening : List (Event Player Value) → Bool
  | [] => false
  | .opened 2 (some true) :: _ => true
  | _ :: rest => hasPlayerZeroTrueOpening rest

theorem false_opens :
    (law (some false)).map (fun execution =>
      hasPlayerOneOpening execution.native.application.events) = FinDist.pure true := by
  rw [law_eq_final, FinDist.map_pure]
  rfl

/-- Withholding leaves reveal node three incomplete even though both commitment
nodes and player zero's opening are present. -/
theorem true_withholds :
    (law (some true)).map (fun execution =>
      (done execution.native.application.events 0, done execution.native.application.events 1,
        hasPlayerZeroTrueOpening execution.native.application.events,
        hasPlayerOneOpening execution.native.application.events)) =
      FinDist.pure (true, true, true, false) := by
  rw [law_eq_final, FinDist.map_pure]
  rfl

theorem disclosure_differs :
    (law (some false)).map (fun execution =>
      hasPlayerOneOpening execution.native.application.events) ≠
    (law (some true)).map (fun execution =>
      hasPlayerOneOpening execution.native.application.events) := by
  rw [false_opens]
  have htrue : (law (some true)).map (fun execution =>
      hasPlayerOneOpening execution.native.application.events) = FinDist.pure false := by
    rw [law_eq_final, FinDist.map_pure]
    rfl
  rw [htrue]
  intro heq
  have hmem : true ∈ (FinDist.pure false : FinDist Bool).support := by
    rw [← heq]
    exact FinDist.mem_support_pure.mpr rfl
  exact Bool.noConfusion (FinDist.mem_support_pure.mp hmem)

end

end VegasTests.PendingWithholding
