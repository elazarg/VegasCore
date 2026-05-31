import GameTheory.Concepts.Babbling

/-!
# Cheap talk

Property boundary: this file proves game-theory facts about explicit
cheap-talk strategy spaces, not runtime compilation or cryptographic security.

This module separates three claims:

* observable cheap talk has a larger contingent strategy space than inert
  message coordinates;
* only the babbling theorem is automatic for the examples in this file;
* protocol-message compilation is checked separately in
  `Vegas.Examples.ProtocolMessageBridge`.
-/

namespace Vegas

open GameTheory
open Math.Probability

namespace Examples
namespace Refinement

/-! ## Observable cheap talk at the game-theory layer -/

inductive TalkPlayer where
  | row
  | col
deriving DecidableEq

open TalkPlayer

/-- A two-player coordination game. Both players receive payoff `1` exactly
when their Boolean actions agree. -/
noncomputable def coordinationGame : KernelGame TalkPlayer where
  Strategy := fun _ => Bool
  Outcome := Bool × Bool
  outcomeKernel := fun profile => PMF.pure (profile row, profile col)
  utility := fun outcome _ => if outcome.1 == outcome.2 then 1 else 0

def coordinationTrueProfile : TalkPlayer → Bool :=
  fun _ => true

theorem coordinationGame_eu
    (profile : TalkPlayer → Bool) (player : TalkPlayer) :
    coordinationGame.eu profile player =
      if profile row == profile col then 1 else 0 := by
  cases player <;>
    simp [coordinationGame, KernelGame.eu, expect_pure]

theorem coordinationTrueProfile_nash :
    coordinationGame.IsNash coordinationTrueProfile := by
  intro player alternative
  cases player <;> cases alternative <;>
    simp [coordinationGame_eu, coordinationTrueProfile, Function.update]

/-- A real observable cheap-talk extension: each player sends a public Bool
message and then chooses a base action as a function of the realized message
profile. -/
noncomputable def coordinationCheapTalk :
    coordinationGame.CheapTalkExtension where
  Msg := fun _ => Bool
  default := fun _ => false

noncomputable abbrev coordinationCheapTalkGame : KernelGame TalkPlayer :=
  coordinationCheapTalk.game

/-- Babbling over the default messages preserves the base Nash equilibrium. -/
theorem coordinationCheapTalk_babbling_true_nash :
    coordinationCheapTalkGame.IsNash
      (coordinationCheapTalk.embedProfile coordinationTrueProfile) := by
  exact coordinationCheapTalk.babbling_nash coordinationTrueProfile_nash

/-- A cheap-talk strategy can condition its real action on the message profile.
This is not an inert `Message × Action` coordinate. -/
def followRowMessageStrategy
    (message : Bool) (player : TalkPlayer) :
    coordinationCheapTalkGame.Strategy player :=
  (message, fun messages => messages row)

def rowSignalsTrueProfile : coordinationCheapTalkGame.Profile
  | row => followRowMessageStrategy true row
  | col => followRowMessageStrategy false col

example :
    coordinationCheapTalk.messageProfile rowSignalsTrueProfile row = true := by
  rfl

example :
    coordinationCheapTalk.messageProfile rowSignalsTrueProfile col = false := by
  rfl

example :
    coordinationCheapTalk.actionProfile rowSignalsTrueProfile row = true := by
  rfl

example :
    coordinationCheapTalk.actionProfile rowSignalsTrueProfile col = true := by
  rfl

example :
    coordinationCheapTalkGame.outcomeKernel rowSignalsTrueProfile =
      PMF.pure (true, true) := by
  rfl

noncomputable def coordinationCheapTalkAction
    (profile : coordinationCheapTalkGame.Profile) :
    TalkPlayer → Bool
  | row => coordinationCheapTalk.actionProfile profile row
  | col => coordinationCheapTalk.actionProfile profile col

theorem coordinationCheapTalk_eu
    (profile : coordinationCheapTalkGame.Profile)
    (player : TalkPlayer) :
    coordinationCheapTalkGame.eu profile player =
      if coordinationCheapTalkAction profile row =
          coordinationCheapTalkAction profile col then 1 else 0 := by
  cases player <;>
    simp [coordinationCheapTalk,
      KernelGame.CheapTalkExtension.game, GameForm.CheapTalkExtension.form,
      KernelGame.eu, expect_pure, coordinationGame,
      coordinationCheapTalkAction]

/-- A non-babbling cheap-talk equilibrium: row's message is used as the
coordination recommendation. This is a game-specific proof, not an automatic
refinement theorem. -/
theorem coordinationCheapTalk_rowSignal_true_nash :
    coordinationCheapTalkGame.IsNash rowSignalsTrueProfile := by
  intro player alternative
  cases player
  · rw [coordinationCheapTalk_eu, coordinationCheapTalk_eu]
    have hbase :
        coordinationCheapTalkAction rowSignalsTrueProfile row =
          coordinationCheapTalkAction rowSignalsTrueProfile col := by
      rfl
    rw [if_pos hbase]
    by_cases hdev :
        coordinationCheapTalkAction
            (Function.update rowSignalsTrueProfile row alternative) row =
          coordinationCheapTalkAction
            (Function.update rowSignalsTrueProfile row alternative) col
    · rw [if_pos hdev]
    · rw [if_neg hdev]
      norm_num
  · rw [coordinationCheapTalk_eu, coordinationCheapTalk_eu]
    have hbase :
        coordinationCheapTalkAction rowSignalsTrueProfile row =
          coordinationCheapTalkAction rowSignalsTrueProfile col := by
      rfl
    rw [if_pos hbase]
    by_cases hdev :
        coordinationCheapTalkAction
            (Function.update rowSignalsTrueProfile col alternative) row =
          coordinationCheapTalkAction
            (Function.update rowSignalsTrueProfile col alternative) col
    · rw [if_pos hdev]
    · rw [if_neg hdev]
      norm_num

example :
    (followRowMessageStrategy false col).2 (fun _ => false) = false := by
  rfl

example :
    (followRowMessageStrategy false col).2
        (Function.update (fun _ => false) row true) = true := by
  rfl

end Refinement
end Examples
end Vegas
