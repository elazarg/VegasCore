/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Semantics

/-! # Source successors for public missed decisions

A missed commitment stores a failed binding; a missed disclosure stores a
failed publication. Both publish the owner and the decision's source name.
Ordinary source successors preserve that public record. Players observe it
alongside their private source view, distinguishing a missed decision from
an ordinary failed binding or deliberate false disclosure.

This module supplies configuration successors. A complete execution protocol,
sequential-equilibrium extension, private attempted-choice memory, and failed
opening evidence lotteries require separate proofs.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Public evidence that the named owned decision completed without a response. -/
structure PublicDecisionMiss (Player : Type) where
  owner : Player
  name : VarId
  deriving DecidableEq

/-- The ordinary typed source state and publicly announced missed decisions. -/
structure PublicMissConfig (Player : Type) (L : IExpr) (Γ : SourceCtx Player L) where
  source : Config Player L Γ
  misses : List (PublicDecisionMiss Player)

namespace PublicMissConfig

variable {Γ : SourceCtx Player L} {name : VarId} {payload : L.Ty}

/-- Every player sees the public miss log, in addition to the original view. -/
def view (who : Player) (config : PublicMissConfig Player L Γ) :=
  (config.source.view who, config.misses)

def sampleSuccessor (name : VarId) (config : PublicMissConfig Player L Γ)
    (value : L.Val payload) : PublicMissConfig Player L ((name, .publicData payload) :: Γ) :=
  ⟨SourceProgram.sampleSuccessor name config.source value, config.misses⟩

def commitSuccessor {owner : Player} (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : PublicMissConfig Player L Γ)
    (choice : PublicationResult (L.Val payload)) :
    PublicMissConfig Player L ((name, .commitment owner payload) :: Γ) :=
  ⟨SourceProgram.commitSuccessor name guard config.source choice, config.misses⟩

def revealSuccessor {owner : Player} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload))
    (config : PublicMissConfig Player L Γ) (disclose : Bool) :
    PublicMissConfig Player L ((published, .publication payload) :: Γ) :=
  ⟨SourceProgram.revealSuccessor published source config.source disclose, config.misses⟩

/-- A silent expiry fails this binding and announces the miss. It leaves every
later source decision available; it does not change the remaining program. -/
def commitMiss {owner : Player} (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : PublicMissConfig Player L Γ) :
    PublicMissConfig Player L ((name, .commitment owner payload) :: Γ) :=
  ⟨SourceProgram.commitSuccessor name guard config.source .failure,
    config.misses ++ [⟨owner, name⟩]⟩

/-- The typed state and retained guard obligations match a failed binding. -/
theorem commitMiss_source {owner : Player} (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : PublicMissConfig Player L Γ) :
    (commitMiss name guard config).source =
      SourceProgram.commitSuccessor name guard config.source .failure := rfl

/-- The newly bound cell has no value to disclose. -/
theorem commitMiss_failed {owner : Player} (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : PublicMissConfig Player L Γ) :
    (commitMiss name guard config).source.state.get HasVar.here =
      PublicationResult.failure := rfl

/-- The announcement is the same for every observer and carries no private
payload or attempted choice. -/
theorem commitMiss_public {owner : Player} (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : PublicMissConfig Player L Γ)
    (who : Player) :
    (view who (commitMiss name guard config)).2 =
      config.misses ++ [⟨owner, name⟩] := rfl

/-- The public announcement distinguishes silence from an ordinary private
forfeiture, even though both store the same failed binding. -/
theorem commitMiss_view_ne_forfeiture {owner : Player} (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : PublicMissConfig Player L Γ)
    (who : Player) :
    view who (commitMiss name guard config) ≠
      view who (commitSuccessor name guard config .failure) := by
  intro equal
  have lengths := congrArg (fun observed => observed.2.length) equal
  simp only [view, commitMiss, commitSuccessor, List.length_append,
    List.length_singleton] at lengths
  omega

/-- A missed disclosure publishes failure and the public miss announcement.
Its source name identifies the publication instruction, not the binding. -/
def revealMiss {owner : Player} (published : VarId)
    (binding : HasVar Γ name (.commitment owner payload))
    (config : PublicMissConfig Player L Γ) :
    PublicMissConfig Player L ((published, .publication payload) :: Γ) :=
  ⟨SourceProgram.revealSuccessor published binding config.source false,
    config.misses ++ [⟨owner, published⟩]⟩

/-- The typed state and guard bookkeeping match ordinary false disclosure. -/
theorem revealMiss_source {owner : Player} (published : VarId)
    (binding : HasVar Γ name (.commitment owner payload))
    (config : PublicMissConfig Player L Γ) :
    (revealMiss published binding config).source =
      SourceProgram.revealSuccessor published binding config.source false := rfl

/-- A missed disclosure produces no publication value. -/
theorem revealMiss_failed {owner : Player} (published : VarId)
    (binding : HasVar Γ name (.commitment owner payload))
    (config : PublicMissConfig Player L Γ) :
    (revealMiss published binding config).source.state.get HasVar.here =
      PublicationResult.failure := by
  simp [revealMiss, SourceProgram.revealSuccessor, Env.get, Env.cons]

/-- Every observer receives the same missed-disclosure announcement. -/
theorem revealMiss_public {owner : Player} (published : VarId)
    (binding : HasVar Γ name (.commitment owner payload))
    (config : PublicMissConfig Player L Γ) (who : Player) :
    (view who (revealMiss published binding config)).2 =
      config.misses ++ [⟨owner, published⟩] := rfl

/-- A miss remains observably different from a deliberate false disclosure,
despite producing the same typed publication result. -/
theorem revealMiss_view_ne_withholding {owner : Player} (published : VarId)
    (binding : HasVar Γ name (.commitment owner payload))
    (config : PublicMissConfig Player L Γ) (who : Player) :
    view who (revealMiss published binding config) ≠
      view who (revealSuccessor published binding config false) := by
  intro equal
  have lengths := congrArg (fun observed => observed.2.length) equal
  simp only [view, revealMiss, revealSuccessor, List.length_append,
    List.length_singleton] at lengths
  omega

end PublicMissConfig

end Vegas.SourceProgram
