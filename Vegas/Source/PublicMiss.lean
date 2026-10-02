/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Semantics

/-! # Source successors for silent public binding misses

A silent binding miss stores a failed binding and publishes its owner and
source name. Ordinary source successors preserve that public record. Players
observe it alongside their existing private source view, so a miss differs
from an ordinary failed binding before publication.

This module supplies configuration successors. A complete execution protocol,
sequential-equilibrium extension, private attempted-choice memory, and failed
opening evidence lotteries require separate proofs.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Public evidence that the named binding completed without a submission. -/
structure PublicBindingMiss (Player : Type) where
  owner : Player
  name : VarId
  deriving DecidableEq

/-- The ordinary typed source state and the publicly announced binding misses. -/
structure PublicMissConfig (Player : Type) (L : IExpr) (Γ : SourceCtx Player L) where
  source : Config Player L Γ
  misses : List (PublicBindingMiss Player)

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
def silentBindingMiss {owner : Player} (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : PublicMissConfig Player L Γ) :
    PublicMissConfig Player L ((name, .commitment owner payload) :: Γ) :=
  ⟨SourceProgram.commitSuccessor name guard config.source .failure,
    config.misses ++ [⟨owner, name⟩]⟩

/-- The typed state and retained guard obligations match a failed binding. -/
theorem silentBindingMiss_source {owner : Player} (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : PublicMissConfig Player L Γ) :
    (silentBindingMiss name guard config).source =
      SourceProgram.commitSuccessor name guard config.source .failure := rfl

/-- The newly bound cell has no value to disclose. -/
theorem silentBindingMiss_failed {owner : Player} (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : PublicMissConfig Player L Γ) :
    (silentBindingMiss name guard config).source.state.get HasVar.here =
      PublicationResult.failure := rfl

/-- The announcement is the same for every observer and carries no private
payload or attempted choice. -/
theorem silentBindingMiss_public {owner : Player} (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : PublicMissConfig Player L Γ)
    (who : Player) :
    (view who (silentBindingMiss name guard config)).2 =
      config.misses ++ [⟨owner, name⟩] := rfl

/-- The public announcement distinguishes silence from an ordinary private
forfeiture, even though both store the same failed binding. -/
theorem silentBindingMiss_view_ne_forfeiture {owner : Player} (name : VarId)
    (guard : SourceGuard L Γ owner name payload) (config : PublicMissConfig Player L Γ)
    (who : Player) :
    view who (silentBindingMiss name guard config) ≠
      view who (commitSuccessor name guard config .failure) := by
  intro equal
  have lengths := congrArg (fun observed => observed.2.length) equal
  simp only [view, silentBindingMiss, commitSuccessor, List.length_append,
    List.length_singleton] at lengths
  omega

end PublicMissConfig

end Vegas.SourceProgram
