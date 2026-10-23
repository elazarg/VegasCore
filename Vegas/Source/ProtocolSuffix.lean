/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryBlockEmbedding

/-! # Exact syntactic source suffixes and preserved entry cells -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A residual lift follows exactly the consumed source constructors. -/
inductive ProtocolSuffix {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}
    (whole : SourceProgram Player L wholeΓ wholeO) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
      (program : SourceProgram Player L Γ O) →
      (ProtocolState program → ProtocolState whole) → Prop where
  | initial : ProtocolSuffix whole whole id
  | sampleTail {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}
      (fresh : name ∉ Γ.map Prod.fst) (law : L.DistExpr (SourcePublicCtx L Γ) payload)
      (next : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
      {lift : ProtocolState (.sample name fresh law next) → ProtocolState whole}
      (origin : ProtocolSuffix whole (.sample name fresh law next) lift) :
      ProtocolSuffix whole next (fun point => lift (Sum.inr point))
  | commitTail {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {owner : Player}
      {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
      (guard : SourceGuard L Γ owner name payload)
      (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
      {lift : ProtocolState (.commit name owner fresh guard next) → ProtocolState whole}
      (origin : ProtocolSuffix whole (.commit name owner fresh guard next) lift) :
      ProtocolSuffix whole next (fun point => lift (Sum.inr point))
  | revealTail {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
      {owner : Player} {payload : L.Ty} (fresh : published ∉ Γ.map Prod.fst)
      (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
      (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
      {lift : ProtocolState (.reveal published owner name fresh selected unresolved next) →
        ProtocolState whole}
      (origin : ProtocolSuffix whole (.reveal published owner name fresh selected unresolved next)
        lift) : ProtocolSuffix whole next (fun point => lift (Sum.inr point))

namespace ProtocolSuffix

variable {wholeΓ Γ Δ : SourceCtx Player L} {wholeO O P : Finset VarId}
  {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
  {tail : SourceProgram Player L Δ P}
  {lift : ProtocolState program → ProtocolState whole}

/-- Equality of whole observations reflects to the same actual typed suffix. -/
theorem observe_reflect (origin : ProtocolSuffix whole program lift) (who : Player) :
    ∀ first second, ProtocolState.observe who whole (lift first) =
        ProtocolState.observe who whole (lift second) →
      ProtocolState.observe who program first = ProtocolState.observe who program second := by
  induction origin with
  | initial => intro first second same; exact same
  | sampleTail fresh law next previous ih =>
      intro first second same
      exact Sum.inr.inj (ih (.inr first) (.inr second) same)
  | commitTail fresh guard next previous ih =>
      intro first second same
      exact Sum.inr.inj (ih (.inr first) (.inr second) same)
  | revealTail fresh selected unresolved next previous ih =>
      intro first second same
      exact Sum.inr.inj (ih (.inr first) (.inr second) same)

/-- A genuine source suffix preserves whether its current instruction commits. -/
theorem atCommit_lift (origin : ProtocolSuffix whole program lift) :
    ∀ point, ProtocolState.atCommit whole (lift point) = ProtocolState.atCommit program point := by
  induction origin with
  | initial => intro point; rfl
  | sampleTail fresh law next previous ih => exact fun point => ih (.inr point)
  | commitTail fresh guard next previous ih => exact fun point => ih (.inr point)
  | revealTail fresh selected unresolved next previous ih => exact fun point => ih (.inr point)

/-- A genuine source suffix preserves the endpoint of its current commitment window. -/
theorem commitEnd_lift (origin : ProtocolSuffix whole program lift) :
    ∀ point, ProtocolState.commitEnd whole (lift point) =
      ProtocolState.commitEnd program point := by
  induction origin with
  | initial => intro point; rfl
  | sampleTail fresh law next previous ih => exact fun point => ih (.inr point)
  | commitTail fresh guard next previous ih => exact fun point => ih (.inr point)
  | revealTail fresh selected unresolved next previous ih => exact fun point => ih (.inr point)

/-- Two genuine source suffix traversals compose without changing the executor. -/
theorem compose {later : ProtocolState tail → ProtocolState program}
    (outer : ProtocolSuffix whole program lift) (inner : ProtocolSuffix program tail later) :
    ProtocolSuffix whole tail (fun point => lift (later point)) := by
  induction inner with
  | initial => exact outer
  | sampleTail fresh law next _origin ih => exact .sampleTail fresh law next ih
  | commitTail fresh guard next _origin ih => exact .commitTail fresh guard next ih
  | revealTail fresh selected unresolved next _origin ih =>
      exact .revealTail fresh selected unresolved next ih

/-- Intendedness of the whole source point includes intendedness of its tail. -/
theorem intended_reflect (origin : ProtocolSuffix whole program lift) :
    ∀ point, ProtocolState.Intended whole (lift point) → ProtocolState.Intended program point := by
  induction origin with
  | initial => intro point intended; exact intended
  | sampleTail fresh law next _origin ih => intro point intended; exact ih (.inr point) intended
  | commitTail fresh guard next _origin ih => intro point intended; exact ih (.inr point) intended
  | revealTail fresh selected unresolved next _origin ih =>
      intro point intended
      exact (ih (.inr point) intended).2

/-- A residual change preserving every old entry cell preserves all earlier
successful publications. Intendedness of its target then lifts to the whole
source program; the reference supplies the already consumed prefix facts. -/
theorem intended_of_base_eq (origin : ProtocolSuffix whole program lift) :
    ∀ reference target,
      ProtocolState.Intended whole (lift reference) → ProtocolState.Intended program target →
      ProtocolState.base program target = ProtocolState.base program reference →
        ProtocolState.Intended whole (lift target) := by
  induction origin with
  | initial => intro reference target _before intended _base; exact intended
  | sampleTail fresh law next _origin ih =>
      intro reference target before intended sameBase
      apply ih (.inr reference) (.inr target) before intended
      change (fun _ _ cell => (ProtocolState.base next target).get (.there cell)) =
        (fun _ _ cell => (ProtocolState.base next reference).get (.there cell))
      rw [sameBase]
  | commitTail fresh guard next _origin ih =>
      intro reference target before intended sameBase
      apply ih (.inr reference) (.inr target) before intended
      change (fun _ _ cell => (ProtocolState.base next target).get (.there cell)) =
        (fun _ _ cell => (ProtocolState.base next reference).get (.there cell))
      rw [sameBase]
  | revealTail fresh selected unresolved next origin ih =>
      intro reference target before intended sameBase
      have previous := origin.intended_reflect (.inr reference) before
      have publication : ∃ value,
          (ProtocolState.base next target).get .here = .success value := by
        rw [sameBase]
        exact previous.1
      apply ih (.inr reference) (.inr target) before ⟨publication, intended⟩
      change (fun _ _ cell => (ProtocolState.base next target).get (.there cell)) =
        (fun _ _ cell => (ProtocolState.base next reference).get (.there cell))
      rw [sameBase]

open Classical in
/-- A literal suffix lift retains the typed source cell readout. -/
theorem cell?_lift
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (point : ProtocolState program)
    (name : VarId) (kind : CellTy Player L) :
    ProtocolState.cell? whole (lift point) name kind =
      ProtocolState.cell? program point name kind := by
  induction origin with
  | initial => rfl
  | sampleTail _ _ _ _ ih => exact ih (.inr point)
  | commitTail _ _ _ _ ih => exact ih (.inr point)
  | revealTail _ _ _ _ _ ih => exact ih (.inr point)

end ProtocolSuffix

namespace CommitPrefix

variable {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- The existing typed commitment lift follows only actual source sum constructors. -/
theorem protocolSuffix (block : CommitPrefix Γ O Δ P) (suffix : SourceProgram Player L Δ P) :
    ProtocolSuffix (block.prepend suffix) suffix (block.liftPoint suffix) := by
  induction block with
  | nil => exact .initial
  | commit name owner fresh guard rest ih =>
      exact (ProtocolSuffix.commitTail fresh guard (rest.prepend suffix)
        ProtocolSuffix.initial).compose (ih suffix)

end CommitPrefix
end Vegas.SourceProgram
