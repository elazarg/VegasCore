import Mathlib.Data.List.Range
example (xs : List (Nat × Nat)) (h : xs.map Prod.fst = List.range xs.length) (i : Fin xs.length) : (xs.get i).1 = i.val := by
  have h1 : (xs.map Prod.fst).get ⟨i.1, by simpa using i.2⟩ = (xs.get i).1 := by simp
  have h2 := congrArg (fun l => l.get ⟨i.1, by simpa using i.2⟩) h
  have h3 : (List.range xs.length).get ⟨i.1, by simpa using i.2⟩ = i.1 := by simp
  exact h1.symm.trans (h2.trans h3)
