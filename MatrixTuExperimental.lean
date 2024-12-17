import Mathlib

section zero

variable {Z : Type*} [Zero Z]

def Matrix.IsBlockDiagonal {m n : Type*} (A : Matrix m n Z) {α : Type*} (ι : m → α) (γ : n → α) : Prop :=
  ∀ i : m, ∀ j : n, ι i ≠ γ j → A i j = 0

lemma Matrix.fromBlocks_isBlockDiagonal {m₁ m₂ n₁ n₂ : Type*}
    (A₁ : Matrix m₁ n₁ Z) (A₂ : Matrix m₂ n₂ Z) :
    (fromBlocks A₁ 0 0 A₂).IsBlockDiagonal (α := Fin 2) (Sum.casesOn · 0 1) (Sum.casesOn · 0 1) := by
  simp [Matrix.IsBlockDiagonal]

end zero

section commring

variable {R : Type*} [CommRing R]

theorem Matrix.isTotallyUnimodular_of_isBlockDiagonal {m n : Type*}
    {A : Matrix m n R} {α : Type*} {ι : m → α} {γ : n → α}
    (hA : A.IsBlockDiagonal ι γ)
    (hAa : ∀ a : α, (A.submatrix
        (fun (I : { i : m // ι i = a }) => I.val)
        (fun (J : { j : n // γ j = a }) => J.val)
      ).IsTotallyUnimodular):
    A.IsTotallyUnimodular := by
  sorry

theorem Matrix.fromBlocks_isTotallyUnimodular {m₁ m₂ n₁ n₂ : Type*}
    [Fintype m₁] [DecidableEq m₁] [Fintype n₁] [DecidableEq n₁]
    [Fintype m₂] [DecidableEq m₂] [Fintype n₂] [DecidableEq n₂]
    {A₁ : Matrix m₁ n₁ R} (hA₁ : A₁.IsTotallyUnimodular)
    {A₂ : Matrix m₂ n₂ R} (hA₂ : A₂.IsTotallyUnimodular) :
    (fromBlocks A₁ 0 0 A₂).IsTotallyUnimodular := by
  apply Matrix.isTotallyUnimodular_of_isBlockDiagonal (Matrix.fromBlocks_isBlockDiagonal A₁ A₂)
  intro k
  fin_cases k
  · have hA :
      (fromBlocks A₁ 0 0 A₂).submatrix
        (fun (I : { i : m₁ ⊕ m₂ // i.casesOn 0 1 = (0 : Fin 2) }) => I.val)
        (fun (J : { j : n₁ ⊕ n₂ // j.casesOn 0 1 = (0 : Fin 2) }) => J.val)
      = A₁.reindex
          (Equiv.ofBijective (fun i₁ => ⟨Sum.inl i₁, rfl⟩)
            ⟨fun _ _ _ => by aesop, fun _ => by aesop⟩)
          (Equiv.ofBijective (fun j₁ => ⟨Sum.inl j₁, rfl⟩)
            ⟨fun _ _ _ => by aesop, fun _ => by aesop⟩)
    · ext i j
      cases hi : i.val
      · cases hj : j.val
        · aesop
        · simpa [hj] using j.property
      · simpa [hi] using i.property
    sorry
    -- TODO why cannot we `rw [hA]` here?
  · sorry

end commring

/-
#check Matrix.det_fromBlocks_zero₁₂
#check Matrix.det_of_lowerTriangular
-/
