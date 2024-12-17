import Mathlib

variable {m₁ m₂ n₁ n₂ : Type*}

section zero

variable {Z : Type*} [Zero Z]

def Matrix.IsBlockDiagonal (A : Matrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) Z) : Prop :=
  (∀ i₁ : m₁, ∀ j₂ : n₂, A (Sum.inl i₁) (Sum.inr j₂) = 0) ∧
  (∀ i₂ : m₂, ∀ j₁ : n₁, A (Sum.inr i₂) (Sum.inl j₁) = 0)

lemma Matrix.fromBlocks_isBlockDiagonal (A₁ : Matrix m₁ n₁ Z) (A₂ : Matrix m₂ n₂ Z) :
    (fromBlocks A₁ 0 0 A₂).IsBlockDiagonal := by
  simp [Matrix.IsBlockDiagonal]

end zero

section commring

variable {R : Type*} [CommRing R]

lemma Matrix.isTotallyUnimodular_of_isBlockDiagonal {A : Matrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) R}
    [Fintype m₁] [DecidableEq m₁] [Fintype m₂] [DecidableEq m₂]
    [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
    (hA₁ : (A.submatrix Sum.inl Sum.inl).IsTotallyUnimodular)
    (hA₂ : (A.submatrix Sum.inr Sum.inr).IsTotallyUnimodular)
    (hA : A.IsBlockDiagonal) :
    A.IsTotallyUnimodular := by
  intro k f g hf hg
  rw [Matrix.isTotallyUnimodular_iff] at hA₁ hA₂
  if hxy : Fintype.card { x₁ : Fin k × m₁ // f x₁.fst = Sum.inl x₁.snd }
         = Fintype.card { y₁ : Fin k × n₁ // g y₁.fst = Sum.inl y₁.snd }
         ∧ Fintype.card { x₂ : Fin k × m₂ // f x₂.fst = Sum.inr x₂.snd }
         = Fintype.card { y₂ : Fin k × n₂ // g y₂.fst = Sum.inr y₂.snd }
  then -- the square case
    sorry
  else -- non-square cases
    sorry

theorem Matrix.fromBlocks_isTotallyUnimodular {A₁ : Matrix m₁ n₁ R} {A₂ : Matrix m₂ n₂ R}
    [Fintype m₁] [DecidableEq m₁] [Fintype m₂] [DecidableEq m₂]
    [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
    (hA₁ : A₁.IsTotallyUnimodular) (hA₂ : A₂.IsTotallyUnimodular) :
    (fromBlocks A₁ 0 0 A₂).IsTotallyUnimodular := by
  apply Matrix.isTotallyUnimodular_of_isBlockDiagonal
  · convert hA₁
  · convert hA₂
  · apply Matrix.fromBlocks_isBlockDiagonal

end commring
