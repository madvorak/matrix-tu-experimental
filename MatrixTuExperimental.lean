import Mathlib


theorem Matrix.blockDiagonal'_isTotallyUnimodular (m n : Fin 2 → Type*)
    (R : Type) [CommRing R]
    [∀ k : Fin 2, DecidableEq (m k)] [∀ k : Fin 2, Fintype (m k)]
    [∀ k : Fin 2, DecidableEq (n k)] [∀ k : Fin 2, Fintype (n k)]
    (M : Π k : Fin 2, Matrix (m k) (n k) R)
    (hM : ∀ k : Fin 2, (M k).IsTotallyUnimodular) :
    (Matrix.blockDiagonal' M).IsTotallyUnimodular := by
  sorry

instance {ι : Fin 2 → Type*} [hι0 : DecidableEq (ι 0)] [hι1 : DecidableEq (ι 1)] :
    ∀ k : Fin 2, DecidableEq (ι k) := by
  intro k
  if hk : k = 0 then
    simpa [hk] using hι0
  else
    simpa [k.eq_one_of_neq_zero hk] using hι1
/-
instance {ι : Fin 2 → Type*} [hι0 : Fintype (ι 0)] [hι1 : Fintype (ι 1)] :
    ∀ k : Fin 2, Fintype (ι k) := by
  intro k
  if hk : k = 0 then
    simpa [hk] using hι0
  else
    simpa [k.eq_one_of_neq_zero hk] using hι1
-/

attribute [-simp] Fintype.card_ofIsEmpty Fintype.card_ofSubsingleton

theorem Matrix.fromBlocks_isTotallyUnimodular {m₁ m₂ n₁ n₂ R : Type} [CommRing R]
    [Fintype m₁] [DecidableEq m₁] [Fintype n₁] [DecidableEq n₁]
    [Fintype m₂] [DecidableEq m₂] [Fintype n₂] [DecidableEq n₂]
    {A₁ : Matrix m₁ n₁ R} (hA₁ : A₁.IsTotallyUnimodular)
    {A₂ : Matrix m₂ n₂ R} (hA₂ : A₂.IsTotallyUnimodular) :
    (fromBlocks A₁ 0 0 A₂).IsTotallyUnimodular := by
  convert
    Matrix.IsTotallyUnimodular.reindex ?_ ?_
      (Matrix.blockDiagonal'_isTotallyUnimodular ![m₁, m₂] ![n₁, n₂] R (
        fun k => match k with
          | 0 => A₁
          | 1 => A₂
      ) (
        fun k => match k with
          | 0 => hA₁
          | 1 => hA₂
      ) )
  swap
  · refine ⟨fun ⟨i, m⟩ => match i with | 0 => Sum.inl m | 1 => Sum.inr m,
        (Sum.casesOn · (⟨0, ·⟩) (⟨1, ·⟩)), ?_, ?_⟩
    · intro
      aesop
    · intro m
      cases m <;> aesop
  swap
  · refine ⟨fun ⟨i, n⟩ => match i with | 0 => Sum.inl n | 1 => Sum.inr n,
        (Sum.casesOn · (⟨0, ·⟩) (⟨1, ·⟩)), ?_, ?_⟩
    · intro
      aesop
    · intro n
      cases n <;> aesop
  swap -- TODO why cannot I use the same instance for `Fintype` as I did with `DecidableEq` ?
  · intro k
    if hk : k = 0 then
      simp [hk]
      assumption
    else
      have hk' := k.eq_one_of_neq_zero hk
      subst hk'
      assumption
  swap -- TODO why cannot I use the same instance for `Fintype` as I did with `DecidableEq` ?
  · intro k
    if hk : k = 0 then
      simp [hk]
      assumption
    else
      have hk' := k.eq_one_of_neq_zero hk
      subst hk'
      assumption
  ext i j
  cases i <;> cases j <;> simp [Matrix.blockDiagonal']
