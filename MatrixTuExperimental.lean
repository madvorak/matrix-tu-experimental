import Mathlib


theorem Matrix.blockDiagonal'_isTotallyUnimodular (m n : Fin 2 → Type*)
    (R : Type) [CommRing R]
    [∀ k : Fin 2, DecidableEq (m k)] [∀ k : Fin 2, Fintype (m k)]
    [∀ k : Fin 2, DecidableEq (n k)] [∀ k : Fin 2, Fintype (n k)]
    (M : Π k : Fin 2, Matrix (m k) (n k) R)
    (hM : ∀ k : Fin 2, (M k).IsTotallyUnimodular) :
    (Matrix.blockDiagonal' M).IsTotallyUnimodular := by
  intro k f g hf hg
  if card : Fintype.card { i₁ : Fin k // (f i₁).fst = 0 }
          = Fintype.card { j₁ : Fin k // (g j₁).fst = 0 }
          ∧ Fintype.card { i₂ : Fin k // (f i₂).fst = 1 }
          = Fintype.card { j₂ : Fin k // (g j₂).fst = 1 }
  then
    obtain ⟨card₁, card₂⟩ := card
    let e₁ : { i₁ : Fin k // (f i₁).fst = 0 } ≃ { j₁ : Fin k // (g j₁).fst = 0 } :=
      Fintype.equivOfCardEq card₁
    let e₂ : { i₂ : Fin k // (f i₂).fst = 1 } ≃ { j₂ : Fin k // (g j₂).fst = 1 } :=
      Fintype.equivOfCardEq card₂
    have hMfg :
      ((Matrix.blockDiagonal' M).submatrix f g).det =
      ((Matrix.blockDiagonal' M).submatrix
        (f ∘ (fun i =>
          if hfi : (f i).fst = 0 then
            (e₁.toFun ⟨i, hfi⟩).val
          else
            (e₂.toFun ⟨i, (f i).fst.eq_one_of_neq_zero hfi⟩).val
        ))
        (g ∘ (fun j =>
          if hgj : (g j).fst = 0 then
            (e₁.invFun ⟨j, hgj⟩).val
          else
            (e₂.invFun ⟨j, (g j).fst.eq_one_of_neq_zero hgj⟩).val
        ))
      ).det
    · sorry
    rw [hMfg]
    sorry -- the square case
  else
    sorry -- non-square cases

instance {ι : Fin 2 → Type*} [hι0 : DecidableEq (ι 0)] [hι1 : DecidableEq (ι 1)] :
    ∀ k : Fin 2, DecidableEq (ι k) := by
  intro k
  if hk : k = 0 then
    simpa [hk] using hι0
  else
    simpa [k.eq_one_of_neq_zero hk] using hι1

theorem Matrix.fromBlocks_isTotallyUnimodular {m₁ m₂ n₁ n₂ R : Type} [CommRing R]
    [Fintype m₁] [DecidableEq m₁] [Fintype n₁] [DecidableEq n₁]
    [Fintype m₂] [DecidableEq m₂] [Fintype n₂] [DecidableEq n₂]
    {A₁ : Matrix m₁ n₁ R} (hA₁ : A₁.IsTotallyUnimodular)
    {A₂ : Matrix m₂ n₂ R} (hA₂ : A₂.IsTotallyUnimodular) :
    (Matrix.fromBlocks A₁ 0 0 A₂).IsTotallyUnimodular := by
  convert
    Matrix.IsTotallyUnimodular.reindex
      ⟨fun ⟨i, m⟩ => match i with | 0 => Sum.inl m | 1 => Sum.inr m,
        (Sum.casesOn · (⟨0, ·⟩) (⟨1, ·⟩)),
        fun _ => by aesop, fun m => by cases m <;> aesop⟩
      ⟨fun ⟨i, n⟩ => match i with | 0 => Sum.inl n | 1 => Sum.inr n,
        (Sum.casesOn · (⟨0, ·⟩) (⟨1, ·⟩)),
        fun _ => by aesop, fun n => by cases n <;> aesop⟩
      (Matrix.blockDiagonal'_isTotallyUnimodular ![m₁, m₂] ![n₁, n₂] R
        (match · with | 0 => A₁ | 1 => A₂)
        (match · with | 0 => hA₁| 1 => hA₂))
  swap
  · intro k
    if hk : k = 0 then
      simp [hk]
      assumption
    else
      have hk' := k.eq_one_of_neq_zero hk
      subst hk'
      assumption
  swap
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
