import Mathlib


lemma finset_of_cardinality_between {α β : Type*} [Fintype α] [Fintype β] {n : ℕ}
    (hα : Fintype.card α < n) (hn : n ≤ Fintype.card α + Fintype.card β) :
    ∃ b : Finset β, Fintype.card (α ⊕ b) = n ∧ Nonempty b := by
  have beta' : n - Fintype.card α ≤ Fintype.card β
  · omega
  obtain ⟨s, hs⟩ : ∃ s : Finset β, s.card = n - Fintype.card α :=
    (Finset.exists_subset_card_eq beta').imp (by simp)
  use s
  rw [Fintype.card_sum, Fintype.card_coe, hs]
  constructor
  · omega
  · by_contra ifempty
    have : s.card = 0
    · rw [Finset.card_eq_zero]
      rw [nonempty_subtype, not_exists] at ifempty
      exact Finset.eq_empty_of_forall_not_mem ifempty
    omega

section decomposition
/-!
# Function to Sum decomposition

Here we decompose a function `f : α → β₁ ⊕ β₂` into a function and two bijections:
`α → α₁ ⊕ α₂ ≃ β₁ ⊕ β₂`
-/

variable {α β₁ β₂ : Type*}

@[simp]
def Function.decomposeSum (f : α → β₁ ⊕ β₂) : α ≃ f ⁻¹' (Set.range Sum.inl) ⊕ f ⁻¹' (Set.range Sum.inr) where
  toFun a :=
    (match hfa : f a with
      | .inl b₁ => Sum.inl ⟨a, by simp [hfa]⟩
      | .inr b₂ => Sum.inr ⟨a, by simp [hfa]⟩
    )
  invFun x :=
    x.casesOn Subtype.val Subtype.val
  left_inv a := by
    aesop
  right_inv x := by
    aesop

lemma Function.eq_comp_decomposeSum (f : α → β₁ ⊕ β₂) :
    f = Sum.elim (fun ⟨_, ha⟩ => Sum.inl ha.choose) (fun ⟨_, ha⟩ => Sum.inr ha.choose) ∘ f.decomposeSum := by
  aesop

end decomposition

/-- `Fintype.ofFinite` from Mathlib copied here but as an instance. -/
noncomputable instance Fintype.ofFinite_copy (α : Type*) [Finite α] : Fintype α :=
  (nonempty_fintype α).some


variable {R : Type*}

section signType_cast

lemma zero_in_set_range_singType_cast [LinearOrderedRing R] : (0 : R) ∈ Set.range SignType.cast :=
  ⟨0, rfl⟩

lemma in_set_range_singType_cast_mul_in_set_range_singType_cast [LinearOrderedRing R] {a b : R}
    (ha : a ∈ Set.range SignType.cast) (hb : b ∈ Set.range SignType.cast) :
    a * b ∈ Set.range SignType.cast := by
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  exact ⟨_, SignType.coe_mul a' b'⟩

lemma in_set_range_singType_cast_iff_abs [LinearOrderedCommRing R] (a : R) :
    a ∈ Set.range SignType.cast ↔ |a| ∈ Set.range SignType.cast := by
  constructor
  · rintro ⟨s, rfl⟩
    cases s with
    | zero => use 0; simp
    | pos => use 1; simp
    | neg => use 1; simp
  · intro ⟨s, hs⟩
    symm at hs
    cases s with
    | zero =>
      rw [SignType.zero_eq_zero, SignType.coe_zero, abs_eq_zero] at hs
      exact ⟨0, hs.symm⟩
    | pos =>
      rw [SignType.pos_eq_one, abs_eq_max_neg, max_eq_iff] at hs
      cases hs with
      | inl poz =>
        exact ⟨1, poz.left.symm⟩
      | inr neg =>
        use -1
        rw [neg_eq_iff_eq_neg] at neg
        exact neg.left.symm
    | neg =>
      exfalso
      rw [SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one] at hs
      have h0 := (abs_nonneg a).trans_eq hs
      norm_num at h0

end signType_cast


variable {X₁ X₂ Y₁ Y₂ Z : Type*}

set_option maxHeartbeats 800000 in
/-- `Matrix.fromBlocks_isTotallyUnimodular` preprocessing. -/
private lemma Matrix.fromBlocks_submatrix [Zero R] (A₁ : Matrix X₁ Y₁ R) (A₂ : Matrix X₂ Y₂ R)
    (f : Z → X₁ ⊕ X₂) (g : Z → Y₁ ⊕ Y₂) :
    (fromBlocks A₁ 0 0 A₂).submatrix f g =
    (fromBlocks
      (A₁.submatrix
        (fun ⟨_, ha⟩ => ha.choose)
        (fun ⟨_, ha⟩ => ha.choose)
      ) 0 0
      (A₂.submatrix
        (fun ⟨_, ha⟩ => ha.choose)
        (fun ⟨_, ha⟩ => ha.choose)
      )
    ).submatrix f.decomposeSum g.decomposeSum := by
  rw [
    f.eq_comp_decomposeSum,
    g.eq_comp_decomposeSum,
    ←Matrix.submatrix_submatrix]
  ext i j
  cases hfi : f i <;> cases hgj : g j <;> simp [hfi, hgj, Matrix.fromBlocks] <;> aesop -- TODO speed up

lemma decomposeSum_card_eq (f : Z → X₁ ⊕ X₂) [Fintype Z] :
    Fintype.card (f ⁻¹' (Set.range Sum.inl)) + Fintype.card (f ⁻¹' (Set.range Sum.inr)) =
    Fintype.card Z := by
  rw [←Fintype.card_sum]
  exact Fintype.card_congr f.decomposeSum.symm


variable [LinearOrderedCommRing R] [DecidableEq Z] [Fintype Z]

/-- `Matrix.fromBlocks_isTotallyUnimodular` square case. -/
private lemma Matrix.fromBlocks_submatrix_det_in_set_range_singType_cast_of_isTotallyUnimodular_of_card_eq
    {A₁ : Matrix X₁ Y₁ R} (hA₁ : A₁.IsTotallyUnimodular)
    {A₂ : Matrix X₂ Y₂ R} (hA₂ : A₂.IsTotallyUnimodular)
    {f : Z → X₁ ⊕ X₂} {g : Z → Y₁ ⊕ Y₂}
    (hfg :
      Fintype.card (f ⁻¹' (Set.range Sum.inl)) =
      Fintype.card (g ⁻¹' (Set.range Sum.inl)) ∧
      Fintype.card (f ⁻¹' (Set.range Sum.inr)) =
      Fintype.card (g ⁻¹' (Set.range Sum.inr))) :
    ((fromBlocks A₁ 0 0 A₂).submatrix f g).det ∈
      Set.range SignType.cast := by
  rw [Matrix.isTotallyUnimodular_iff_fintype] at hA₁ hA₂
  rw [Matrix.fromBlocks_submatrix]
  let e₁ : (f ⁻¹' (Set.range Sum.inl)) ≃ (g ⁻¹' (Set.range Sum.inl)) :=
    Fintype.equivOfCardEq hfg.1
  let e₂ : (f ⁻¹' (Set.range Sum.inr)) ≃ (g ⁻¹' (Set.range Sum.inr)) :=
    Fintype.equivOfCardEq hfg.2
  have hAfg :
    (fromBlocks
      (A₁.submatrix
        (fun ⟨_, ha⟩ => ha.choose)
        (fun ⟨_, ha⟩ => ha.choose)
      ) 0 0
      (A₂.submatrix
        (fun ⟨_, ha⟩ => ha.choose)
        (fun ⟨_, ha⟩ => ha.choose)
      )
    ).submatrix f.decomposeSum g.decomposeSum
    = -- make outer submatrix bijective
    (fromBlocks
      (A₁.submatrix (fun ⟨_, ha⟩ => ha.choose) ((fun ⟨_, ha⟩ => ha.choose) ∘ e₁)) 0 0
      (A₂.submatrix (fun ⟨_, ha⟩ => ha.choose) ((fun ⟨_, ha⟩ => ha.choose) ∘ e₂))
    ).submatrix f.decomposeSum (g.decomposeSum.trans (Equiv.sumCongr e₁.symm e₂.symm))
  · ext
    simp only [Function.decomposeSum, Equiv.coe_fn_mk, Equiv.coe_trans, Equiv.sumCongr_apply, Function.comp_apply,
      Matrix.submatrix, Matrix.of_apply]
    split <;> split <;> simp
  rw [hAfg,
  -- absolute value of determinant was preserved by previous mappings,
    in_set_range_singType_cast_iff_abs, Matrix.abs_det_submatrix_equiv_equiv,
  -- we now express it as a product of determinants of submatrices in blocks
    Matrix.det_fromBlocks_zero₁₂, ←in_set_range_singType_cast_iff_abs]
  -- determinants of submatrices in blocks are in `Set.range SignType.cast` by TUness of `A₁` and `A₂`
  apply in_set_range_singType_cast_mul_in_set_range_singType_cast
  · apply hA₁
  · apply hA₂

/-- `Matrix.fromBlocks_isTotallyUnimodular` non-square case. -/
private lemma Matrix.fromBlocks_submatrix_det_in_set_range_singType_cast_of_card_lt
    (A₁ : Matrix X₁ Y₁ R) (A₂ : Matrix X₂ Y₂ R) {f : Z → X₁ ⊕ X₂} {g : Z → Y₁ ⊕ Y₂}
    (hfg :
      Fintype.card (f ⁻¹' (Set.range Sum.inl)) <
      Fintype.card (g ⁻¹' (Set.range Sum.inl))) :
    ((fromBlocks A₁ 0 0 A₂).submatrix f g).det ∈
      Set.range SignType.cast := by
  -- we will show that the submatrix is singular
  convert zero_in_set_range_singType_cast
  rw [Matrix.fromBlocks_submatrix]
  -- we need a new indexing type [`▫X₁ ⊕ ` a part of `▫X₂`] of the same cardinality as `▫Y₁` for the "top half"
  -- then the bottom left blocks will be all `0`s, hence we can multiply the two determinants, and the top left block will
  -- have at least one row made of `0`s, hence its determinant is `0`
  have hZY₁ :
      Fintype.card (g ⁻¹' (Set.range Sum.inl)) ≤
      Fintype.card (f ⁻¹' (Set.range Sum.inl)) +
      Fintype.card (f ⁻¹' (Set.range Sum.inr))
  · rw [decomposeSum_card_eq]
    exact Fintype.card_le_of_embedding ⟨_, Subtype.val_injective⟩
  obtain ⟨X', hY₁, hX'⟩ := finset_of_cardinality_between hfg hZY₁
  have hY₂ : Fintype.card { y // y ∉ X' } = Fintype.card (g ⁻¹' (Set.range Sum.inr))
  · suffices :
        Fintype.card { y // y ∉ X' } + Fintype.card ((f ⁻¹' (Set.range Sum.inl)) ⊕ X') =
        Fintype.card (g ⁻¹' (Set.range Sum.inl)) +
        Fintype.card (g ⁻¹' (Set.range Sum.inr))
    · omega
    rw [Fintype.card_sum, add_comm, add_assoc, ←Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl (· ∈ X')),
      decomposeSum_card_eq, decomposeSum_card_eq]
  let e₁ := Fintype.equivOfCardEq hY₁
  let e₂ := Fintype.equivOfCardEq hY₂
  let e₃ := (Equiv.sumAssoc (f ⁻¹' (Set.range Sum.inl)) X' { x // x ∉ X' }).symm
  let e' := (Equiv.sumCompl (· ∈ X')).symm
  have hAfg :
    (fromBlocks
      (A₁.submatrix
        ((fun ⟨_, ha⟩ => ha.choose) : (f ⁻¹' (Set.range Sum.inl)) → X₁)
        ((fun ⟨_, ha⟩ => ha.choose) : (g ⁻¹' (Set.range Sum.inl)) → Y₁)
      ) 0 0
      (A₂.submatrix
        ((fun ⟨_, ha⟩ => ha.choose) : (f ⁻¹' (Set.range Sum.inr)) → X₂)
        ((fun ⟨_, ha⟩ => ha.choose) : (g ⁻¹' (Set.range Sum.inr)) → Y₂)
      )
    ).submatrix f.decomposeSum g.decomposeSum
    = -- make outer submatrix bijective
    (fromBlocks
      (fromRows (A₁.submatrix (fun ⟨_, ha⟩ => ha.choose) ((fun ⟨_, ha⟩ => ha.choose) ∘ e₁)) 0)
      (fromRows 0 (A₂.submatrix (fun ⟨⟨_, ha⟩, _⟩ => ha.choose) ((fun ⟨_, ha⟩ => ha.choose) ∘ e₂)))
      0
      (A₂.submatrix (fun ⟨⟨_, ha⟩, _⟩ => ha.choose) ((fun ⟨_, ha⟩ => ha.choose) ∘ e₂))
    ).submatrix
      ((f.decomposeSum.trans ((Equiv.refl _).sumCongr e')).trans e₃)
      (g.decomposeSum.trans (Equiv.sumCongr e₁.symm e₂.symm))
  · ext
    simp only [Function.decomposeSum, Equiv.coe_fn_mk, Equiv.coe_trans, Equiv.sumCongr_apply, Function.comp_apply,
      Matrix.submatrix, Matrix.of_apply, e₃, e']
    split
    · split <;> simp [Equiv.sumCompl, Equiv.sumAssoc, Matrix.fromBlocks, Matrix.fromRows]
    · split <;>
        simp only [Matrix.fromBlocks, Matrix.fromRows, Sum.elim_inl, Sum.elim_inr, Sum.map_inl, Sum.map_inr,
          Equiv.sumAssoc, Equiv.sumCompl, Equiv.coe_fn_symm_mk, Set.mem_range, Matrix.zero_apply] <;> split <;>
        simp
  rw [hAfg, ←abs_eq_zero, Matrix.abs_det_submatrix_equiv_equiv, abs_eq_zero]
  convert_to
    (fromRows (A₁.submatrix (fun ⟨_, ha⟩ => ha.choose) ((fun ⟨_, ha⟩ => ha.choose) ∘ e₁)) 0).det *
              (A₂.submatrix (fun ⟨⟨_, ha⟩, _⟩ => ha.choose) ((fun ⟨_, ha⟩ => ha.choose) ∘ e₂)).det
      = 0
  · convert -- none of `exact` `apply` `rw` `erw` `simp_rw` works with `Matrix.det_fromBlocks_zero₂₁` here
      Matrix.det_fromBlocks_zero₂₁
        (fromRows (A₁.submatrix (fun ⟨_, ha⟩ => ha.choose) ((fun ⟨_, ha⟩ => ha.choose) ∘ e₁)) 0)
        (fromRows 0 (A₂.submatrix (fun ⟨⟨_, ha⟩, _⟩ => ha.choose) ((fun ⟨_, ha⟩ => ha.choose) ∘ e₂)))
        (A₂.submatrix (fun ⟨⟨_, ha⟩, _⟩ => ha.choose) ((fun ⟨_, ha⟩ => ha.choose) ∘ e₂))
  convert zero_mul _
  exact Matrix.det_eq_zero_of_row_eq_zero (Sum.inr (Classical.choice hX')) (fun _ => rfl)

omit Z

/-- The block matrix that has two totally unimodular matrices along the diagonal and zeros elsewhere is totally unimodular. -/
lemma Matrix.fromBlocks_isTotallyUnimodular {A₁ : Matrix X₁ Y₁ R} {A₂ : Matrix X₂ Y₂ R}
    (hA₁ : A₁.IsTotallyUnimodular) (hA₂ : A₂.IsTotallyUnimodular) :
    (fromBlocks A₁ 0 0 A₂).IsTotallyUnimodular :=
  fun k f g _ _ =>
    if hxy :
      Fintype.card (f ⁻¹' (Set.range Sum.inl)) =
      Fintype.card (g ⁻¹' (Set.range Sum.inl)) ∧
      Fintype.card (f ⁻¹' (Set.range Sum.inr)) =
      Fintype.card (g ⁻¹' (Set.range Sum.inr))
    then
      Matrix.fromBlocks_submatrix_det_in_set_range_singType_cast_of_isTotallyUnimodular_of_card_eq hA₁ hA₂ hxy
    else if hxy₁ :
      Fintype.card (f ⁻¹' (Set.range Sum.inl)) <
      Fintype.card (g ⁻¹' (Set.range Sum.inl))
    then
      Matrix.fromBlocks_submatrix_det_in_set_range_singType_cast_of_card_lt A₁ A₂ hxy₁
    else by
      rw [←Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose]
      apply Matrix.fromBlocks_submatrix_det_in_set_range_singType_cast_of_card_lt
      have := decomposeSum_card_eq f
      have := decomposeSum_card_eq g
      omega

#check Matrix.fromBlocks_isTotallyUnimodular
#print axioms Matrix.fromBlocks_isTotallyUnimodular
