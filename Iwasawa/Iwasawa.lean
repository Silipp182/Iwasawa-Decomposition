import Mathlib

/-
# The Iwasawa decomposition for `GLₙ` over a local field

Let `F` be a (non-archimedean) local field with valuation ring `o_F`.  The Iwasawa
decomposition states that

  `GLₙ(F) = GLₙ(o_F) · B`,

where `GLₙ(o_F)` is the (maximal compact) subgroup of matrices that are invertible
over `o_F`, and `B` is the group of invertible upper-triangular matrices over `F`.

We prove this in the natural generality of a **valuation ring** `A` with fraction
field `K` (a local field's valuation ring is a discrete valuation ring, hence a
valuation ring, and `ℤ_[p] ⊆ ℚ_[p]` is the guiding example, treated at the end).

The proof is Gaussian elimination: any `g ∈ GLₙ(K)` can be turned into an
upper-triangular matrix by left multiplication with elements of `GLₙ(A)` (row
permutations and row operations with coefficients in `A`).  The key input is that
in a valuation ring any two elements are comparable under divisibility, so each
column has an entry dividing all the others (the "pivot").
-/

open Matrix

namespace Iwasawa

variable (A : Type*) {K : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]

/-- `x : K` is *integral*, i.e. lies in the valuation ring `A ⊆ K`. --/
def IsInt (x : K) : Prop := x ∈ (algebraMap A K).range

/-- A matrix has all entries in the valuation ring `A`. --/
def IsIntMat {n : ℕ} (M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ i j, IsInt A (M i j)

/-- `M ∈ GLₙ(A)`: `M` has entries in `A` and a two-sided inverse with entries in `A`. --/
def InGLO {n : ℕ} (M : Matrix (Fin n) (Fin n) K) : Prop :=
  IsIntMat A M ∧ ∃ N, IsIntMat A N ∧ M * N = 1 ∧ N * M = 1

/-- The elementary matrix `1 + Σ_{i≠0} cᵢ E_{i,0}`: adding `A`-multiples of the
first row to the other rows (a unipotent lower-triangular matrix supported on the
first column). -/
def Lmat {n : ℕ} (c : Fin (n + 1) → K) : Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  1 + Matrix.of (fun i j => if j = 0 ∧ i ≠ 0 then c i else 0)

/-- Embed a matrix `k' : Matrix (Fin n) (Fin n) K` as the block-diagonal matrix
`diag(1, k')` of size `n+1`. -/
def blockDiagOne {n : ℕ} (k' : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.of (fun i j =>
    Fin.cases (motive := fun _ => K)
      (Fin.cases (motive := fun _ => K) (1 : K) (fun _ => (0 : K)) j)
      (fun a => Fin.cases (motive := fun _ => K) (0 : K) (fun b => k' a b) j) i)

/-! ### Basic facts about integrality and `GLₙ(A)` -/

/--
`x` is integral iff its valuation is `≤ 1`.
-/
-- Mathlib uses multiplicative valuations, so we have to convert between the two conventions. That is why the valuation is compared to `1` instead of `0`.
lemma isInt_iff_val_le (x : K) :
    IsInt A x ↔ ValuationRing.valuation A K x ≤ 1 := by
  convert Iff.rfl
  convert ValuationRing.mem_integer_iff A K x using 1

omit [IsDomain A] [ValuationRing A] [IsFractionRing A K] in
/-- The identity matrix is in `GLₙ(A)`. -/
lemma InGLO.one {n : ℕ} : InGLO A (1 : Matrix (Fin n) (Fin n) K) := by
  refine' ⟨ _, 1, _, _, _ ⟩ <;> norm_num;
  · intro i j; by_cases hij : i = j <;> simp [ hij, IsInt ] ;
    exact ⟨ 1, by aesop ⟩;
  · intro i j; by_cases hij : i = j <;> simp [ hij, IsInt ] ;
    exact ⟨ 1, by aesop ⟩


omit [IsDomain A] [ValuationRing A] [IsFractionRing A K] in
/-- `GLₙ(A)` is closed under multiplication. -/
lemma InGLO.mul {n : ℕ} {M N : Matrix (Fin n) (Fin n) K}
    (hM : InGLO A M) (hN : InGLO A N) : InGLO A (M * N) := by
  refine' ⟨ _, _ ⟩;
  · intro i j; have := hM.1; have := hN.1; simp_all [ IsIntMat, Matrix.mul_apply ] ;
    choose f hf using ‹∀ i j, IsInt A ( M i j ) ›; choose g hg using ‹∀ i j, IsInt A ( N i j ) ›; use ∑ k, f i k * g k j; simp [ *, map_sum, map_mul ] ;
  · obtain ⟨ N₁, hN₁, hN₂, hN₃ ⟩ := hM.2
    obtain ⟨ N₂, hN₄, hN₅, hN₆ ⟩ := hN.2
    use N₂ * N₁
    simp_all [ mul_assoc ];
    simp_all [ ← mul_assoc, IsIntMat ];
    simp_all [ Matrix.mul_apply, IsInt ];
    choose f hf using hN₄; choose g hg using hN₁; use fun i j => ⟨ ∑ k, f i k * g k j, by simp [ hf, hg, map_sum, map_mul ] ⟩ ;

omit [IsDomain A] [ValuationRing A] [IsFractionRing A K] in
/-- `GLₙ(A)` contains the permutation matrices. -/
lemma InGLO_permMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    InGLO A (σ.permMatrix K) := by
  constructor <;> norm_num [ Matrix.mul_apply, Equiv.Perm.permMatrix ];
  · intro i j; by_cases hij : σ i = j <;> simp [ hij ] ;
    · exact ⟨ 1, by simp ⟩;
    · exact ⟨ 0, by simp ⟩;
  · refine' ⟨ ( Equiv.toPEquiv σ⁻¹ ).toMatrix, _, _, _ ⟩;
    · intro i j; simp [ PEquiv.toMatrix_apply ] ;
      split_ifs <;> [ exact ⟨ 1, by simp ⟩ ; exact ⟨ 0, by simp ⟩ ];
    · ext i j; simp [ Matrix.mul_apply, Equiv.toPEquiv ];
      rw [ Finset.sum_eq_single ( σ i ) ] <;> aesop;
    · ext i j; simp [ Matrix.mul_apply, Equiv.toPEquiv ];
      rw [ Finset.sum_eq_single ( σ.symm i ) ] <;>aesop

/-! ### The elementary column-clearing matrix `Lmat` -/

/-- Left Multiplication by `Lmat c` adds `c i` times the first row to the `i`-th row, for `i ≠ 0`. -/
lemma Lmat_mul_apply_col0 {n : ℕ} (c : Fin (n + 1) → K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (i : Fin (n + 1)) (hi : i ≠ 0) :
    (Lmat c * M) i 0 = M i 0 + c i * M 0 0 := by
  simp [Lmat, Matrix.mul_apply, hi];
  simp_all [ Finset.sum_add_distrib, add_mul ];
  simp [Matrix.one_apply]

/-- Left multiplication by `Lmat c` does not change the `(0,0)` entry of a matrix. -/
lemma Lmat_mul_apply_col0_zero {n : ℕ} (c : Fin (n + 1) → K)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    (Lmat c * M) 0 0 = M 0 0 := by
  unfold Lmat;
  simp [Matrix.mul_apply];
  simp [ Matrix.one_apply ]


omit [IsDomain A] in
/-- `Lmat c` lies in `GLₙ(A)` if the coefficients `c i` are integral. -/
lemma InGLO_Lmat {n : ℕ} (c : Fin (n + 1) → K) (hc : ∀ i, IsInt A (c i)) :
    InGLO A (Lmat c) := by
  refine' ⟨ _, _ ⟩;
  · intro i j; by_cases hij : j = 0 ∧ i ≠ 0 <;> simp [ hij, hc, Lmat ] ;
    by_cases hij' : i = j <;> simp_all [ Matrix.one_apply ];
    · exact ⟨ 1, by simp ⟩;
    · exact ⟨ 0, by simp ⟩;
  · refine' ⟨ 1 - Matrix.of ( fun i j => if j = 0 ∧ i ≠ 0 then c i else 0 ), _, _, _ ⟩ <;> simp [ IsIntMat, Lmat ];
    · intro i j; split_ifs <;> simp_all [ IsInt ] ;
      by_cases hij : i = j <;> aesop;
    · simp [Matrix.mul_sub, add_mul, mul_one];
      ext i j; simp [ Matrix.mul_apply ] ;
      rw [ Finset.sum_eq_zero ] ; aesop;
    · ext i j ; by_cases hi : i = j <;> simp [ *, Matrix.mul_apply ];
      · simp [ *, Finset.sum_add_distrib, sub_mul, mul_add, Matrix.one_apply ];
        rw [ Finset.sum_eq_zero ] ; aesop;
      · simp [Matrix.one_apply, Finset.sum_add_distrib, sub_mul, mul_add, hi];
        rw [ Finset.sum_eq_single i ] <;> aesop

/-! ### The block-diagonal embedding -/

/-- Embedding n×n identity matrix as the block-diagonal matrix diag(1, 1) of size n+1. -/
lemma blockDiagOne_one {n : ℕ} :
    blockDiagOne (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  ext i j; refine Fin.cases ?_ ?_ i <;> refine Fin.cases ?_ ?_ j <;> simp [ blockDiagOne ] ;
  · simp [ Matrix.one_apply ];
    exact fun i => ne_of_lt ( Fin.succ_pos i );
  · simp [Matrix.one_apply ]

/-- The block-diagonal embedding is multiplicative: diag(1, k₁ * k₂) = diag(1, k₁) * diag(1, k₂). -/
lemma blockDiagOne_mul {n : ℕ} (k₁ k₂ : Matrix (Fin n) (Fin n) K) :
    blockDiagOne (k₁ * k₂) = blockDiagOne k₁ * blockDiagOne k₂ := by
  ext i j; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [ *, Matrix.mul_apply, Fin.sum_univ_succ ] ; ring_nf;
  · simp [ blockDiagOne ];
  · unfold blockDiagOne; aesop;
  · unfold blockDiagOne; simp [Matrix.mul_apply] ;
  · rcases i with ⟨ _ | i, hi ⟩ <;> rcases j with ⟨ _ | j, hj ⟩ <;> simp [blockDiagOne] at *;
    rfl

omit [IsDomain A] [ValuationRing A] [IsFractionRing A K] in
/-- If k' ∈ GLₙ(A), then diag(1, k') ∈ GLₙ(A). -/
lemma InGLO_blockDiagOne {n : ℕ} {k' : Matrix (Fin n) (Fin n) K}
    (hk : InGLO A k') : InGLO A (blockDiagOne k') := by
  -- By definition of $blockDiagOne$, we know that this matrix has entries in $A$.
  have h_blockDiagOne_entries : IsIntMat A (blockDiagOne k') ∧ IsIntMat A (blockDiagOne (hk.2.choose)) := by
    constructor <;> intro i j <;> simp [ blockDiagOne ];
    · refine' Fin.cases _ _ i <;> refine' Fin.cases _ _ j <;> simp;
      · exact ⟨ 1, map_one _ ⟩;
      · exact fun _ => ⟨ 0, by simp ⟩;
      · exact fun _ => ⟨ 0, by simp ⟩;
      · exact fun i j => hk.1 j i;
    · refine' Fin.cases _ _ i <;> refine' Fin.cases _ _ j <;> simp [ IsIntMat ];
      · exact ⟨ 1, by simp ⟩;
      · exact fun _ => ⟨ 0, by simp ⟩;
      · exact fun _ => ⟨ 0, by simp ⟩;
      · exact fun i j => hk.2.choose_spec.1 j i;
  refine' ⟨ h_blockDiagOne_entries.1, _, h_blockDiagOne_entries.2, _ ⟩;
  have := hk.2.choose_spec;
  exact ⟨ by rw [ ← blockDiagOne_mul, this.2.1, blockDiagOne_one ], by rw [ ← blockDiagOne_mul, this.2.2, blockDiagOne_one ] ⟩

/--
If the first column of `M2` is cleared below the diagonal and `k' * (trailing block)`
is upper triangular, then `diag(1,k') * M2` is upper triangular.
-/
lemma blockDiagOne_mul_upperTri {n : ℕ} (k' : Matrix (Fin n) (Fin n) K)
    (M2 : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hcol : ∀ i, i ≠ 0 → M2 i 0 = 0)
    (hUT : Matrix.BlockTriangular (k' * M2.submatrix Fin.succ Fin.succ) (id : Fin n → Fin n)) :
    Matrix.BlockTriangular (blockDiagOne k' * M2) (id : Fin (n + 1) → Fin (n + 1)) := by
  intro i j hij; induction' i with i hi generalizing j; induction' j with j hj generalizing k' M2; simp_all [ Fin.forall_fin_succ, Matrix.mul_apply ] ;
  rcases i with ( _ | i ) <;> rcases j with ( _ | j ) <;> simp_all [ Fin.sum_univ_succ, blockDiagOne ];
  convert hUT ( show ⟨ j, by linarith ⟩ < ⟨ i, by linarith ⟩ from hij ) using 1

/-! ### Auxiliary determinant/pivot lemmas -/

/--
An invertible matrix has a nonzero entry in its first column.
-/
lemma exists_col0_ne {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (h : IsUnit M.det) : ∃ i, M i 0 ≠ 0 := by
  exact not_forall.mp fun H => h.ne_zero <| by rw [ Matrix.det_eq_zero_of_column_eq_zero 0 fun i => by aesop ] ;

/--
After clearing the first column, the trailing block stays invertible.
-/
-- determinant of the trailing block of a matrix with zeros in the first column below the diagonal is invertible if the original matrix is invertible.
lemma isUnit_det_submatrix_of_col_cleared {n : ℕ}
    (N : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hcol : ∀ i, i ≠ 0 → N i 0 = 0) (h : IsUnit N.det) :
    IsUnit (N.submatrix Fin.succ Fin.succ).det := by
  have h_submatrix_det : N.det = N 0 0 * Matrix.det (N.submatrix Fin.succ Fin.succ) := by
    convert Matrix.det_succ_column_zero N using 1;
    rw [ Finset.sum_eq_single_of_mem 0 ] <;> simp_all [ Fin.succAbove_zero ];
  aesop

/-- Every column of an invertible matrix has an entry dividing all others (the pivot).
-/
lemma pivot {n : ℕ} (v : Fin n → K) (hv : ∃ i, v i ≠ 0) :
    ∃ i0, v i0 ≠ 0 ∧ ∀ j, IsInt A (v j / v i0) := by
  -- By definition of IsInt, we need to show that for each j (v j / v i0) is in the range of the algebra map from A to K.
  suffices h_exists_i0 : ∃ i0, v i0 ≠ 0 ∧ ∀ j, ValuationRing.valuation A K (v j / v i0) ≤ 1 by
    exact ⟨ h_exists_i0.choose, h_exists_i0.choose_spec.1, fun j => isInt_iff_val_le _ ( v j / v h_exists_i0.choose ) |>.2 ( h_exists_i0.choose_spec.2 j ) ⟩;
  -- By definition of `ValuationRing.valuation`, we know that `ValuationRing.valuation A K (v j / v i0) = ValuationRing.valuation A K (v j) / ValuationRing.valuation A K (v i0)`.
  suffices h_exists_i0 : ∃ i0, v i0 ≠ 0 ∧ ∀ j, ValuationRing.valuation A K (v j) ≤ ValuationRing.valuation A K (v i0) by
    obtain ⟨ i0, hi0 ⟩ := h_exists_i0; use i0; simp_all [div_eq_mul_inv] ;
    exact fun j => div_le_one_of_le₀ ( hi0.2 j ) ( by simp );
  have := Finset.exists_max_image Finset.univ ( fun i => ValuationRing.valuation A K ( v i ) ) ⟨ hv.choose, Finset.mem_univ _ ⟩ ; aesop;

/--
Bring a pivot of the first column to the top by a permutation in `GLₙ(A)`.
-/
lemma pivot_to_top {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (hM : ∃ i, M i 0 ≠ 0) :
    ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) K,
      InGLO A P ∧ (P * M) 0 0 ≠ 0 ∧ ∀ j, IsInt A ((P * M) j 0 / (P * M) 0 0) := by
  obtain ⟨ i0, hi0 ⟩ := pivot A ( fun i => M i 0 ) hM;
  -- Let P be the permutation matrix corresponding to the swap of 0 and i0.
  use (Equiv.swap 0 i0).permMatrix K;
  refine' ⟨ InGLO_permMatrix A _, _, _ ⟩;
  · simp [ *, Matrix.mul_apply ];
  · simp_all [ Matrix.mul_apply, Equiv.swap_apply_def ]

/-! ### The core elimination lemma and the main theorem -/

/--
**Core lemma.** Any invertible matrix in `GLₙ(K)` can be made upper triangular by left
multiplication with an element of `GLₙ(A)`.
-/
theorem core : ∀ {n : ℕ} (g : Matrix (Fin n) (Fin n) K), IsUnit g.det →
    ∃ k, InGLO A k ∧ Matrix.BlockTriangular (k * g) (id : Fin n → Fin n) := by
  intro n g hM;
  induction' n with n ih;
  · refine' ⟨ 1, _, _ ⟩ <;> simp [ InGLO.one, Matrix.BlockTriangular ];
  · -- By pivot_to_top A g (exists_col0_ne A g hM), get P with hP : InGLO A P, hP00 : (P*g) 0 0 ≠ 0, hPdiv : ∀ j, IsInt A ((P*g) j 0 / (P*g) 0 0).
    obtain ⟨P, hP, hP00, hPdiv⟩ : ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) K, InGLO A P ∧ (P * g) 0 0 ≠ 0 ∧ ∀ j, IsInt A ((P * g) j 0 / (P * g) 0 0) := by
      apply pivot_to_top;
      grind +suggestions;
    -- Set L := Lmat c; InGLO A L by InGLO_Lmat A c (that ∀ i, IsInt A (c i)). This is the transvection matrix that clears the first column of P*g below the diagonal. Let M2 := L * (P*g). Then M2 i 0 = 0 for i > 0.
    let c : Fin (n + 1) → K := fun i => -(P * g) i 0 / (P * g) 0 0
    have hL : InGLO A (Lmat c) := by
      apply InGLO_Lmat;
      intro i
      simp [c]
      obtain ⟨ x, hx ⟩ := hPdiv i; use -x; simp [hx, neg_div ] ;
    let g1 := Lmat c * (P * g);
    -- Column-clearing: for i ≠ 0, M2 i 0 = 0.
    have hcol : ∀ i, i ≠ 0 → g1 i 0 = 0 := by
      intro i hi
      grind +suggestions;
      -- alternatively:
      -- simp only [g1, c]
      -- rw [ Lmat_mul_apply_col0 ] <;> simp [ *, neg_div ];
    -- Trailing block: let g' := g1.submatrix Fin.succ Fin.succ. By isUnit_det_submatrix_of_col_cleared g1 hcol (IsUnit g1.det), IsUnit g'.det.
    have hg' : IsUnit (g1.submatrix Fin.succ Fin.succ).det := by
      apply isUnit_det_submatrix_of_col_cleared g1 hcol;
      have hP_det : IsUnit P.det := by
        obtain ⟨ PInv, hPInv, hPN, hNP ⟩ := hP.2;
        exact isUnit_iff_exists_inv.mpr ⟨ PInv.det, by rw [ ← Matrix.det_mul, hPN, Matrix.det_one ] ⟩
      have hL_det : IsUnit (Lmat c).det := by
        obtain ⟨ LMatInv, hLMatInv, hN' ⟩ := hL.2;
        exact isUnit_iff_exists_inv.mpr ⟨ LMatInv.det, by rw [ ← Matrix.det_mul, hN'.1, Matrix.det_one ] ⟩;
      aesop;
    obtain ⟨ k', hk', hk'' ⟩ := ih _ hg';
    refine' ⟨ blockDiagOne k' * Lmat c * P, _, _ ⟩;
    · exact InGLO.mul A ( InGLO.mul A ( InGLO_blockDiagOne A hk' ) hL ) hP;
    · convert blockDiagOne_mul_upperTri k' g1 hcol hk'' using 1;
      simp[ Matrix.mul_assoc, g1 ]

/--
**Iwasawa decomposition.** `GLₙ(K) = GLₙ(A) · B`, where `B` ranges over
invertible upper-triangular matrices: every invertible `g` factors as `g = k * b`
with `k ∈ GLₙ(A)` and `b` invertible upper triangular.
-/
theorem iwasawa {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (hg : IsUnit g.det) :
    ∃ k b, InGLO A k ∧ Matrix.BlockTriangular b (id : Fin n → Fin n) ∧
      IsUnit b.det ∧ g = k * b := by
  obtain ⟨ k, hk, h ⟩ := core A g hg;
  -- Now, g = k * b with b := k⁻¹ * g upper triangular. We need to show that b is invertible and upper triangular. In the code, k' = k⁻¹.
  rcases hk with ⟨ hk₁, k', hk'₁, hk'₂, hk'₃ ⟩;
  refine' ⟨ k', k * g, _, _, _, _⟩;
  · exact ⟨ hk'₁, k, hk₁, hk'₃, hk'₂ ⟩;
  · exact h;
  · have hkdet : IsUnit k.det := by
      rw [isUnit_iff_ne_zero]
      intro hk_zero
      have hdet := congr_arg Matrix.det hk'₂
      simp [Matrix.det_mul, hk_zero] at hdet
    simpa [Matrix.det_mul] using hkdet.mul hg
  · rw [ ← Matrix.mul_assoc, hk'₃, Matrix.one_mul ]

/-! ### The `p`-adic special case -/

/-- **Iwasawa decomposition for the `p`-adics.** For `GLₙ(ℚ_[p])` we have
`GLₙ(ℚ_[p]) = GLₙ(ℤ_[p]) · B`. -/
theorem iwasawa_padic (p : ℕ) [Fact p.Prime] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) ℚ_[p]) (hg : IsUnit g.det) :
    ∃ k b, InGLO ℤ_[p] k ∧ Matrix.BlockTriangular b (id : Fin n → Fin n) ∧
      IsUnit b.det ∧ g = k * b :=
  iwasawa ℤ_[p] g hg

end Iwasawa
