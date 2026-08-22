import Mathlib

#eval Lean.versionString

/-!
# Green's Open Problem 29: standalone Lean4Web proof

This file reproduces the proposition in the exact Formal Conjectures target and proves that it is
false using mathlib only.

The proof is adapted from the public, kernel-verified solution for submission
`82ab85ee-5dfc-4775-b3e1-8abc16e213b9`.  The public validator credits the submission to hotkey
`5GeGrYFpMrNSh3Nwcx987zWz4cME9A9NbCkEbjBvv4uLUScV`.
-/

open scoped Pointwise

namespace Green29Lean4Web

private def slabCoord {H : Type*} (g : Multiplicative ℤ × H) : ℤ :=
  Multiplicative.toAdd g.1

private def slabOuter (H : Type*) [Group H] [Fintype H] [DecidableEq H] :
    Finset (Multiplicative ℤ × H) :=
  ({Multiplicative.ofAdd (-1 : ℤ), Multiplicative.ofAdd (1 : ℤ)} :
      Finset (Multiplicative ℤ)) ×ˢ (Finset.univ : Finset H)

private def slabA (H : Type*) [Group H] [Fintype H] [DecidableEq H] :
    Finset (Multiplicative ℤ × H) :=
  slabOuter H ∪ {(Multiplicative.ofAdd (0 : ℤ), 1)}

private def slabX (H : Type*) [Group H] [DecidableEq H] :
    Finset (Multiplicative ℤ × H) :=
  {(Multiplicative.ofAdd (-1 : ℤ), 1),
   (Multiplicative.ofAdd (0 : ℤ), 1),
   (Multiplicative.ofAdd (1 : ℤ), 1)}

private lemma slab_mem_iff (H : Type*) [Group H] [Fintype H] [DecidableEq H]
    (g : Multiplicative ℤ × H) :
    g ∈ slabA H ↔
      g.1 = Multiplicative.ofAdd (-1 : ℤ) ∨
      g.1 = Multiplicative.ofAdd (1 : ℤ) ∨
      g = (Multiplicative.ofAdd (0 : ℤ), 1) := by
  (simp [slabA, slabOuter] ; tauto)

private lemma slabCoord_mul {H : Type*} [Group H]
    (x y : Multiplicative ℤ × H) :
    slabCoord (x * y) = slabCoord x + slabCoord y := by
  simp [slabCoord]

private lemma slabCoord_pow {H : Type*} [Group H]
    (g : Multiplicative ℤ × H) (n : ℕ) :
    slabCoord (g ^ n) = n • slabCoord g := by
  simp [slabCoord]

private lemma slab_mem_coord_bound (H : Type*) [Group H] [Fintype H] [DecidableEq H]
    {g : Multiplicative ℤ × H} (hg : g ∈ slabA H) :
    -1 ≤ slabCoord g ∧ slabCoord g ≤ 1 := by
  rw [slab_mem_iff] at hg
  rcases hg with h | h | h
  · have hc : slabCoord g = -1 := by simp [slabCoord, h]
    omega
  · have hc : slabCoord g = 1 := by simp [slabCoord, h]
    omega
  · subst g
    norm_num [slabCoord]

private lemma slab_pow_coord_bound (H : Type*) [Group H] [Fintype H] [DecidableEq H]
    (m : ℕ) {g : Multiplicative ℤ × H} (hg : g ∈ slabA H ^ m) :
    -(m : ℤ) ≤ slabCoord g ∧ slabCoord g ≤ (m : ℤ) := by
  induction m generalizing g with
  | zero =>
      have h : g = 1 := by simpa using hg
      subst g
      simp [slabCoord]
  | succ m ih =>
      rw [pow_succ] at hg
      rcases Finset.mem_mul.mp hg with ⟨x, hx, y, hy, hxy⟩
      subst g
      have hx' := ih hx
      have hy' := slab_mem_coord_bound H hy
      rw [slabCoord_mul]
      omega

private lemma slabX_mem_of_bounds (H : Type*) [Group H] [DecidableEq H]
    (z : ℤ) (hl : -1 ≤ z) (hu : z ≤ 1) :
    (Multiplicative.ofAdd z, 1) ∈ slabX H := by
  have hz : z = -1 ∨ z = 0 ∨ z = 1 := by omega
  rcases hz with rfl | rfl | rfl <;> simp [slabX]

private lemma slab_neg_one_mem (H : Type*) [Group H] [Fintype H] [DecidableEq H]
    (h : H) :
    (Multiplicative.ofAdd (-1 : ℤ), h) ∈ slabA H := by
  simp [slabA, slabOuter]

private lemma slab_one_mem (H : Type*) [Group H] [Fintype H] [DecidableEq H]
    (h : H) :
    (Multiplicative.ofAdd (1 : ℤ), h) ∈ slabA H := by
  simp [slabA, slabOuter]

private lemma slab_sq_subset_mul (H : Type*) [Group H] [Fintype H] [DecidableEq H] :
    slabA H ^ 2 ⊆ slabX H * slabA H := by
  intro g hg
  rw [pow_two] at hg
  rcases Finset.mem_mul.mp hg with ⟨a, ha, b, hb, hab⟩
  subst g
  have ha' := slab_mem_coord_bound H ha
  have hb' := slab_mem_coord_bound H hb
  let q : ℤ := slabCoord a + slabCoord b
  have hqlo : -2 ≤ q := by dsimp [q]; omega
  have hqhi : q ≤ 2 := by dsimp [q]; omega
  by_cases hq : q ≤ 0
  · refine Finset.mem_mul.mpr
      ⟨(Multiplicative.ofAdd (q + 1), 1),
       slabX_mem_of_bounds H (q + 1) (by omega) (by omega),
       (Multiplicative.ofAdd (-1 : ℤ), a.2 * b.2),
       slab_neg_one_mem H (a.2 * b.2), ?_⟩
    apply Prod.ext
    · apply Multiplicative.ext
      simp [q, slabCoord]
    · simp
  · refine Finset.mem_mul.mpr
      ⟨(Multiplicative.ofAdd (q - 1), 1),
       slabX_mem_of_bounds H (q - 1) (by omega) (by omega),
       (Multiplicative.ofAdd (1 : ℤ), a.2 * b.2),
       slab_one_mem H (a.2 * b.2), ?_⟩
    apply Prod.ext
    · apply Multiplicative.ext
      simp [q, slabCoord]
    · simp

private lemma slab_inv_mem_iff (H : Type*) [Group H] [Fintype H] [DecidableEq H]
    (g : Multiplicative ℤ × H) :
    g⁻¹ ∈ slabA H ↔ g ∈ slabA H := by
  have forward : ∀ x : Multiplicative ℤ × H, x⁻¹ ∈ slabA H → x ∈ slabA H := by
    intro x hx
    rw [slab_mem_iff] at hx ⊢
    rcases hx with h | h | h
    · right
      left
      have h' := congrArg Inv.inv h
      simpa using h'
    · left
      have h' := congrArg Inv.inv h
      simpa using h'
    · right
      right
      have h' := congrArg Inv.inv h
      simpa using h'
  constructor
  · exact forward g
  · intro hg
    exact forward (g⁻¹) (by simpa using hg)

private lemma slab_inv_eq (H : Type*) [Group H] [Fintype H] [DecidableEq H] :
    (↑(slabA H) : Set (Multiplicative ℤ × H))⁻¹ = ↑(slabA H) := by
  ext g
  simpa using slab_inv_mem_iff H g

private lemma slab_isApproximateSubgroup
    (H : Type*) [Group H] [Fintype H] [DecidableEq H] :
    IsApproximateSubgroup 3
      (↑(slabA H) : Set (Multiplicative ℤ × H)) := by
  refine ⟨?_, slab_inv_eq H, ?_⟩
  · change (1 : Multiplicative ℤ × H) ∈ slabA H
    rw [slabA]
    exact Finset.mem_union_right _ (by simp; rfl)
  · refine ⟨slabX H, ?_, ?_⟩
    · have hcard : (slabX H).card ≤ 3 := by
        unfold slabX
        exact Finset.card_le_three
      exact_mod_cast hcard
    · intro g hg
      have hg' : g ∈ slabA H ^ 2 := by
        simpa only [← Finset.coe_pow, Finset.mem_coe] using hg
      have hm := slab_sq_subset_mul H hg'
      simpa only [← Finset.mem_coe, Finset.coe_mul, smul_eq_mul] using hm

private lemma slab_good_subset_singleton
    (H : Type*) [Group H] [Fintype H] [DecidableEq H]
    {S : Finset (Multiplicative ℤ × H)}
    (hSA : S ⊆ slabA H) (hpow : S ^ 8 ⊆ slabA H ^ 4) :
    S ⊆ {(Multiplicative.ofAdd (0 : ℤ), 1)} := by
  intro s hs
  have hs8 : s ^ 8 ∈ S ^ 8 := Finset.pow_mem_pow (n := 8) hs
  have hA4 := hpow hs8
  have hb := slab_pow_coord_bound H 4 hA4
  rw [slabCoord_pow] at hb
  norm_num [Int.nsmul_eq_mul] at hb
  have hzero : slabCoord s = 0 := by omega
  have hsA := hSA hs
  rw [slab_mem_iff] at hsA
  rcases hsA with h | h | h
  · have hc : slabCoord s = -1 := by simp [slabCoord, h]
    omega
  · have hc : slabCoord s = 1 := by simp [slabCoord, h]
    omega
  · simp [h]

private lemma slab_good_card_le_one
    (H : Type*) [Group H] [Fintype H] [DecidableEq H]
    {S : Finset (Multiplicative ℤ × H)}
    (hSA : S ⊆ slabA H) (hpow : S ^ 8 ⊆ slabA H ^ 4) :
    S.card ≤ 1 := by
  calc
    S.card ≤ ({(Multiplicative.ofAdd (0 : ℤ), 1)} :
        Finset (Multiplicative ℤ × H)).card :=
      Finset.card_le_card (slab_good_subset_singleton H hSA hpow)
    _ = 1 := by simp

private def slabFiber (H : Type*) [Group H] [Fintype H] [DecidableEq H] :
    Finset (Multiplicative ℤ × H) :=
  ({Multiplicative.ofAdd (1 : ℤ)} : Finset (Multiplicative ℤ)) ×ˢ
    (Finset.univ : Finset H)

private lemma slabFiber_subset (H : Type*) [Group H] [Fintype H] [DecidableEq H] :
    slabFiber H ⊆ slabA H := by
  intro g hg
  rcases Finset.mem_product.mp hg with ⟨h1, h2⟩
  apply Finset.mem_union_left
  exact Finset.mem_product.mpr ⟨Finset.mem_insert_of_mem h1, h2⟩

private lemma fintype_card_le_slabA_card
    (H : Type*) [Group H] [Fintype H] [DecidableEq H] :
    Fintype.card H ≤ (slabA H).card := by
  have h := Finset.card_le_card (slabFiber_subset H)
  simpa [slabFiber] using h

/-- The exact mathematical proposition in `Green29.green_29` is false. -/
theorem green_29_proposition_false :
    ¬ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {G : Type*} [Group G] [DecidableEq G] (K : ℝ) (A : Finset G),
        1 ≤ K → IsApproximateSubgroup K (A : Set G) →
          ∃ S ⊆ A, C * K ^ (-c) * (A.card : ℝ) ≤ (S.card : ℝ) ∧
          S ^ 8 ⊆ A ^ 4 := by
  intro h
  rcases h with ⟨C, c, hC, hc, hall⟩
  let α : ℝ := C * (3 : ℝ) ^ (-c)
  have hα : 0 < α := by
    dsimp [α]
    positivity
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (1 / α)
  let H := ULift (Multiplicative (Fin (n + 1)))
  let A : Finset (Multiplicative ℤ × H) := slabA H
  have hApprox : IsApproximateSubgroup (3 : ℝ)
      (↑A : Set (Multiplicative ℤ × H)) := by
    dsimp [A]
    exact slab_isApproximateSubgroup H
  rcases hall (G := Multiplicative ℤ × H) 3 A (by norm_num) hApprox with
    ⟨S, hSA, hsize, hpow⟩
  have hAcardNat : n + 1 ≤ A.card := by
    calc
      n + 1 = Fintype.card H := by simp [H]
      _ ≤ A.card := by
        dsimp [A]
        exact fintype_card_le_slabA_card H
  have hAcardReal : ((n + 1 : ℕ) : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast hAcardNat
  have h1n : (1 : ℝ) < (n : ℝ) * α := (div_lt_iff₀ hα).mp hn
  have hnle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
  have h1succ : (1 : ℝ) < α * ((n + 1 : ℕ) : ℝ) := by
    calc
      1 < (n : ℝ) * α := h1n
      _ ≤ ((n + 1 : ℕ) : ℝ) * α :=
        mul_le_mul_of_nonneg_right hnle (le_of_lt hα)
      _ = α * ((n + 1 : ℕ) : ℝ) := by ring
  have hSgt : (1 : ℝ) < (S.card : ℝ) := by
    calc
      1 < α * ((n + 1 : ℕ) : ℝ) := h1succ
      _ ≤ α * (A.card : ℝ) :=
        mul_le_mul_of_nonneg_left hAcardReal (le_of_lt hα)
      _ ≤ (S.card : ℝ) := by simpa [α] using hsize
  have hSleNat : S.card ≤ 1 := by
    apply slab_good_card_le_one H
    · simpa [A] using hSA
    · simpa [A] using hpow
  have hSle : (S.card : ℝ) ≤ 1 := by exact_mod_cast hSleNat
  linarith

/-- Standalone version of the proposed `answer(False)` wrapper. -/
theorem green_29_answer_false :
    False ↔
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ {G : Type*} [Group G] [DecidableEq G] (K : ℝ) (A : Finset G),
          1 ≤ K → IsApproximateSubgroup K (A : Set G) →
            ∃ S ⊆ A, C * K ^ (-c) * (A.card : ℝ) ≤ (S.card : ℝ) ∧
            S ^ 8 ⊆ A ^ 4 := by
  simpa using green_29_proposition_false

#print axioms green_29_answer_false

end Green29Lean4Web
