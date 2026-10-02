-- ════════════════════════════════════════════════════════════════════════
-- HexLemmas.lean  (v0.6.1)
-- Elementary sum lemmas for HexForge, proved WITHOUT sorry/admit/axiom.
--
-- The large faces k = 7..10 are split off individually; k ≥ 11 stays as a tail
-- (Finset.Ico 11 (m+1)).  The split lemmas rewrite the Inventory sums over
-- Finset.Ico 7 (m+1) / Finset.Ico 3 (m+1) into explicit p_i 7..p_i 10 plus the
-- tail; the tail lemmas bound the k ≥ 11 part.  For m < 10, faces beyond m are 0
-- by p_range.
-- ════════════════════════════════════════════════════════════════════════
import Mathlib
import Inventory

open Finset

namespace SimplyCon3ConnectedMap
variable {g : ℤ}

-- ── split lemmas: Finset.Ico 7 (m+1) = {7,8,9,10} ∪ Finset.Ico 11 (m+1) ──────

/-- face_split (expanded): f_2 = p_3 + … + p_10 + Σ_{k≥11} p_k. -/
lemma face_split (M : SimplyCon3ConnectedMap g) (hM : IsMap M) :
    (∑ k ∈ Finset.Ico 3 (M.m + 1), M.p_i k) =
      M.p_i 3 + M.p_i 4 + M.p_i 5 + M.p_i 6 + M.p_i 7 + M.p_i 8 + M.p_i 9 + M.p_i 10 +
      ∑ k ∈ Finset.Ico 11 (M.m + 1), M.p_i k := by
  have hfin : (∑ k ∈ (Finset.Ico 3 11 : Finset ℕ), M.p_i k) =
      M.p_i 3 + M.p_i 4 + M.p_i 5 + M.p_i 6 + M.p_i 7 + M.p_i 8 + M.p_i 9 + M.p_i 10 := by
    rw [show (Finset.Ico 3 11 : Finset ℕ) = {3, 4, 5, 6, 7, 8, 9, 10} from by decide,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  by_cases hm : 11 ≤ M.m + 1
  · rw [← Finset.sum_Ico_consecutive _ (show 3 ≤ 11 from by norm_num) hm, hfin]
  · push_neg at hm
    rw [show (Finset.Ico 11 (M.m + 1) : Finset ℕ) = ∅ from Finset.Ico_eq_empty (by omega),
        Finset.sum_empty, add_zero]
    have hext : (∑ k ∈ Finset.Ico 3 (M.m + 1), M.p_i k) =
        ∑ k ∈ (Finset.Ico 3 11 : Finset ℕ), M.p_i k := by
      apply Finset.sum_subset (Finset.Ico_subset_Ico_right (by omega : M.m + 1 ≤ 11))
      intro k hk hkm
      simp only [Finset.mem_Ico] at hk hkm
      exact p_range M hM k (by omega)
    rw [hext, hfin]

/-- split_count (ℤ): Σ_{k≥7} p_k = p_7 + p_8 + p_9 + p_10 + Σ_{k≥11} p_k. -/
lemma split_count (M : SimplyCon3ConnectedMap g) (hM : IsMap M) :
    (∑ k ∈ Finset.Ico 7 (M.m + 1), (M.p_i k : ℤ)) =
      (M.p_i 7 : ℤ) + (M.p_i 8 : ℤ) + (M.p_i 9 : ℤ) + (M.p_i 10 : ℤ) +
      ∑ k ∈ Finset.Ico 11 (M.m + 1), (M.p_i k : ℤ) := by
  have hfin : (∑ k ∈ (Finset.Ico 7 11 : Finset ℕ), (M.p_i k : ℤ)) =
      (M.p_i 7 : ℤ) + (M.p_i 8 : ℤ) + (M.p_i 9 : ℤ) + (M.p_i 10 : ℤ) := by
    rw [show (Finset.Ico 7 11 : Finset ℕ) = {7, 8, 9, 10} from by decide,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  by_cases hm : 11 ≤ M.m + 1
  · rw [← Finset.sum_Ico_consecutive _ (show 7 ≤ 11 from by norm_num) hm, hfin]
  · push_neg at hm
    rw [show (Finset.Ico 11 (M.m + 1) : Finset ℕ) = ∅ from Finset.Ico_eq_empty (by omega),
        Finset.sum_empty, add_zero]
    have hext : (∑ k ∈ Finset.Ico 7 (M.m + 1), (M.p_i k : ℤ)) =
        ∑ k ∈ (Finset.Ico 7 11 : Finset ℕ), (M.p_i k : ℤ) := by
      apply Finset.sum_subset (Finset.Ico_subset_Ico_right (by omega : M.m + 1 ≤ 11))
      intro k hk hkm
      simp only [Finset.mem_Ico] at hk hkm
      simp [p_range M hM k (by omega)]
    rw [hext, hfin]

/-- split_W (ℤ): Σ_{k≥7}(k−6)p_k = p_7 + 2p_8 + 3p_9 + 4p_10 + Σ_{k≥11}(k−6)p_k. -/
lemma split_W (M : SimplyCon3ConnectedMap g) (hM : IsMap M) :
    (∑ k ∈ Finset.Ico 7 (M.m + 1), ((k : ℤ) - 6) * (M.p_i k : ℤ)) =
      (M.p_i 7 : ℤ) + 2 * (M.p_i 8 : ℤ) + 3 * (M.p_i 9 : ℤ) + 4 * (M.p_i 10 : ℤ) +
      ∑ k ∈ Finset.Ico 11 (M.m + 1), ((k : ℤ) - 6) * (M.p_i k : ℤ) := by
  have hfin : (∑ k ∈ (Finset.Ico 7 11 : Finset ℕ), ((k : ℤ) - 6) * (M.p_i k : ℤ)) =
      (M.p_i 7 : ℤ) + 2 * (M.p_i 8 : ℤ) + 3 * (M.p_i 9 : ℤ) + 4 * (M.p_i 10 : ℤ) := by
    rw [show (Finset.Ico 7 11 : Finset ℕ) = {7, 8, 9, 10} from by decide,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
    push_cast; ring
  by_cases hm : 11 ≤ M.m + 1
  · rw [← Finset.sum_Ico_consecutive _ (show 7 ≤ 11 from by norm_num) hm, hfin]
  · push_neg at hm
    rw [show (Finset.Ico 11 (M.m + 1) : Finset ℕ) = ∅ from Finset.Ico_eq_empty (by omega),
        Finset.sum_empty, add_zero]
    have hext : (∑ k ∈ Finset.Ico 7 (M.m + 1), ((k : ℤ) - 6) * (M.p_i k : ℤ)) =
        ∑ k ∈ (Finset.Ico 7 11 : Finset ℕ), ((k : ℤ) - 6) * (M.p_i k : ℤ) := by
      apply Finset.sum_subset (Finset.Ico_subset_Ico_right (by omega : M.m + 1 ≤ 11))
      intro k hk hkm
      simp only [Finset.mem_Ico] at hk hkm
      simp [p_range M hM k (by omega)]
    rw [hext, hfin]

/-- split_J (ℤ): Σ_{k≥7}(⌊(k+1)/2⌋−6)p_k
      = −2p_7 − 2p_8 − p_9 − p_10 + Σ_{k≥11}(⌊(k+1)/2⌋−6)p_k. -/
lemma split_J (M : SimplyCon3ConnectedMap g) (hM : IsMap M) :
    (∑ k ∈ Finset.Ico 7 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ)) =
      -2 * (M.p_i 7 : ℤ) - 2 * (M.p_i 8 : ℤ) - (M.p_i 9 : ℤ) - (M.p_i 10 : ℤ) +
      ∑ k ∈ Finset.Ico 11 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ) := by
  have hfin : (∑ k ∈ (Finset.Ico 7 11 : Finset ℕ), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ)) =
      -2 * (M.p_i 7 : ℤ) - 2 * (M.p_i 8 : ℤ) - (M.p_i 9 : ℤ) - (M.p_i 10 : ℤ) := by
    rw [show (Finset.Ico 7 11 : Finset ℕ) = {7, 8, 9, 10} from by decide,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
    push_cast; omega
  by_cases hm : 11 ≤ M.m + 1
  · rw [← Finset.sum_Ico_consecutive _ (show 7 ≤ 11 from by norm_num) hm, hfin]
  · push_neg at hm
    rw [show (Finset.Ico 11 (M.m + 1) : Finset ℕ) = ∅ from Finset.Ico_eq_empty (by omega),
        Finset.sum_empty, add_zero]
    have hext : (∑ k ∈ Finset.Ico 7 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ)) =
        ∑ k ∈ (Finset.Ico 7 11 : Finset ℕ), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ) := by
      apply Finset.sum_subset (Finset.Ico_subset_Ico_right (by omega : M.m + 1 ≤ 11))
      intro k hk hkm
      simp only [Finset.mem_Ico] at hk hkm
      simp [p_range M hM k (by omega)]
    rw [hext, hfin]

-- ── tail lemmas (k ≥ 11) ────────────────────────────────────────────────────

/-- tail_excess: Σ_{k≥11}(k−6)p_k ≥ 5·Σ_{k≥11} p_k  (k − 6 ≥ 5). -/
lemma tail_excess (M : SimplyCon3ConnectedMap g) :
    (∑ k ∈ Finset.Ico 11 (M.m + 1), ((k : ℤ) - 6) * (M.p_i k : ℤ)) ≥
      5 * ∑ k ∈ Finset.Ico 11 (M.m + 1), (M.p_i k : ℤ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk11 : (11 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk.1
  have hp : (0 : ℤ) ≤ (M.p_i k : ℤ) := by positivity
  nlinarith

/-- tail_juc_nonneg: Σ_{k≥11}(⌊(k+1)/2⌋−6)p_k ≥ 0  (⌊(k+1)/2⌋ − 6 ≥ 0). -/
lemma tail_juc_nonneg (M : SimplyCon3ConnectedMap g) :
    (∑ k ∈ Finset.Ico 11 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ)) ≥ 0 := by
  apply Finset.sum_nonneg
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk11 : (11 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk.1
  have hp : (0 : ℤ) ≤ (M.p_i k : ℤ) := by positivity
  have hco : (0 : ℤ) ≤ ((k : ℤ) + 1) / 2 - 6 := by omega
  exact mul_nonneg hco hp

/-- tail_juc_upper: Σ(k−6)p − Σ(⌊(k+1)/2⌋−6)p ≥ 5·Σ p  (⌊k/2⌋ ≥ 5). -/
lemma tail_juc_upper (M : SimplyCon3ConnectedMap g) :
    (∑ k ∈ Finset.Ico 11 (M.m + 1), ((k : ℤ) - 6) * (M.p_i k : ℤ)) -
      (∑ k ∈ Finset.Ico 11 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ)) ≥
      5 * ∑ k ∈ Finset.Ico 11 (M.m + 1), (M.p_i k : ℤ) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk11 : (11 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk.1
  have hp : (0 : ℤ) ≤ (M.p_i k : ℤ) := by positivity
  have hco : ((k : ℤ) - 6) - (((k : ℤ) + 1) / 2 - 6) ≥ 5 := by omega
  nlinarith [mul_nonneg hp (by linarith :
    (0 : ℤ) ≤ (((k : ℤ) - 6) - (((k : ℤ) + 1) / 2 - 6)) - 5)]

/-- tail_juc_half: 2·Σ(⌊(k+1)/2⌋−6)p ≥ Σ(k−6)p − 6·Σ p  (2⌊(k+1)/2⌋ ≥ k). -/
lemma tail_juc_half (M : SimplyCon3ConnectedMap g) :
    2 * (∑ k ∈ Finset.Ico 11 (M.m + 1), (((k : ℤ) + 1) / 2 - 6) * (M.p_i k : ℤ)) ≥
      (∑ k ∈ Finset.Ico 11 (M.m + 1), ((k : ℤ) - 6) * (M.p_i k : ℤ)) -
      6 * ∑ k ∈ Finset.Ico 11 (M.m + 1), (M.p_i k : ℤ) := by
  rw [Finset.mul_sum,
      show (6 : ℤ) * ∑ k ∈ Finset.Ico 11 (M.m + 1), (M.p_i k : ℤ) =
        ∑ k ∈ Finset.Ico 11 (M.m + 1), 6 * (M.p_i k : ℤ) from Finset.mul_sum _ _ _,
      ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.mem_Ico] at hk
  have hk11 : (11 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk.1
  have hp : (0 : ℤ) ≤ (M.p_i k : ℤ) := by positivity
  have hco : 2 * (((k : ℤ) + 1) / 2 - 6) - (((k : ℤ) - 6) - 6) ≥ 0 := by omega
  nlinarith [mul_nonneg hp hco]

-- ── Barnette side condition: Σ_{k≥7} p_k ≥ 3  ⇒  m ≥ 6 ──────────────────────
lemma barnette_m_ge_six (M : SimplyCon3ConnectedMap g)
    (hsum : ∑ k ∈ Finset.Ico 7 (M.m + 1), (M.p_i k : ℤ) ≥ 3) : M.m ≥ 6 := by
  by_contra h
  push_neg at h
  have hempty : (Finset.Ico 7 (M.m + 1) : Finset ℕ) = ∅ :=
    Finset.Ico_eq_empty (by omega)
  rw [hempty, Finset.sum_empty] at hsum
  norm_num at hsum

end SimplyCon3ConnectedMap
