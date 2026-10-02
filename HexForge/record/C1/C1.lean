import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C1 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 12) :
    2 * (maps.p_i 6 : ℤ) ≥ (maps.p_i 8 : ℤ) + 2 * (maps.p_i 10 : ℤ) - ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) + 8 := by
  have s1 : (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) + (maps.p_i 7 : ℤ) + (maps.p_i 9 : ℤ) - (maps.p_i 10 : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) ≥ 8 := by
    by_cases hc1 : (3 : ℤ) ≤ (maps.p_i 7 : ℤ) + (maps.p_i 8 : ℤ) + (maps.p_i 9 : ℤ) + (maps.p_i 10 : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*p_7 + 1*p_8 + 1*p_9 + 1*p_10 + 1*sum_pk_after_p10 >= 3
      have s2 : -5 * ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s3 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s4 : (maps.p_i 7 : ℤ) ≥ 0 := by positivity
      have s5 : (maps.p_i 9 : ℤ) ≥ 0 := by positivity
      have s6 : ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) ≥ 0 := by exact Finset.sum_nonneg (fun k _ => by positivity)
      have s7 : (maps.p_i 7 : ℤ) + (maps.p_i 8 : ℤ) + (maps.p_i 9 : ℤ) + (maps.p_i 10 : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) ≥ 3 := by linarith [hc1]
      have s8 : -(maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * (maps.p_i 7 : ℤ) + 2 * (maps.p_i 8 : ℤ) + 2 * (maps.p_i 9 : ℤ) + 2 * (maps.p_i 10 : ℤ) + 2 * ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by
        have hcnt := SimplyCon3ConnectedMap.split_count maps hM
        have hS3 : (3 : ℤ) ≤ (maps.p_i 7 : ℤ) + (maps.p_i 8 : ℤ) + (maps.p_i 9 : ℤ) + (maps.p_i 10 : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) := by linarith [s7]
        have hsum7 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by linarith [hS3, hcnt]
        have hm6 := SimplyCon3ConnectedMap.barnette_m_ge_six maps hsum7
        have hb := Barnette_P6Bound maps hM hm6 hsum7
        linarith [hb, hcnt]
      have s9 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - (maps.p_i 7 : ℤ) - 2 * (maps.p_i 8 : ℤ) - 3 * (maps.p_i 9 : ℤ) - 4 * (maps.p_i 10 : ℤ) - ∑ k ∈ Finset.Ico 11 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        have hw := SimplyCon3ConnectedMap.split_W maps hM
        linear_combination he + hw
      have s10 : (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) + (maps.p_i 7 : ℤ) + (maps.p_i 9 : ℤ) - (maps.p_i 10 : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) ≥ 8 := by linarith [s2, s3, s4, s5, s6, s8, s9]
      linarith [s10]
    · -- 1*p_7 + 1*p_8 + 1*p_9 + 1*p_10 + 1*sum_pk_after_p10 <= 2
      have s11 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s12 : (maps.p_i 7 : ℤ) ≥ 0 := by positivity
      have s13 : (maps.p_i 8 : ℤ) ≥ 0 := by positivity
      have s14 : (maps.p_i 9 : ℤ) ≥ 0 := by positivity
      have s15 : ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) ≥ 0 := by exact Finset.sum_nonneg (fun k _ => by positivity)
      have s16 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 12 := by exact_mod_cast h1
      have s17 : -(maps.p_i 7 : ℤ) - (maps.p_i 8 : ℤ) - (maps.p_i 9 : ℤ) - (maps.p_i 10 : ℤ) - ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s18 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - (maps.p_i 7 : ℤ) - (maps.p_i 8 : ℤ) - (maps.p_i 9 : ℤ) - (maps.p_i 10 : ℤ) - ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s19 : (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) + (maps.p_i 7 : ℤ) + (maps.p_i 9 : ℤ) - (maps.p_i 10 : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) ≥ 8 := by linarith [s11, s12, s13, s14, s15, s16, s17, s18]
      linarith [s19]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + (maps.p_i 7 : ℤ) + (maps.p_i 8 : ℤ) + (maps.p_i 9 : ℤ) + (maps.p_i 10 : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
