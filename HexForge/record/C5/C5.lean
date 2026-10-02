import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C5 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 15) :
    (maps.p_i 6 : ℤ) ≥ ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) + 13 := by
  have s1 : (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) + (maps.p_i 7 : ℤ) + (maps.p_i 8 : ℤ) + (maps.p_i 9 : ℤ) + (maps.p_i 10 : ℤ) ≥ 13 := by
    by_cases hc1 : (3 : ℤ) ≤ (maps.p_i 7 : ℤ) + (maps.p_i 8 : ℤ) + (maps.p_i 9 : ℤ) + (maps.p_i 10 : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*p_7 + 1*p_8 + 1*p_9 + 1*p_10 + 1*sum_pk_after_p10 >= 3
      have s2 : -5 * ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s3 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s4 : (maps.p_i 8 : ℤ) ≥ 0 := by positivity
      have s5 : (maps.p_i 9 : ℤ) ≥ 0 := by positivity
      have s6 : (maps.p_i 10 : ℤ) ≥ 0 := by positivity
      have s7 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 15 := by exact_mod_cast h1
      have s8 : (maps.p_i 7 : ℤ) + (maps.p_i 8 : ℤ) + (maps.p_i 9 : ℤ) + (maps.p_i 10 : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) ≥ 3 := by linarith [hc1]
      have s9 : -(maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * (maps.p_i 7 : ℤ) + 2 * (maps.p_i 8 : ℤ) + 2 * (maps.p_i 9 : ℤ) + 2 * (maps.p_i 10 : ℤ) + 2 * ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by
        have hcnt := SimplyCon3ConnectedMap.split_count maps hM
        have hS3 : (3 : ℤ) ≤ (maps.p_i 7 : ℤ) + (maps.p_i 8 : ℤ) + (maps.p_i 9 : ℤ) + (maps.p_i 10 : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) := by linarith [s8]
        have hsum7 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by linarith [hS3, hcnt]
        have hm6 := SimplyCon3ConnectedMap.barnette_m_ge_six maps hsum7
        have hb := Barnette_P6Bound maps hM hm6 hsum7
        linarith [hb, hcnt]
      have s10 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - (maps.p_i 7 : ℤ) - 2 * (maps.p_i 8 : ℤ) - 3 * (maps.p_i 9 : ℤ) - 4 * (maps.p_i 10 : ℤ) - ∑ k ∈ Finset.Ico 11 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        have hw := SimplyCon3ConnectedMap.split_W maps hM
        linear_combination he + hw
      have s11 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - (maps.p_i 7 : ℤ) - (maps.p_i 8 : ℤ) - (maps.p_i 9 : ℤ) - (maps.p_i 10 : ℤ) - ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s12 : 4 * (maps.p_i 3 : ℤ) + 4 * (maps.p_i 4 : ℤ) + 4 * (maps.p_i 5 : ℤ) + 8 * (maps.p_i 6 : ℤ) + 4 * (maps.p_i 7 : ℤ) + 4 * (maps.p_i 8 : ℤ) + 4 * (maps.p_i 9 : ℤ) + 4 * (maps.p_i 10 : ℤ) ≥ 49 := by linarith [s2, s3, s4, s5, s6, s7, s8, s9, s10, s11]
      have s13 : (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) + (maps.p_i 7 : ℤ) + (maps.p_i 8 : ℤ) + (maps.p_i 9 : ℤ) + (maps.p_i 10 : ℤ) ≥ 13 := by have hr := s12; omega
      linarith [s13]
    · -- 1*p_7 + 1*p_8 + 1*p_9 + 1*p_10 + 1*sum_pk_after_p10 <= 2
      have s14 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s15 : (maps.p_i 7 : ℤ) ≥ 0 := by positivity
      have s16 : (maps.p_i 8 : ℤ) ≥ 0 := by positivity
      have s17 : (maps.p_i 9 : ℤ) ≥ 0 := by positivity
      have s18 : (maps.p_i 10 : ℤ) ≥ 0 := by positivity
      have s19 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 15 := by exact_mod_cast h1
      have s20 : -(maps.p_i 7 : ℤ) - (maps.p_i 8 : ℤ) - (maps.p_i 9 : ℤ) - (maps.p_i 10 : ℤ) - ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s21 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - (maps.p_i 7 : ℤ) - (maps.p_i 8 : ℤ) - (maps.p_i 9 : ℤ) - (maps.p_i 10 : ℤ) - ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s22 : (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) + (maps.p_i 7 : ℤ) + (maps.p_i 8 : ℤ) + (maps.p_i 9 : ℤ) + (maps.p_i 10 : ℤ) ≥ 13 := by linarith [s14, s15, s16, s17, s18, s19, s20, s21]
      linarith [s22]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + (maps.p_i 7 : ℤ) + (maps.p_i 8 : ℤ) + (maps.p_i 9 : ℤ) + (maps.p_i 10 : ℤ) + ∑ k ∈ Finset.Ico 11 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
