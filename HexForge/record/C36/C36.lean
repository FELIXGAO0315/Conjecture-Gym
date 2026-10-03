import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C36 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 4 = 0) (h2 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≤ 3) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 5 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - 1 := by
  have s1 : 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -1 := by
    by_cases hc1 : (7 : ℤ) ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*f_2 >= 7
      have s2 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
      have s3 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
      have s4 : 3 ≥ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by exact_mod_cast h2
      have s5 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 7 := by linarith [hc1]
      have s6 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
        have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s5]
        have hj := (JucovicTheorem maps hM hf7).1
        linarith [hj]
      have s7 : (maps.p_i 4 : ℤ) = 0 := by exact_mod_cast h1
      have s8 : 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -1 := by linarith [s2, s3, s4, s6, s7]
      linarith [s8]
    · -- 1*f_2 <= 6
      have s9 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s10 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
      have s11 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
      have s12 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s13 : -∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ -6 := by have hcc := hc1; omega
      have s14 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s15 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s16 : 4 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) - 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -3 := by linarith [s9, s10, s11, s12, s13, s14, s15]
      have s17 : 2 * (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -1 := by have hr := s16; omega
      linarith [s17]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
