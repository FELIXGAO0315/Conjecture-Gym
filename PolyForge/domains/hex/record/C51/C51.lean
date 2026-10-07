import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C51 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : 2 * maps.p_i 3 ≥ 3 * maps.p_i 5) :
    (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 3 : ℤ) - 2 * (maps.p_i 4 : ℤ) + 8 := by
  have s1 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by
    by_cases hc1 : (4 : ℤ) ≤ (maps.p_i 3 : ℤ)
    · -- 1*p_3 >= 4
      have s2 : (maps.p_i 3 : ℤ) ≥ 4 := by linarith [hc1]
      have s3 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
      have s4 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s5 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*p_3 <= 3
      have s6 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
      have s7 : 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_lower maps; linarith [h]
      have s8 : -3 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_upper maps; linarith [h]
      have s9 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 0 := by exact Finset.sum_nonneg (fun k _ => by positivity)
      have s10 : 2 * (maps.p_i 3 : ℤ) ≥ 3 * (maps.p_i 5 : ℤ) := by exact_mod_cast h1
      have s11 : -(maps.p_i 3 : ℤ) ≥ -3 := by have hcc := hc1; omega
      have s12 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s13 : 2 * (maps.p_i 4 : ℤ) ≥ 1 := by linarith [s7, s8, s9, s10, s11, s12]
      have s14 : (maps.p_i 4 : ℤ) ≥ 1 := by have hr := s13; omega
      have s15 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s16 : 22 * (maps.p_i 3 : ℤ) + 22 * (maps.p_i 4 : ℤ) + 11 * (maps.p_i 6 : ℤ) ≥ 82 := by linarith [s6, s14, s15, s9, s10, s12]
      have s17 : 2 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 8 := by have hr := s16; omega
      linarith [s17]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
