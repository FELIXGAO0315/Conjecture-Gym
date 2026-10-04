import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C186 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : 3 * maps.p_i 4 ≥ 2 * maps.p_i 3) (h2 : 2 * maps.p_i 5 ≥ 2 * maps.p_i 4) (h3 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≤ 1) :
    2 * (maps.p_i 6 : ℤ) ≥ (maps.p_i 3 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 2 := by
  have s1 : -(maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 2 := by
    by_cases hc1 : (7 : ℤ) ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*f_2 >= 7
      have s2 : 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_half maps; linarith [h]
      have s3 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s4 : 3 * (maps.p_i 4 : ℤ) ≥ 2 * (maps.p_i 3 : ℤ) := by exact_mod_cast h1
      have s5 : 2 * (maps.p_i 5 : ℤ) ≥ 2 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
      have s6 : 1 ≥ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by exact_mod_cast h3
      have s7 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 7 := by linarith [hc1]
      have s8 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
        have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s7]
        have hj := (JucovicTheorem maps hM hf7).1
        linarith [hj]
      have s9 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s10 : -5 * (maps.p_i 3 : ℤ) + 10 * (maps.p_i 5 : ℤ) + 10 * (maps.p_i 6 : ℤ) ≥ 6 := by linarith [s2, s3, s4, s5, s6, s8, s9]
      have s11 : -(maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 2 := by have hr := s10; omega
      linarith [s11]
    · -- 1*f_2 <= 6
      have s12 : -3 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_upper maps; linarith [h]
      have s13 : 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_half maps; linarith [h]
      have s14 : 3 * (maps.p_i 4 : ℤ) ≥ 2 * (maps.p_i 3 : ℤ) := by exact_mod_cast h1
      have s15 : 2 * (maps.p_i 5 : ℤ) ≥ 2 * (maps.p_i 4 : ℤ) := by exact_mod_cast h2
      have s16 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s17 : 5 * (maps.p_i 5 : ℤ) ≥ 8 := by linarith [s12, s13, s14, s15, s16]
      have s18 : (maps.p_i 5 : ℤ) ≥ 2 := by have hr := s17; omega
      have s19 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s20 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 0 := by exact Finset.sum_nonneg (fun k _ => by positivity)
      have s21 : -∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ -6 := by have hcc := hc1; omega
      have s22 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s23 : -7 * (maps.p_i 3 : ℤ) ≥ -18 := by linarith [s19, s20, s14, s15, s21, s22]
      have s24 : -(maps.p_i 3 : ℤ) ≥ -2 := by have hr := s23; omega
      have s25 : -(maps.p_i 3 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 2 := by linarith [s18, s19, s24]
      linarith [s25]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
