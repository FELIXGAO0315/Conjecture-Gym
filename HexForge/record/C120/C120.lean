import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C120 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 5 ≥ 3) (h2 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 1) (h3 : maps.p_i 3 ≥ 2 * maps.p_i 5) :
    2 * (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 4 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + 4 := by
  have s1 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
      have s3 : (maps.p_i 5 : ℤ) ≥ 3 := by exact_mod_cast h1
      have s4 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s5 : (maps.p_i 3 : ℤ) ≥ 2 * (maps.p_i 5 : ℤ) := by exact_mod_cast h3
      have s6 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 3 := by linarith [hc1]
      have s7 : -(maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by
        have hsum7 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by linarith [s6]
        have hm6 := SimplyCon3ConnectedMap.barnette_m_ge_six maps hsum7
        have hb := Barnette_P6Bound maps hM hm6 hsum7
        linarith [hb]
      have s8 : 4 * (maps.p_i 4 : ℤ) + 4 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 7 := by linarith [s2, s3, s4, s5, s7]
      have s9 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by have hr := s8; omega
      linarith [s9]
    · -- 1*sum_pk_after_p6 <= 2
      have s10 : 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_half maps; linarith [h]
      have s11 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
      have s12 : (maps.p_i 3 : ℤ) ≥ 2 * (maps.p_i 5 : ℤ) := by exact_mod_cast h3
      have s13 : (maps.p_i 5 : ℤ) ≥ 3 := by exact_mod_cast h1
      have s14 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s15 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 1 := by exact_mod_cast h2
      have s16 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s17 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 10 := by linarith [s11, s13, s14, s15, s12, s16]
      have s18 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
        have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s17]
        have hj := (JucovicTheorem maps hM hf7).1
        linarith [hj]
      have s19 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
        have he := Juc_EulerFormula maps hM
        linear_combination he
      have s20 : 2 * ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 23 := by linarith [s10, s11, s13, s12, s18, s19, s16]
      have s21 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 12 := by have hr := s20; omega
      have s22 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s23 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 1 := by linarith [s10, s11, s13, s12, s22, s18, s19]
      have s24 : (maps.p_i 4 : ℤ) + (maps.p_i 6 : ℤ) ≥ 1 := by have hr := s23; omega
      have s25 : 38 * (maps.p_i 4 : ℤ) + 38 * (maps.p_i 6 : ℤ) + 19 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 67 := by linarith [s10, s11, s12, s21, s24, s18, s19, s16]
      have s26 : 2 * (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by have hr := s25; omega
      linarith [s26]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
