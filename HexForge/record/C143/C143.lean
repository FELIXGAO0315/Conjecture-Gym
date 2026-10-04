import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C143 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≤ 16) (h2 : maps.p_i 4 ≥ 3) :
    (maps.p_i 6 : ℤ) ≥ (maps.p_i 3 : ℤ) - 7 := by
  have s1 : -(maps.p_i 3 : ℤ) + (maps.p_i 6 : ℤ) ≥ -7 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : (maps.p_i 4 : ℤ) ≥ 3 := by exact_mod_cast h2
      have s3 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
      have s4 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s5 : 16 ≥ ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) := by exact_mod_cast h1
      have s6 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 3 := by linarith [hc1]
      have s7 : -(maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by
        have hsum7 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by linarith [s6]
        have hm6 := SimplyCon3ConnectedMap.barnette_m_ge_six maps hsum7
        have hb := Barnette_P6Bound maps hM hm6 hsum7
        linarith [hb]
      have s8 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s9 : -3 * (maps.p_i 3 : ℤ) + 3 * (maps.p_i 6 : ℤ) ≥ -22 := by linarith [s2, s3, s4, s5, s7, s8]
      have s10 : -(maps.p_i 3 : ℤ) + (maps.p_i 6 : ℤ) ≥ -7 := by have hr := s9; omega
      linarith [s10]
    · -- 1*sum_pk_after_p6 <= 2
      have s11 : -(maps.p_i 3 : ℤ) + (maps.p_i 6 : ℤ) ≥ -7 := by
        by_cases hc11 : (7 : ℤ) ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ)
        · -- 1*f_2 >= 7
          have s12 : 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_half maps; linarith [h]
          have s13 : (maps.p_i 4 : ℤ) ≥ 3 := by exact_mod_cast h2
          have s14 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s15 : 16 ≥ ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) := by exact_mod_cast h1
          have s16 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s17 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 7 := by linarith [hc11]
          have s18 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
            have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s17]
            have hj := (JucovicTheorem maps hM hf7).1
            linarith [hj]
          have s19 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s20 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s21 : -8 * (maps.p_i 3 : ℤ) + 8 * (maps.p_i 6 : ℤ) ≥ -61 := by linarith [s12, s13, s14, s15, s16, s18, s19, s20]
          have s22 : -(maps.p_i 3 : ℤ) + (maps.p_i 6 : ℤ) ≥ -7 := by have hr := s21; omega
          linarith [s22]
        · -- 1*f_2 <= 6
          have s23 : (maps.p_i 4 : ℤ) ≥ 3 := by exact_mod_cast h2
          have s24 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
          have s25 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s26 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 0 := by exact Finset.sum_nonneg (fun k _ => by positivity)
          have s27 : -∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ -6 := by have hcc := hc11; omega
          have s28 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s29 : -(maps.p_i 3 : ℤ) + (maps.p_i 6 : ℤ) ≥ -3 := by linarith [s23, s24, s25, s26, s27, s28]
          linarith [s29]
      linarith [s11]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
