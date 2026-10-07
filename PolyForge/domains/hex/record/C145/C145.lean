import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C145 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 58) (h2 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≤ 4) (h3 : maps.p_i 4 ≥ 3 * maps.p_i 5) :
    2 * (maps.p_i 6 : ℤ) ≥ -(maps.p_i 4 : ℤ) + 23 := by
  have s1 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 23 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s3 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 58 := by exact_mod_cast h1
      have s4 : 4 ≥ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by exact_mod_cast h2
      have s5 : (maps.p_i 4 : ℤ) ≥ 3 * (maps.p_i 5 : ℤ) := by exact_mod_cast h3
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
      have s9 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 30 := by linarith [s2, s3, s4, s5, s7, s8]
      linarith [s9]
    · -- 1*sum_pk_after_p6 <= 2
      have s10 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 23 := by
        by_cases hc10 : (27 : ℤ) ≤ (maps.p_i 3 : ℤ)
        · -- 1*p_3 >= 27
          have s11 : 6 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_juc_half maps; linarith [h]
          have s12 : (maps.p_i 3 : ℤ) ≥ 27 := by linarith [hc10]
          have s13 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s14 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s15 : (maps.p_i 4 : ℤ) ≥ 3 * (maps.p_i 5 : ℤ) := by exact_mod_cast h3
          have s16 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 58 := by exact_mod_cast h1
          have s17 : 2 * (maps.p_i 4 : ℤ) + 3 * (maps.p_i 5 : ℤ) + 3 * (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (((k : ℤ) + 1) / 2 - 6) * (maps.p_i k : ℤ) ≥ 12 := by
            have hf7 : 7 ≤ ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k := by zify; linarith [s16]
            have hj := (JucovicTheorem maps hM hf7).1
            linarith [hj]
          have s18 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
            have he := Juc_EulerFormula maps hM
            linear_combination he
          have s19 : 11 * (maps.p_i 4 : ℤ) + 22 * (maps.p_i 6 : ℤ) ≥ 243 := by linarith [s11, s12, s13, s14, s15, s17, s18]
          have s20 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 23 := by have hr := s19; omega
          linarith [s20]
        · -- 1*p_3 <= 26
          have s21 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
          have s22 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 58 := by exact_mod_cast h1
          have s23 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
          have s24 : (maps.p_i 4 : ℤ) ≥ 3 * (maps.p_i 5 : ℤ) := by exact_mod_cast h3
          have s25 : -(maps.p_i 3 : ℤ) ≥ -26 := by have hcc := hc10; omega
          have s26 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
            have h := SimplyCon3ConnectedMap.face_split_agg maps hM
            have h2 := congrArg (Nat.cast : ℕ → ℤ) h
            push_cast at h2
            omega
          have s27 : 2 * (maps.p_i 4 : ℤ) + 4 * (maps.p_i 6 : ℤ) ≥ 45 := by linarith [s21, s22, s23, s24, s25, s26]
          have s28 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 23 := by have hr := s27; omega
          linarith [s28]
      linarith [s10]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
