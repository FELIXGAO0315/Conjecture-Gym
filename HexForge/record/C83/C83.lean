import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C83 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), maps.p_i k ≥ 32) (h2 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≤ 4) (h3 : 3 * maps.p_i 5 ≥ 2 * maps.p_i 3) :
    2 * (maps.p_i 6 : ℤ) ≥ -(maps.p_i 4 : ℤ) - 2 * (maps.p_i 5 : ℤ) + 24 := by
  have s1 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 24 := by
    by_cases hc1 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ)
    · -- 1*sum_pk_after_p6 >= 3
      have s2 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
      have s3 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 32 := by exact_mod_cast h1
      have s4 : 4 ≥ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by exact_mod_cast h2
      have s5 : 3 * (maps.p_i 5 : ℤ) ≥ 2 * (maps.p_i 3 : ℤ) := by exact_mod_cast h3
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
      have s9 : 11 * (maps.p_i 4 : ℤ) + 22 * (maps.p_i 5 : ℤ) + 22 * (maps.p_i 6 : ℤ) ≥ 256 := by linarith [s2, s3, s4, s5, s7, s8]
      have s10 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 24 := by have hr := s9; omega
      linarith [s10]
    · -- 1*sum_pk_after_p6 <= 2
      have s11 : (maps.p_i 4 : ℤ) ≥ 0 := by positivity
      have s12 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
      have s13 : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) ≥ 32 := by exact_mod_cast h1
      have s14 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s15 : 3 * (maps.p_i 5 : ℤ) ≥ 2 * (maps.p_i 3 : ℤ) := by exact_mod_cast h3
      have s16 : -(maps.p_i 3 : ℤ) - (maps.p_i 4 : ℤ) - (maps.p_i 5 : ℤ) - (maps.p_i 6 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = 0 := by
        have h := SimplyCon3ConnectedMap.face_split_agg maps hM
        have h2 := congrArg (Nat.cast : ℕ → ℤ) h
        push_cast at h2
        omega
      have s17 : (maps.p_i 4 : ℤ) + 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) ≥ 24 := by linarith [s11, s12, s13, s14, s15, s16]
      linarith [s17]
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s1, hFaceZ]
