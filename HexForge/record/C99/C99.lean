import Mathlib
import Inventory
import HexLemmas

open Finset

theorem C99 (maps : SimplyCon3ConnectedMap 0) (hM : IsMap maps) (h1 : maps.p_i 3 ≤ 4) (h2 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), maps.p_i k ≥ 3) (h3 : maps.p_i 4 ≤ 4) :
    2 * (maps.p_i 6 : ℤ) ≥ -2 * (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + 4 := by
  have s1 : -∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) ≥ 0 := by have h := SimplyCon3ConnectedMap.tail_excess maps; linarith [h]
  have s2 : (maps.p_i 5 : ℤ) ≥ 0 := by positivity
  have s3 : (maps.p_i 6 : ℤ) ≥ 0 := by positivity
  have s4 : 4 ≥ (maps.p_i 4 : ℤ) := by exact_mod_cast h3
  have s5 : ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 3 := by exact_mod_cast h2
  have s6 : -(maps.p_i 3 : ℤ) + (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) + 2 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by
    have hsum7 : (3 : ℤ) ≤ ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by linarith [s5]
    have hm6 := SimplyCon3ConnectedMap.barnette_m_ge_six maps hsum7
    have hb := Barnette_P6Bound maps hM hm6 hsum7
    linarith [hb]
  have s7 : 3 * (maps.p_i 3 : ℤ) + 2 * (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) - ∑ k ∈ Finset.Ico 7 (maps.m + 1), ((k : ℤ) - 6) * (maps.p_i k : ℤ) = 12 := by
    have he := Juc_EulerFormula maps hM
    linear_combination he
  have s8 : 10 * (maps.p_i 5 : ℤ) + 10 * (maps.p_i 6 : ℤ) + 5 * ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 16 := by linarith [s1, s2, s3, s4, s6, s7]
  have s9 : 2 * (maps.p_i 5 : ℤ) + 2 * (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) ≥ 4 := by have hr := s8; omega
  have hFaceZ : ∑ k ∈ Finset.Ico 3 (maps.m + 1), (maps.p_i k : ℤ) = (maps.p_i 3 : ℤ) + (maps.p_i 4 : ℤ) + (maps.p_i 5 : ℤ) + (maps.p_i 6 : ℤ) + ∑ k ∈ Finset.Ico 7 (maps.m + 1), (maps.p_i k : ℤ) := by
    have h := SimplyCon3ConnectedMap.face_split_agg maps hM
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h
    push_cast at h2
    omega
  linarith [s9, hFaceZ]
