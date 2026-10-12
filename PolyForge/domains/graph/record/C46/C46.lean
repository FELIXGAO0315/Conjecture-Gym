import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C46 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≥ 5) (hn2 : (G.indepNum : ℤ) ≥ 3) :
    2 * (G.chromaticNumber.toNat : ℤ) ≥ -3 * (G.indepNum : ℤ) + 13 := by
  have s1 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 3 := by linarith [hn2]
      have s4 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 15 := by linarith [s2, s3]
      linarith [s4]
    · -- 1*chi <= 2
      have s5 : (G.indepNum : ℤ) ≥ 3 := by linarith [hn2]
      have s6 : (Fintype.card V : ℤ) ≥ 5 := by linarith [hn1]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s8 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s9 : 3 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s5]) (by linarith [s8])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s10 : 6 * (G.chromaticNumber.toNat : ℤ) + 9 * (G.indepNum : ℤ) ≥ 37 := by linarith [s5, s6, s7, s9]
      have s11 : 2 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) ≥ 13 := by have hr := s10; omega
      linarith [s11]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
