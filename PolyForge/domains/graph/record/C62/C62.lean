import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C62 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (Fintype.card V : ℤ) ≤ 2 * (G.cliqueNum : ℤ)) (hn2 : (G.edgeFinset.card : ℤ) ≥ 1) :
    (G.cliqueNum : ℤ) ≤ 3 * (Fintype.card V : ℤ) - 4 := by
  have s1 : 3 * (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 4 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s5 : 3 * (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 6 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : (G.edgeFinset.card : ℤ) ≥ 1 := by linarith [hn2]
      have s7 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := two_mul_edges_le_card_sq_sub_card_int G
        try push_cast at hw
        linarith [hw]
      have s8 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s9 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s10 : -(Fintype.card V : ℤ) + 2 * (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s11 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s12 : -(Fintype.card V : ℤ) ≥ -4 := by linarith [s9, s10, s11]
      have s13 : 5 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (4 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s8]) (by linarith [s12])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s14 : 2 * (Fintype.card V : ℤ) ≥ 3 := by linarith [s6, s7, s13]
      have s15 : (Fintype.card V : ℤ) ≥ 2 := by have hr := s14; omega
      have s16 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s9, s11]
      have s17 : 3 * (Fintype.card V : ℤ) - (G.cliqueNum : ℤ) ≥ 4 := by linarith [s15, s16]
      linarith [s17]
  linarith [s1]
