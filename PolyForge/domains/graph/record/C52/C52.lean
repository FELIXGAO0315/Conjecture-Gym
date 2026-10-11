import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C52 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (G.edgeFinset.card : ℤ) ≤ 4) :
    (G.cliqueNum : ℤ) ≤ -3 * (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) + 2 := by
  have s1 : -3 * (G.minDegree : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ -2 := by
    by_cases hc1 : (3 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 3
      have s2 : (Fintype.card V : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := bipartite_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s5 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s6 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s5]) (by linarith [s3])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s7 : 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s2, s3, s4, s6]
      have s8 : (G.indepNum : ℤ) ≥ 2 := by have hr := s7; omega
      have s9 : 2 * (G.edgeFinset.card : ℤ) - (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hw := handshake_min_int G
        try push_cast at hw
        linarith [hw]
      have s10 : -(G.edgeFinset.card : ℤ) ≥ -4 := by linarith [hn1]
      have s11 : (G.minDegree : ℤ) ≥ 0 := by positivity
      have s12 : -3 * (G.minDegree : ℤ) + (Fintype.card V : ℤ) * (G.minDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * ((G.minDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s2]) (by linarith [s11])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s13 : -3 * (G.minDegree : ℤ) ≥ -8 := by linarith [s9, s10, s12]
      have s14 : -(G.minDegree : ℤ) ≥ -2 := by have hr := s13; omega
      have s15 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s16 : -(G.cliqueNum : ℤ) ≥ -2 := by linarith [s15, s3]
      have s17 : -3 * (G.minDegree : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ -2 := by linarith [s8, s14, s16]
      linarith [s17]
    · -- 1*n <= 2
      have s18 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s19 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) ≥ 0 := by
        have hw := min_le_max_int G
        try push_cast at hw
        linarith [hw]
      have s20 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s21 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s22 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := bipartite_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s23 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := bipartite_four_mul_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s24 : -(Fintype.card V : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s25 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s26 : 3 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (2 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s25]) (by linarith [s24])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s27 : -3 * (G.minDegree : ℤ) - (G.cliqueNum : ℤ) + 3 * (G.indepNum : ℤ) ≥ -2 := by linarith [s18, s19, s20, s21, s22, s23, s24, s26]
      linarith [s27]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
