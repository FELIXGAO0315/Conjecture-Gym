import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C257 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (G.maxDegree : ℤ) ≤ (G.cliqueNum : ℤ)) :
    (G.edgeFinset.card : ℤ) ≤ (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) - 3 := by
  have s1 : -(G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by
    by_cases hc1 : (2 : ℤ) ≤ (Fintype.card V : ℤ)
    · -- 1*n >= 2
      have s2 : (Fintype.card V : ℤ) ≥ 2 := by have hcc := hc1; omega
      have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := bipartite_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s4 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s7 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s6]) (by linarith [s3])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s8 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s9 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s10 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s8, s3, s9]
      have s11 : 2 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * (2 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s2]) (by linarith [s10])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s12 : -(G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by linarith [s2, s3, s4, s5, s7, s11]
      linarith [s12]
    · -- 1*n <= 1
      have s13 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s14 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s15 : -(Fintype.card V : ℤ) - 2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
        have hw := two_mul_edges_le_card_sq_sub_card_int G
        try push_cast at hw
        linarith [hw]
      have s16 : -(Fintype.card V : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s17 : (Fintype.card V : ℤ) ≥ 1 := by
        have hw := card_ge_one_int (V := V)
        try push_cast at hw
        linarith [hw]
      have s18 : 2 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (1 - (Fintype.card V : ℤ)) :=
          mul_nonneg (by linarith [s17]) (by linarith [s16])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s19 : -(G.edgeFinset.card : ℤ) + (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 3 := by linarith [s13, s14, s15, s16, s18]
      linarith [s19]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
