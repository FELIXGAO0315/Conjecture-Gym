import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C75 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.cliqueNum : ℤ) ≥ (G.maxDegree : ℤ)) :
    (G.maxDegree : ℤ) ≥ -(G.indepNum : ℤ) + 3 := by
  have s1 : (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.cliqueNum : ℤ)
    · -- 1*omega >= 3
      have s2 : (G.cliqueNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s6 : (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by linarith [s2, s3, s4, s5]
      linarith [s6]
    · -- 1*omega <= 2
      have s7 : (Fintype.card V : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 1 := by
        have hw := tau_le_card_sub_one_int' G
        try push_cast at hw
        linarith [hw]
      have s8 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s9 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s10 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s11 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
        have hw := not_bipartite_chi_int G hp1
        try push_cast at hw
        linarith [hw]
      have s12 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s10, s11]
      have s13 : -(G.maxDegree : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s14 : -(G.cliqueNum : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s15 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s13, s14]
      have s16 : 2 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 6 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 3) * (2 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s12]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : 3 * (Fintype.card V : ℤ) + 3 * (G.maxDegree : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by linarith [s7, s8, s9, s16]
      have s18 : (Fintype.card V : ℤ) + (G.maxDegree : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 3 := by have hr := s17; omega
      linarith [s18]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
