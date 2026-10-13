import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C39 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.cliqueNum : ℤ) ≤ 2 * (G.maxDegree : ℤ)) :
    (Fintype.card V : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 7 := by
  have s1 : 2 * (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by
    by_cases hc1 : (2 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 2
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.indepNum : ℤ) ≥ 2 := by have hcc := hc1; omega
      have s4 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := acyclic_chi_int G (isTree_acyclic G hp1)
        try push_cast at hw
        linarith [hw]
      have s6 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 2) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s3]) (by linarith [s5])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s7 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s8 : 2 * (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by linarith [s2, s3, s4, s6, s7]
      linarith [s8]
    · -- 1*alpha <= 1
      have s9 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
        have hw := max_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s10 : (G.cliqueNum : ℤ) ≥ 1 := by
        have hw := omega_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s12 : 2 * (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s13 : -(G.indepNum : ℤ) ≥ -1 := by have hcc := hc1; omega
      have s14 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s15 : (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hmul : (0 : ℤ) ≤ (1 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s13]) (by linarith [s14])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s16 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
        have hw := tree_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s17 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s9, s10, s11, s12, s13, s15, s16]
      have s18 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s17; omega
      have s19 : 2 * (Fintype.card V : ℤ) ≥ 3 := by linarith [s9, s10, s12, s16]
      have s20 : (Fintype.card V : ℤ) ≥ 2 := by have hr := s19; omega
      have s21 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
        have hw := acyclic_chi_int G (isTree_acyclic G hp1)
        try push_cast at hw
        linarith [hw]
      have s22 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s23 : -(G.vertexCoverNum.toNat : ℤ) ≥ -1 := by linarith [s21, s11, s15, s22]
      have s24 : 2 * (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 7 := by linarith [s18, s20, s23]
      linarith [s24]
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s1, heq_gallai, heq_tree]
