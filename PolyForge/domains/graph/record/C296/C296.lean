import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C296 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 2) (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ (G.cliqueNum : ℤ)) :
    (Fintype.card V : ℤ) ≤ 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - 8 := by
  have s1 : 2 * (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 8 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.indepNum : ℤ)
    · -- 1*alpha >= 3
      have s2 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.indepNum : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s5 : -(G.chromaticNumber.toNat : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
      have s6 : (G.maxDegree : ℤ) = 2 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s7 : -(G.chromaticNumber.toNat : ℤ) ≥ -3 := by linarith [s4, s5, s6]
      have s8 : 3 * (G.chromaticNumber.toNat : ℤ) + 3 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 9 := by
        have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 3) * (3 - (G.chromaticNumber.toNat : ℤ)) :=
          mul_nonneg (by linarith [s3]) (by linarith [s7])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s9 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s10 : 2 * (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 9 := by linarith [s2, s8, s9]
      linarith [s10]
    · -- 1*alpha <= 2
      have s11 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
        have hw := max_lt_card_int' G
        try push_cast at hw
        linarith [hw]
      have s12 : (G.maxDegree : ℤ) = 2 := by
        have hw := regular_max_int' G hp1
        try push_cast at hw
        linarith [hw]
      have s13 : (Fintype.card V : ℤ) ≥ 3 := by linarith [s11, s12]
      have s14 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := card_le_alpha_chi_int G
        try push_cast at hw
        linarith [hw]
      have s15 : -(G.indepNum : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s16 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
        have hw := chi_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s17 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
          mul_nonneg (by linarith [s15]) (by linarith [s16])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s18 : 2 * (G.chromaticNumber.toNat : ℤ) ≥ 3 := by linarith [s11, s14, s15, s17, s12]
      have s19 : (G.chromaticNumber.toNat : ℤ) ≥ 2 := by have hr := s18; omega
      have s20 : 2 * (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 2) :=
          mul_nonneg (by linarith [s15]) (by linarith [s19])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s21 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s22 : 4 * (Fintype.card V : ℤ) + 6 * (G.chromaticNumber.toNat : ℤ) - 6 * (G.vertexCoverNum.toNat : ℤ) ≥ 15 := by linarith [s13, s14, s20, s21]
      have s23 : 2 * (Fintype.card V : ℤ) + 3 * (G.chromaticNumber.toNat : ℤ) - 3 * (G.vertexCoverNum.toNat : ℤ) ≥ 8 := by have hr := s22; omega
      linarith [s23]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s1, heq_gallai, heq_rege, heq_regx, heq_regn]
