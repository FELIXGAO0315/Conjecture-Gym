import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C35 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hn1 : (G.vertexCoverNum.toNat : ℤ) ≤ (G.indepNum : ℤ)) (hn2 : (G.chromaticNumber.toNat : ℤ) ≥ (Fintype.card V : ℤ)) :
    (Fintype.card V : ℤ) ≤ (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) - 2 := by
  have s1 : -(Fintype.card V : ℤ) + (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 2 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
        have hw := chi_le_n_int G
        try push_cast at hw
        linarith [hw]
      have s3 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s4 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s5 : (G.indepNum : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s6 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s7 : -2 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) + 6 * (G.indepNum : ℤ) ≥ 3 := by linarith [s2, s3, s4, s5, s6]
      have s8 : -(Fintype.card V : ℤ) + (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 2 := by have hr := s7; omega
      linarith [s8]
    · -- 1*chi <= 2
      have s9 : (G.indepNum : ℤ) ≥ 1 := by
        have hw := alpha_ge_one_int' G
        try push_cast at hw
        linarith [hw]
      have s10 : (G.edgeFinset.card : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by
        have hw := tau_le_edges_int G
        try push_cast at hw
        linarith [hw]
      have s11 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s12 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s13 : -(Fintype.card V : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn2]
      have s14 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s15 : -(Fintype.card V : ℤ) ≥ -2 := by linarith [s13, s14]
      have s16 : 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hmul : (0 : ℤ) ≤ (2 - (Fintype.card V : ℤ)) * ((G.maxDegree : ℤ) - 0) :=
          mul_nonneg (by linarith [s15]) (by linarith [s12])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
        have hw := gallai_int G
        try push_cast at hw
        linarith [hw]
      have s18 : -(Fintype.card V : ℤ) + (G.maxDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 2 := by linarith [s9, s10, s11, s16, s17]
      linarith [s18]
  linarith [s1]
