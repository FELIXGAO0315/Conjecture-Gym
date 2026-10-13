import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C42 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hn1 : (G.chromaticNumber.toNat : ℤ) ≥ (G.maxDegree : ℤ)) (hn2 : (G.radius.toNat : ℤ) ≥ 1) :
    2 * (G.cliqueNum : ℤ) ≤ 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 3 := by
  have s1 : 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 3 := by
    by_cases hc1 : (3 : ℤ) ≤ (G.chromaticNumber.toNat : ℤ)
    · -- 1*chi >= 3
      have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by have hcc := hc1; omega
      have s3 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
        have hw := omega_le_maxdeg_add_one_int G
        try push_cast at hw
        linarith [hw]
      have s4 : (G.maxDegree : ℤ) ≥ 0 := by positivity
      have s5 : 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 4 := by linarith [s2, s3, s4]
      linarith [s5]
    · -- 1*chi <= 2
      have s6 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
        have hw := omega_le_chi_int G
        try push_cast at hw
        linarith [hw]
      have s7 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) ≥ -1 := by
        have hw := connected_edges_int G hp1
        try push_cast at hw
        linarith [hw]
      have s8 : -2 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 0 := by
        have hw := handshake_max_int G
        try push_cast at hw
        linarith [hw]
      have s9 : (G.diam : ℤ) - (G.radius.toNat : ℤ) ≥ 0 := by
        have hw := radius_le_diam_int G hp1
        try push_cast at hw
        linarith [hw]
      have s10 : (Fintype.card V : ℤ) - (G.diam : ℤ) ≥ 1 := by
        have hw := diam_le_card_sub_one_int G hp1
        try push_cast at hw
        linarith [hw]
      have s11 : (G.radius.toNat : ℤ) ≥ 1 := by linarith [hn2]
      have s12 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s9, s10, s11]
      have s13 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
      have s14 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by have hcc := hc1; omega
      have s15 : -(G.maxDegree : ℤ) ≥ -2 := by linarith [s13, s14]
      have s16 : 2 * (Fintype.card V : ℤ) + 2 * (G.maxDegree : ℤ) - (Fintype.card V : ℤ) * (G.maxDegree : ℤ) ≥ 4 := by
        have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 2) * (2 - (G.maxDegree : ℤ)) :=
          mul_nonneg (by linarith [s12]) (by linarith [s15])
        ring_nf at hmul ⊢
        linarith [hmul]
      have s17 : 3 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 2 * (G.cliqueNum : ℤ) ≥ 3 := by linarith [s6, s7, s8, s16]
      linarith [s17]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s1, heq_gallai]
