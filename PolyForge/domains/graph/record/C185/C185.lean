import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C185 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsRegularOfDegree 2) (hn1 : (G.indepNum : ℤ) ≤ 2) :
    (G.vertexCoverNum.toNat : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ) - 2 := by
  have s1 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.indepNum : ℤ) ≥ -2 := by linarith [hn1]
  have s4 : 2 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ (2 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
      mul_nonneg (by linarith [s3]) (by linarith [s2])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s5 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s6 : (G.maxDegree : ℤ) = 2 := by
    have hw := regular_max_int' G hp1
    try push_cast at hw
    linarith [hw]
  have s7 : (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - (G.vertexCoverNum.toNat : ℤ) ≥ 4 := by linarith [s1, s4, s5, s6]
  have heq_gallai := gallai_int G
  have heq_rege := regular_edges_int G hp1
  have heq_regx := regular_max_int' G hp1
  have heq_regn := regular_min_int' G hp1
  try push_cast at heq_gallai heq_rege heq_regx heq_regn
  linarith [s7, heq_gallai, heq_rege, heq_regx, heq_regn]
