import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C188 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (Fintype.card V : ℤ) ≤ 5) :
    (G.indepNum : ℤ) ≥ 3 * (G.edgeFinset.card : ℤ) - (G.chromaticNumber.toNat : ℤ) - 13 := by
  have s1 : -4 * (G.edgeFinset.card : ℤ) + (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 0 := by
    have hw := bipartite_four_mul_edges_int G hp1
    try push_cast at hw
    linarith [hw]
  have s2 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := card_le_alpha_chi_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (Fintype.card V : ℤ) ≥ 1 := by
    have hw := card_ge_one_int (V := V)
    try push_cast at hw
    linarith [hw]
  have s4 : -(Fintype.card V : ℤ) ≥ -5 := by linarith [hn1]
  have s5 : 6 * (Fintype.card V : ℤ) - (Fintype.card V : ℤ) * (Fintype.card V : ℤ) ≥ 5 := by
    have hmul : (0 : ℤ) ≤ ((Fintype.card V : ℤ) - 1) * (5 - (Fintype.card V : ℤ)) :=
      mul_nonneg (by linarith [s3]) (by linarith [s4])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s6 : -4 * (G.edgeFinset.card : ℤ) ≥ -25 := by linarith [s1, s4, s5]
  have s7 : -(G.edgeFinset.card : ℤ) ≥ -6 := by have hr := s6; omega
  have s8 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s9 : (G.indepNum : ℤ) ≥ 1 := by
    have hw := alpha_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s10 : (G.chromaticNumber.toNat : ℤ) + 2 * (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 2 := by
    have hmul : (0 : ℤ) ≤ ((G.indepNum : ℤ) - 1) * (2 - (G.chromaticNumber.toNat : ℤ)) :=
      mul_nonneg (by linarith [s9]) (by linarith [s8])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s11 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    try push_cast at hw
    linarith [hw]
  have s12 : -2 * (G.vertexCoverNum.toNat : ℤ) ≥ -5 := by linarith [s8, s2, s4, s10, s11]
  have s13 : -(G.vertexCoverNum.toNat : ℤ) ≥ -2 := by have hr := s12; omega
  have s14 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int' G
    try push_cast at hw
    linarith [hw]
  have s15 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
  have s16 : -(G.indepNum : ℤ) ≥ -5 := by linarith [s15, s4, s11]
  have s17 : 5 * (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) - (G.indepNum : ℤ) * (G.chromaticNumber.toNat : ℤ) ≥ 5 := by
    have hmul : (0 : ℤ) ≤ (5 - (G.indepNum : ℤ)) * ((G.chromaticNumber.toNat : ℤ) - 1) :=
      mul_nonneg (by linarith [s16]) (by linarith [s14])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s18 : -90 * (G.edgeFinset.card : ℤ) + 30 * (G.chromaticNumber.toNat : ℤ) + 30 * (G.indepNum : ℤ) ≥ -413 := by linarith [s1, s2, s5, s7, s13, s17, s11]
  have s19 : -3 * (G.edgeFinset.card : ℤ) + (G.chromaticNumber.toNat : ℤ) + (G.indepNum : ℤ) ≥ -13 := by have hr := s18; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s19, heq_gallai]
