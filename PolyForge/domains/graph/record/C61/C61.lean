import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C61 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : 2 ≤ Fintype.card V) (hp2 : G.IsTree) (hn1 : (G.maxDegree : ℤ) ≥ 2) :
    (G.minDegree : ℤ) ≤ -(G.edgeFinset.card : ℤ) + 3 * (G.indepNum : ℤ) - 2 := by
  have s1 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s2 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G (isTree_acyclic G hp2)
    try push_cast at hw
    linarith [hw]
  have s3 : (G.maxDegree : ℤ) ≥ 2 := by linarith [hn1]
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
      mul_nonneg (by linarith [s5]) (by linarith [s2])
    ring_nf at hmul ⊢
    linarith [hmul]
  have s7 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp2
    try push_cast at hw
    linarith [hw]
  have s8 : (G.minDegree : ℤ) = 1 := by
    have hw := tree_min_deg_int G hp2 hp1
    try push_cast at hw
    linarith [hw]
  have s9 : -2 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) + 6 * (G.indepNum : ℤ) ≥ 3 := by linarith [s1, s2, s3, s4, s6, s7, s8]
  have s10 : -(G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) + 3 * (G.indepNum : ℤ) ≥ 2 := by have hr := s9; omega
  linarith [s10]
