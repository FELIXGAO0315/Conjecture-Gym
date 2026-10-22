import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T253 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsTree) (hn1 : (G.maxDegree : ℤ) ≥ 2 * (G.minDegree : ℤ)) :
    2 * (Fintype.card V : ℤ) ≥ 3 * (G.minDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) - 1 := by
  have s1 : (Fintype.card V : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by
    have hw := chi_le_n_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (Fintype.card V : ℤ) - (G.maxDegree : ℤ) ≥ 1 := by
    have hw := max_lt_card_int' G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := acyclic_chi_int G (isTree_acyclic G hp1)
    try push_cast at hw
    linarith [hw]
  have s4 : (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : 4 * (Fintype.card V : ℤ) - 6 * (G.minDegree : ℤ) - 4 * (G.chromaticNumber.toNat : ℤ) ≥ -3 := by linarith [s1, s2, s3, s4]
  have s6 : 2 * (Fintype.card V : ℤ) - 3 * (G.minDegree : ℤ) - 2 * (G.chromaticNumber.toNat : ℤ) ≥ -1 := by have hr := s5; omega
  have heq_gallai := gallai_int G
  have heq_tree := tree_edges_int G hp1
  try push_cast at heq_gallai heq_tree
  linarith [s6, heq_gallai, heq_tree]
