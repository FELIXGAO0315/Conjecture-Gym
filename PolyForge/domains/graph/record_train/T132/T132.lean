import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem T132 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (G.maxDegree : ℤ) ≥ 2 * (G.minDegree : ℤ)) :
    2 * (G.edgeFinset.card : ℤ) ≥ (G.minDegree : ℤ) + 3 * (G.cliqueNum : ℤ) - 4 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    try push_cast at hw
    linarith [hw]
  have s3 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
    have hw := omega_le_maxdeg_add_one_int G
    try push_cast at hw
    linarith [hw]
  have s4 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s5 : (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn1]
  have s6 : 4 * (G.edgeFinset.card : ℤ) - 2 * (G.minDegree : ℤ) - 6 * (G.cliqueNum : ℤ) ≥ -9 := by linarith [s1, s2, s3, s4, s5]
  have s7 : 2 * (G.edgeFinset.card : ℤ) - (G.minDegree : ℤ) - 3 * (G.cliqueNum : ℤ) ≥ -4 := by have hr := s6; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s7, heq_gallai]
