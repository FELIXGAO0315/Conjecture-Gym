import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C111 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : ¬ G.IsBipartite) (hn1 : (G.chromaticNumber.toNat : ℤ) ≤ 2 * (G.maxDegree : ℤ)) :
    (G.cliqueNum : ℤ) ≤ 3 * (G.maxDegree : ℤ) - 3 := by
  have s1 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
    have hw := omega_le_maxdeg_add_one_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.chromaticNumber.toNat : ℤ) ≥ 3 := by
    have hw := not_bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s3 : 2 * (G.maxDegree : ℤ) - (G.chromaticNumber.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s4 : 2 * (G.maxDegree : ℤ) ≥ 3 := by linarith [s2, s3]
  have s5 : (G.maxDegree : ℤ) ≥ 2 := by have hr := s4; omega
  have s6 : 3 * (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ 3 := by linarith [s1, s5]
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]
