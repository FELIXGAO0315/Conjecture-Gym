import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C65 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.IsBipartite) (hn1 : (G.maxDegree : ℤ) ≥ 2 * (G.minDegree : ℤ)) :
    (G.maxDegree : ℤ) ≥ (G.minDegree : ℤ) + 3 * (G.cliqueNum : ℤ) - 5 := by
  have s1 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
    have hw := omega_le_maxdeg_add_one_int G
    try push_cast at hw
    linarith [hw]
  have s3 : -(G.chromaticNumber.toNat : ℤ) ≥ -2 := by
    have hw := bipartite_chi_int G hp1
    try push_cast at hw
    linarith [hw]
  have s4 : (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) ≥ 0 := by linarith [hn1]
  have s5 : 2 * (G.maxDegree : ℤ) - 2 * (G.minDegree : ℤ) - 6 * (G.cliqueNum : ℤ) ≥ -11 := by linarith [s1, s2, s3, s4]
  have s6 : (G.maxDegree : ℤ) - (G.minDegree : ℤ) - 3 * (G.cliqueNum : ℤ) ≥ -5 := by have hr := s5; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s6, heq_gallai]
