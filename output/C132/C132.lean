import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C132 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : (G.maxDegree : ℤ) ≥ 4) (hn2 : (G.cliqueNum : ℤ) ≤ 2 * (G.indepNum : ℤ)) :
    (G.maxDegree : ℤ) ≥ (G.cliqueNum : ℤ) - (G.indepNum : ℤ) + 2 := by
  have s1 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) ≥ -1 := by
    have hw := omega_le_maxdeg_add_one_int G
    try push_cast at hw
    linarith [hw]
  have s2 : (G.maxDegree : ℤ) ≥ 4 := by linarith [hn1]
  have s3 : -(G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 0 := by linarith [hn2]
  have s4 : 2 * (G.maxDegree : ℤ) - 2 * (G.cliqueNum : ℤ) + 2 * (G.indepNum : ℤ) ≥ 3 := by linarith [s1, s2, s3]
  have s5 : (G.maxDegree : ℤ) - (G.cliqueNum : ℤ) + (G.indepNum : ℤ) ≥ 2 := by have hr := s4; omega
  have heq_gallai := gallai_int G
  try push_cast at heq_gallai
  linarith [s5, heq_gallai]
