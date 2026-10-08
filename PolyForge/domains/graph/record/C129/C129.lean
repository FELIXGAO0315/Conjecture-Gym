import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C129 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hn1 : -(G.cliqueNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0) (hn2 : (G.indepNum : ℤ) ≥ 2) :
    (Fintype.card V : ℤ) ≥ 3 := by
  have s1 : (G.indepNum : ℤ) ≥ 2 := by linarith [hn2]
  have s2 : (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by positivity
  have s3 : -(Fintype.card V : ℤ) + (G.indepNum : ℤ) + (G.vertexCoverNum.toNat : ℤ) = 0 := by
    have hw := gallai_int G
    linarith [hw]
  have s4 : (Fintype.card V : ℤ) ≥ 2 := by linarith [s1, s2, s3]
  have s5 : (G.cliqueNum : ℤ) ≥ 1 := by
    have hw := omega_ge_one_int G (by omega)
    linarith [hw]
  have s6 : -(G.cliqueNum : ℤ) + 2 * (G.vertexCoverNum.toNat : ℤ) ≥ 0 := by linarith [hn1]
  have s7 : 2 * (Fintype.card V : ℤ) ≥ 5 := by linarith [s5, s1, s6, s3]
  have s8 : (Fintype.card V : ℤ) ≥ 3 := by have hr := s7; omega
  linarith [s8]
