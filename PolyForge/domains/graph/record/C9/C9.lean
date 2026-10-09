import Mathlib
import GraphLemmas

open SimpleGraph
open PolyForge.Graph

theorem C9 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hp1 : G.Connected) (hp2 : G.IsTree) (hn1 : -2 * (G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) ≥ 0) :
    2 * (G.maxDegree : ℤ) ≤ 2 * (G.chromaticNumber.toNat : ℤ) + (G.diam : ℤ) - 2 := by
  have s1 : (G.diam : ℤ) ≥ 0 := by positivity
  have s2 : (G.chromaticNumber.toNat : ℤ) - (G.cliqueNum : ℤ) ≥ 0 := by
    have hw := omega_le_chi_int G
    linarith [hw]
  have s3 : (G.edgeFinset.card : ℤ) - (G.maxDegree : ℤ) ≥ 0 := by
    have hw := max_le_edges_int G
    linarith [hw]
  have s4 : (G.edgeFinset.card : ℤ) ≥ 0 := by positivity
  have s5 : -(Fintype.card V : ℤ) + (G.edgeFinset.card : ℤ) = -1 := by
    have hw := tree_edges_int G hp2
    linarith [hw]
  have s6 : (Fintype.card V : ℤ) ≥ 1 := by linarith [s4, s5]
  have s7 : (G.chromaticNumber.toNat : ℤ) ≥ 1 := by
    have hw := chi_ge_one_int G (by omega)
    linarith [hw]
  have s8 : -2 * (G.edgeFinset.card : ℤ) + (G.cliqueNum : ℤ) ≥ 0 := by linarith [hn1]
  have s9 : -2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) ≥ 1 := by linarith [s2, s3, s7, s8]
  have s10 : -(G.maxDegree : ℤ) + (G.chromaticNumber.toNat : ℤ) ≥ 1 := by have hr := s9; omega
  have s11 : -2 * (G.maxDegree : ℤ) + 2 * (G.chromaticNumber.toNat : ℤ) + (G.diam : ℤ) ≥ 2 := by linarith [s1, s10]
  linarith [s11]
