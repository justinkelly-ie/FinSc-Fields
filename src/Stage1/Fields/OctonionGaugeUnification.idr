module Stage1.Fields.OctonionGaugeUnification

import Stage0.BoxInt
import Stage1.Basis.Coordinate
import Stage1.MultisetTree
import Stage1.FanoOctonion
import Stage1.TypeTheory.Staging
import public Stage1.Carrier.SquareMaxel
import Stage1.Carrier.CellMultiset
import Data.Vect
import Data.List

%default total

------------------------------------------------------------------------
-- 1. FANO SU(3) COLOR DECOMPOSITION UNDER e_7 STABILIZER
------------------------------------------------------------------------

||| The 3 quark color charges of SU(3) corresponding to Fano points E1, E2, E3.
public export
data FanoColor = ColorRed | ColorGreen | ColorBlue

public export
Eq FanoColor where
  ColorRed   == ColorRed   = True
  ColorGreen == ColorGreen = True
  ColorBlue  == ColorBlue  = True
  _          == _          = False

public export
Show FanoColor where
  show ColorRed   = "Red(E1)"
  show ColorGreen = "Green(E2)"
  show ColorBlue  = "Blue(E3)"

||| Canonical embedding of quark color charge into the Fano octonionic basis.
public export
colorToFano : FanoColor -> FanoPoint
colorToFano ColorRed   = E1
colorToFano ColorGreen = E2
colorToFano ColorBlue  = E3

||| Fano points E4, E5, E6 correspond to antiquark colors (anticolor triplet 3*).
public export
anticolorToFano : FanoColor -> FanoPoint
anticolorToFano ColorRed   = E4
anticolorToFano ColorGreen = E5
anticolorToFano ColorBlue  = E6

||| SU(3) Representation sector of each Fano imaginary unit under the e_7 stabilizer:
||| - Color Triplet 3:      E1, E2, E3
||| - Anticolor Triplet 3*: E4, E5, E6
||| - Leptonic Singlet 1:   E7
public export
data Su3Sector = SectorTriplet FanoColor | SectorAntitriplet FanoColor | SectorSinglet

public export
fanoToSu3Sector : FanoPoint -> Su3Sector
fanoToSu3Sector E1 = SectorTriplet ColorRed
fanoToSu3Sector E2 = SectorTriplet ColorGreen
fanoToSu3Sector E3 = SectorTriplet ColorBlue
fanoToSu3Sector E4 = SectorAntitriplet ColorRed
fanoToSu3Sector E5 = SectorAntitriplet ColorGreen
fanoToSu3Sector E6 = SectorAntitriplet ColorBlue
fanoToSu3Sector E7 = SectorSinglet

------------------------------------------------------------------------
-- 2. DISCRETE GELL-MANN MATRICES AS ALGEBRAIC BASIS MAXELS
------------------------------------------------------------------------

||| Elementary basis unit E_{r, c} = [r, c] with unit weight 1 in dimension 3:
public export
eBasis3 : Nat -> Nat -> SquareMaxel 3
eBasis3 r c = MkSquareMaxel (singletonCell (mkPixel r c) (intToBoxInt 1))

||| Elementary basis unit with explicit signed integer weight:
public export
eBasisSigned3 : Nat -> Nat -> Integer -> SquareMaxel 3
eBasisSigned3 r c v = MkSquareMaxel (singletonCell (mkPixel r c) (intToBoxInt v))

||| Helper to build a 3x3 SquareMaxel from a list of indexed entries ((r, c), val).
public export
makeMatrix3 : List ((Nat, Nat), Integer) -> SquareMaxel 3
makeMatrix3 [] = MkSquareMaxel BoxLeaf
makeMatrix3 (((r, c), v) :: rest) =
  let MkSquareMaxel tree = makeMatrix3 rest
  in if v /= 0
       then MkSquareMaxel (setCellMultiset (mkPixel r c) (intToBoxInt v) tree)
       else MkSquareMaxel tree

||| The 8 discrete Gell-Mann matrices generating su(3) over the 3 color states (0=R, 1=G, 2=B)
||| constructed algebraically from elementary pixel basis units:
||| lambda_1 = [0, 1] + [1, 0]
||| lambda_2 = -[0, 1] + [1, 0]  (real skew-symmetric proxy for imaginary -i, +i)
||| lambda_3 = [0, 0] - [1, 1]
||| lambda_4 = [0, 2] + [2, 0]
||| lambda_5 = -[0, 2] + [2, 0] (skew-symmetric proxy)
||| lambda_6 = [1, 2] + [2, 1]
||| lambda_7 = -[1, 2] + [2, 1] (skew-symmetric proxy)
||| lambda_8 = [0, 0] + [1, 1] - 2[2, 2] (unnormalized integer diagonal [1, 1, -2])
public export
gellMannMaxel : (idx : Nat) -> SquareMaxel 3
gellMannMaxel 1 = addSquareMaxel (eBasis3 0 1) (eBasis3 1 0)
gellMannMaxel 2 = addSquareMaxel (eBasisSigned3 0 1 (-1)) (eBasis3 1 0)
gellMannMaxel 3 = addSquareMaxel (eBasis3 0 0) (eBasisSigned3 1 1 (-1))
gellMannMaxel 4 = addSquareMaxel (eBasis3 0 2) (eBasis3 2 0)
gellMannMaxel 5 = addSquareMaxel (eBasisSigned3 0 2 (-1)) (eBasis3 2 0)
gellMannMaxel 6 = addSquareMaxel (eBasis3 1 2) (eBasis3 2 1)
gellMannMaxel 7 = addSquareMaxel (eBasisSigned3 1 2 (-1)) (eBasis3 2 1)
gellMannMaxel 8 = addSquareMaxel (addSquareMaxel (eBasis3 0 0) (eBasis3 1 1)) (eBasisSigned3 2 2 (-2))
gellMannMaxel _ = MkSquareMaxel BoxLeaf

||| Lie bracket / commutator of two SquareMaxels: [A, B] = A · B - B · A.
||| Evaluated via pixel basis contraction [A, B] · [C, D] = [A, D] iff B = C.
public export
commutatorSquareMaxel : {dim : Nat} -> SquareMaxel dim -> SquareMaxel dim -> SquareMaxel dim
commutatorSquareMaxel a b =
  let ab = mulSquareMaxel a b
      ba = mulSquareMaxel b a
      negBA = scaleSquareMaxel (intToBoxInt (-1)) ba
  in addSquareMaxel ab negBA

||| Synthesizes the 8 Gell-Mann gluon matrices from the 27 Elliptic confinement tokens (3^3 = 27):
public export
synthesizeGellMannFromEllipticCount : Nat -> Vect 8 (SquareMaxel 3)
synthesizeGellMannFromEllipticCount ellCount =
  if ellCount >= 27
    then [ gellMannMaxel 1, gellMannMaxel 2, gellMannMaxel 3, gellMannMaxel 4
         , gellMannMaxel 5, gellMannMaxel 6, gellMannMaxel 7, gellMannMaxel 8
         ]
    else [ makeMatrix3 [], makeMatrix3 [], makeMatrix3 [], makeMatrix3 []
         , makeMatrix3 [], makeMatrix3 [], makeMatrix3 [], makeMatrix3 []
         ]

||| 2LTT Staged compilation of the 8 Gell-Mann generators at Level 1.
public export
stagedGellMannMaxel : (idx : Nat) -> Code (SquareMaxel 3)
stagedGellMannMaxel idx = quote (gellMannMaxel idx)

------------------------------------------------------------------------
-- 3. G_2 EXCEPTIONAL LIE ALGEBRA 14D DECOMPOSITION
------------------------------------------------------------------------

||| Dimension decomposition of G_2 = Aut(O) into SU(3) + Coset:
||| dim(G_2) = 14 = 8 (Gluons of SU(3)) + 3 (Triplet leptoquarks) + 3 (Antitriplet leptoquarks).
public export
record G2Decomposition where
  constructor MkG2Decomposition
  su3GluonDim     : Nat
  cosetTripletDim : Nat
  cosetAntiDim    : Nat
  totalG2Dim      : Nat

public export
canonicalG2Decomposition : G2Decomposition
canonicalG2Decomposition = MkG2Decomposition 8 3 3 14

||| Proof witness that 8 + 3 + 3 = 14.
public export
auditG2DimensionSum : Bool
auditG2DimensionSum =
  (canonicalG2Decomposition.su3GluonDim +
   canonicalG2Decomposition.cosetTripletDim +
   canonicalG2Decomposition.cosetAntiDim) == canonicalG2Decomposition.totalG2Dim

||| Verifies that the trace of all 8 discrete Gell-Mann matrices vanishes:
||| Tr(lambda_i) = p_00 + p_11 + p_22 = 0 for all i = 1..8.
public export
auditGellMannTraceless : Bool
auditGellMannTraceless =
  let indices : List Nat
      indices = [1, 2, 3, 4, 5, 6, 7, 8]
      trace3 : SquareMaxel 3 -> BoxInt
      trace3 (MkSquareMaxel tree) =
        lookupCellMultiset (MkPixel 0 0) tree +
        lookupCellMultiset (MkPixel 1 1) tree +
        lookupCellMultiset (MkPixel 2 2) tree
      traces = map (\i => trace3 (gellMannMaxel i)) indices
  in all boxIsZero traces

||| Verifies that Gell-Mann lambda_3 squared is the projector onto Red and Green:
||| lambda_3^2 = diag(1, 1, 0).
public export
auditGellMannLambda3Squared : Bool
auditGellMannLambda3Squared =
  let l3 = gellMannMaxel 3
      l3_sq = mulSquareMaxel l3 l3
      MkSquareMaxel tree = l3_sq
      p00 = lookupCellMultiset (MkPixel 0 0) tree
      p11 = lookupCellMultiset (MkPixel 1 1) tree
      p22 = lookupCellMultiset (MkPixel 2 2) tree
  in p00 == intToBoxInt 1 && p11 == intToBoxInt 1 && boxIsZero p22

||| Verifies that the commutator [lambda_1, lambda_2] identically equals 2 * lambda_3:
||| [lambda_1, lambda_2] = 2 * lambda_3.
public export
auditGellMannCommutator12 : Bool
auditGellMannCommutator12 =
  let c12 = commutatorSquareMaxel (gellMannMaxel 1) (gellMannMaxel 2)
      target = scaleSquareMaxel (intToBoxInt 2) (gellMannMaxel 3)
      diff = addSquareMaxel c12 (scaleSquareMaxel (intToBoxInt (-1)) target)
  in entries diff == BoxLeaf

||| Verifies that the commutator [lambda_1, lambda_3] identically equals 2 * lambda_2:
||| [lambda_1, lambda_3] = 2 * lambda_2.
public export
auditGellMannCommutator13 : Bool
auditGellMannCommutator13 =
  let c13 = commutatorSquareMaxel (gellMannMaxel 1) (gellMannMaxel 3)
      target = scaleSquareMaxel (intToBoxInt 2) (gellMannMaxel 2)
      diff = addSquareMaxel c13 (scaleSquareMaxel (intToBoxInt (-1)) target)
  in entries diff == BoxLeaf

||| Verifies that the commutator [lambda_4, lambda_5] identically equals lambda_3 + lambda_8:
||| [lambda_4, lambda_5] = lambda_3 + lambda_8.
public export
auditGellMannCommutator45 : Bool
auditGellMannCommutator45 =
  let c45 = commutatorSquareMaxel (gellMannMaxel 4) (gellMannMaxel 5)
      target = addSquareMaxel (gellMannMaxel 3) (gellMannMaxel 8)
      diff = addSquareMaxel c45 (scaleSquareMaxel (intToBoxInt (-1)) target)
  in entries diff == BoxLeaf
