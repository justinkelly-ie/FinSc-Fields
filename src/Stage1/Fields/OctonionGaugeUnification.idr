module Stage1.Fields.OctonionGaugeUnification

import Stage0.BoxInt
import Stage1.VexelMaxel
import Stage1.MultisetTree
import Stage1.FanoOctonion
import Stage1.TypeTheory.Staging
import Data.Vect

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
-- 2. DISCRETE GELL-MANN MATRICES AS BoxSquareMaxel 3
------------------------------------------------------------------------

||| Helper to build a 3x3 BoxSquareMaxel from a list of indexed entries ((r, c), val).
public export
makeMatrix3 : List ((Nat, Nat), Integer) -> BoxSquareMaxel 3
makeMatrix3 entries =
  let step : BoxMultisetTree Pixel -> ((Nat, Nat), Integer) -> BoxMultisetTree Pixel
      step acc ((r, c), v) =
        if v /= 0
           then setBoxTree (MkPixel r c) (intToBoxInt v) acc
           else acc
      tree = foldl step BoxLeaf entries
  in MkBoxSquareMaxel tree

||| The 8 discrete Gell-Mann matrices generating su(3) over the 3 color states (0=R, 1=G, 2=B):
||| lambda_1 = [ [0, 1, 0], [1, 0, 0], [0, 0, 0] ]
||| lambda_2 = [ [0, -1, 0], [1, 0, 0], [0, 0, 0] ]  (real skew-symmetric proxy for imaginary -i, +i)
||| lambda_3 = [ [1, 0, 0], [0, -1, 0], [0, 0, 0] ]
||| lambda_4 = [ [0, 0, 1], [0, 0, 0], [1, 0, 0] ]
||| lambda_5 = [ [0, 0, -1], [0, 0, 0], [1, 0, 0] ] (skew-symmetric proxy)
||| lambda_6 = [ [0, 0, 0], [0, 0, 1], [0, 1, 0] ]
||| lambda_7 = [ [0, 0, 0], [0, 0, -1], [0, 1, 0] ] (skew-symmetric proxy)
||| lambda_8 = [ [1, 0, 0], [0, 1, 0], [0, 0, -2] ] (unnormalized integer diagonal [1, 1, -2])
public export
gellMannMaxel : (idx : Nat) -> BoxSquareMaxel 3
gellMannMaxel 1 = makeMatrix3 [ ((0, 1), 1), ((1, 0), 1) ]
gellMannMaxel 2 = makeMatrix3 [ ((0, 1), -1), ((1, 0), 1) ]
gellMannMaxel 3 = makeMatrix3 [ ((0, 0), 1), ((1, 1), -1) ]
gellMannMaxel 4 = makeMatrix3 [ ((0, 2), 1), ((2, 0), 1) ]
gellMannMaxel 5 = makeMatrix3 [ ((0, 2), -1), ((2, 0), 1) ]
gellMannMaxel 6 = makeMatrix3 [ ((1, 2), 1), ((2, 1), 1) ]
gellMannMaxel 7 = makeMatrix3 [ ((1, 2), -1), ((2, 1), 1) ]
gellMannMaxel 8 = makeMatrix3 [ ((0, 0), 1), ((1, 1), 1), ((2, 2), -2) ]
gellMannMaxel _ = makeMatrix3 []

||| 2LTT Staged compilation of the 8 Gell-Mann generators at Level 1.
public export
stagedGellMannMaxel : (idx : Nat) -> Code (BoxSquareMaxel 3)
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
      trace3 : BoxSquareMaxel 3 -> BoxInt
      trace3 (MkBoxSquareMaxel tree) =
        lookupBoxTree (MkPixel 0 0) tree +
        lookupBoxTree (MkPixel 1 1) tree +
        lookupBoxTree (MkPixel 2 2) tree
      traces = map (\i => trace3 (gellMannMaxel i)) indices
  in all boxIsZero traces

||| Verifies that Gell-Mann lambda_3 squared is the projector onto Red and Green:
||| lambda_3^2 = diag(1, 1, 0).
public export
auditGellMannLambda3Squared : Bool
auditGellMannLambda3Squared =
  let l3 = gellMannMaxel 3
      l3_sq = mulBoxSquareMaxel l3 l3
      MkBoxSquareMaxel tree = l3_sq
      p00 = lookupBoxTree (MkPixel 0 0) tree
      p11 = lookupBoxTree (MkPixel 1 1) tree
      p22 = lookupBoxTree (MkPixel 2 2) tree
  in p00 == intToBoxInt 1 && p11 == intToBoxInt 1 && boxIsZero p22
