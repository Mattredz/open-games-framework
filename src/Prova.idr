
%default total

infixr 9 $$

-- | Il record per contenitori dipendenti
record Container where
  constructor ($$)
  shape    : Type
  position : shape -> Type

-- | Container unitario (neutrale per il prodotto)
MkCUnit : Container
MkCUnit = () $$ \_ => ()

-- | GADT che discrimina i tre casi di prodotto di container
data ProdShape : Container -> Container -> Type where
  LeftUnit  : {c2 : Container} -> shape c2  -> ProdShape MkCUnit c2
  RightUnit : {c1 : Container} -> shape c1  -> ProdShape c1 MkCUnit
  Both      : {c1, c2 : Container} -> (shape c1 , shape c2 ) -> ProdShape c1 c2

-- | Position corrispondente a ciascun caso di ProdShape
ProdPosition : {c1, c2 : Container} -> ProdShape c1 c2 -> Type
ProdPosition {c2}      (LeftUnit x2)   = position c2  x2
ProdPosition {c1}      (RightUnit x1)  = position c1 x1
ProdPosition {c1} {c2} (Both (x1,x2)) = (position c1 x1, position c2  x2)

-- | Prodotto “intelligente”: elimina i casi unit
infixr 7 ><
(><) : Container -> Container -> Container
c1 >< c2 = ProdShape c1 c2 $$ ProdPosition

-- | Lente parametrica: da xs a yr con parametro P
record ParaLens (pq, xs, yr : Container) where
  constructor MkParaLens
  fwd : shape pq -> shape xs -> shape yr
  bwd : (p : shape pq) -> (x : shape xs)
        -> position yr (fwd p x)
        -> ( position xs x
           , position pq p )

-- | Lente dipendente semplice (nessun parametro aggiuntivo)
DepLens : Container -> Container -> Type
DepLens = ParaLens MkCUnit

-- | Composizione di due ParaLens, con smart-product sui parametri
infixr 9 >>>
(>>>)
  : {P1, P2, xs, yr, zt : Container}
  -> ParaLens P1 xs yr
  -> ParaLens P2 yr zt
  -> ParaLens (P1 >< P2) xs zt
(>>>) (MkParaLens f1 b1) (MkParaLens f2 b2) = MkParaLens fwd bwd where
  fwd : (P1 >< P2).shape -> shape xs -> zt.shape
  fwd shp x = case shp of
    LeftUnit p2     => f2 p2    (f1 () x)
    RightUnit p1    => f2 ()     (f1 p1 x)
    Both (p1,p2)    => f2 p2    (f1 p1 x)

  bwd : (pp : (P1 >< P2).shape)
      -> (x  : shape xs)
      -> (t  : zt.position (fwd pp x))
      -> ( position xs x, (P1 >< P2).position pp )
  bwd pp x t = case pp of
    LeftUnit p2       =>
      let (ypos, q2) = b2 p2 (f1 () x) t
          (xpos, _)  = b1 () x ypos
      in (xpos, q2)
    RightUnit p1      =>
      let (ypos, _)  = b2 () (f1 p1 x) t
          (xpos, q1) = b1 p1 x ypos
      in (xpos, q1)
    Both (p1, p2)     =>
      let (ypos, q2) = b2 p2 (f1 p1 x) t
          (xpos, q1) = b1 p1 x ypos
      in (xpos, (q1, q2))


-- | Esempio di container e composizione di DepLens
C1 : Container
C1 = Int $$ const Bool

C2 : Container
C2 = Char $$ const Double


C3 : Container
C3 = String $$ const Char

P1 : ParaLens C1 C2 C3
P1 = MkParaLens
  ?play
  ?coplay

P2 : DepLens C3 C2
P2 = MkParaLens
  ?playd
  ?coplayd

comp : ?
comp = P1 >>> P2