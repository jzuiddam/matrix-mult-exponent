import OmegaBound.ADVXXZCertSemantic

namespace OmegaBound.ADVXXZCertificateSplitData

open ADVXXZ

def resZRow40Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 1 => 23779956645500103293985052466696444860528581935443
  | 3 => 23779956645500103293985052466696444860528581935443
  | 9 => 23779761512248104741604059766208035757754402995885
  | 27 => 23779761512248104741604059766208035757754402995885
  | _ => 0

def resZRow40Dist : SplitDist 4 where
  num := resZRow40Num
  den := 95119436315496416071178224465808961236565969862656
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resZRow41Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 0 => 1
  | _ => 0

def resZRow41Dist : SplitDist 4 where
  num := resZRow41Num
  den := 1
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resZRow42Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 1 => 4503599627370481
  | 3 => 4503599627370493
  | 9 => 4503599627370490
  | 27 => 4503599627370520
  | _ => 0

def resZRow42Dist : SplitDist 4 where
  num := resZRow42Num
  den := 18014398509481984
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resZRow43Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 0 => 1
  | _ => 0

def resZRow43Dist : SplitDist 4 where
  num := resZRow43Num
  den := 1
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resZRow44Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 0 => 1
  | _ => 0

def resZRow44Dist : SplitDist 4 where
  num := resZRow44Num
  den := 1
  den_pos := by decide +kernel
  sum_num := by decide +kernel

end OmegaBound.ADVXXZCertificateSplitData
