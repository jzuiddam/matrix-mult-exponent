import OmegaBound.ADVXXZCertSemantic

namespace OmegaBound.ADVXXZCertificateSplitData

open ADVXXZ

def resXRow00Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 0 => 1
  | _ => 0

def resXRow00Dist : SplitDist 4 where
  num := resXRow00Num
  den := 1
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resXRow01Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 0 => 1
  | _ => 0

def resXRow01Dist : SplitDist 4 where
  num := resXRow01Num
  den := 1
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resXRow02Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 0 => 1
  | _ => 0

def resXRow02Dist : SplitDist 4 where
  num := resXRow02Num
  den := 1
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resXRow03Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 0 => 1
  | _ => 0

def resXRow03Dist : SplitDist 4 where
  num := resXRow03Num
  den := 1
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resXRow04Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 0 => 1
  | _ => 0

def resXRow04Dist : SplitDist 4 where
  num := resXRow04Num
  den := 1
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resXRow05Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 0 => 1
  | _ => 0

def resXRow05Dist : SplitDist 4 where
  num := resXRow05Num
  den := 1
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resXRow06Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 0 => 1
  | _ => 0

def resXRow06Dist : SplitDist 4 where
  num := resXRow06Num
  den := 1
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resXRow07Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 0 => 1
  | _ => 0

def resXRow07Dist : SplitDist 4 where
  num := resXRow07Num
  den := 1
  den_pos := by decide +kernel
  sum_num := by decide +kernel

end OmegaBound.ADVXXZCertificateSplitData
