import OmegaBound.ADVXXZCertSemantic

namespace OmegaBound.ADVXXZCertificateSplitData

open ADVXXZ

def resYRow40Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 1 => 15853094851867649798565100319182061203885536597369
  | 3 => 15853094851867649798565100319182061203885536597369
  | 9 => 15853383919964488891827641169420925874969786690183
  | 27 => 15853383919964488891827641169420925874969786690183
  | _ => 0

def resYRow40Dist : SplitDist 4 where
  num := resYRow40Num
  den := 63412957543664277380785482977205974157710646575104
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resYRow41Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 2 => 232967450667180411190304910839823
  | 4 => 5170539905967178610740993337080292
  | 6 => 232967450786610882117735068862415
  | 10 => 5136554309373001378536802312089536
  | 12 => 5136554306644392499299638916985529
  | 18 => 232967454247225519328728270101055
  | 28 => 5136554309840820032285403652455800
  | 30 => 5136554311428757822014690759766192
  | 36 => 5170523140180587854516290478907000
  | 54 => 232967447450602194402035274130662
  | _ => 0

def resYRow41Dist : SplitDist 4 where
  num := resYRow41Num
  den := 31819150086586357204432622981218304
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resYRow42Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 0 => 1
  | _ => 0

def resYRow42Dist : SplitDist 4 where
  num := resYRow42Num
  den := 1
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resYRow43Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 1 => 4503599627370481
  | 3 => 4503599627370493
  | 9 => 4503599627370490
  | 27 => 4503599627370520
  | _ => 0

def resYRow43Dist : SplitDist 4 where
  num := resYRow43Num
  den := 18014398509481984
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resYRow44Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 0 => 1
  | _ => 0

def resYRow44Dist : SplitDist 4 where
  num := resYRow44Num
  den := 1
  den_pos := by decide +kernel
  sum_num := by decide +kernel

end OmegaBound.ADVXXZCertificateSplitData
