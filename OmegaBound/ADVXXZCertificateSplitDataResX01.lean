import OmegaBound.ADVXXZCertSemantic

namespace OmegaBound.ADVXXZCertificateSplitData

open ADVXXZ

def resXRow08Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 0 => 1
  | _ => 0

def resXRow08Dist : SplitDist 4 where
  num := resXRow08Num
  den := 1
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resXRow09Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 1 => 2251799813685251
  | 3 => 2251799813685252
  | 9 => 2251799813685240
  | 27 => 2251799813685249
  | _ => 0

def resXRow09Dist : SplitDist 4 where
  num := resXRow09Num
  den := 9007199254740992
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resXRow10Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 1 => 47568996810247985865645965775433079514016489973279
  | 3 => 47568996810247985865645965775433079514016489973279
  | 9 => 47567188763651081162307867372778987520859780897249
  | 27 => 47567188763651081162307867372778987520859780897249
  | _ => 0

def resXRow10Dist : SplitDist 4 where
  num := resXRow10Num
  den := 190272371147798134055907666296424134069752541741056
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resXRow11Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 1 => 348977504172911798585334944003787824887782476698939
  | 3 => 348977504172911798585334944003787824887782476698939
  | 9 => 348977501146813786469656256720103194536624957336261
  | 27 => 348977501146813786469656256720103194536624957336261
  | _ => 0

def resXRow11Dist : SplitDist 4 where
  num := resXRow11Num
  den := 1395910010639451170109982401447782038848814868070400
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resXRow12Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 1 => 26755747407530662398794805023654494430162706296607601
  | 3 => 26755747407530662398794805023654494430162706296607601
  | 9 => 26755745979336253384533016564398104910663163047439503
  | 27 => 26755745979336253384533016564398104910663163047439503
  | _ => 0

def resXRow12Dist : SplitDist 4 where
  num := resXRow12Num
  den := 107022986773733831566655643176105198681651738688094208
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resXRow13Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 1 => 107023001242342693161459257474055625128056159190792935
  | 3 => 107023001242342693161459257474055625128056159190792935
  | 9 => 107023009817624551874512982645384414927430346648438041
  | 27 => 107023009817624551874512982645384414927430346648438041
  | _ => 0

def resXRow13Dist : SplitDist 4 where
  num := resXRow13Num
  den := 428092022119934490071944480238880080110973011678461952
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resXRow14Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 1 => 1395918256007037414201689229508866590172357060688469
  | 3 => 1395918256007037414201689229508866590172357060688469
  | 9 => 1395918258907090451684173548251782680614557554869675
  | 27 => 1395918258907090451684173548251782680614557554869675
  | _ => 0

def resXRow14Dist : SplitDist 4 where
  num := resXRow14Num
  den := 5583673029828255731771725555521298541573829231116288
  den_pos := by decide +kernel
  sum_num := by decide +kernel

def resXRow15Num (c : Chunk 4) : ℕ :=
  match (ADVXXZCertSemantic.chunkIndex c).1 with
  | 1 => 47571530724897172841297451385336745371120635763061
  | 3 => 47571530724897172841297451385336745371120635763061
  | 9 => 47538117820013022558757790307474970542557660685963
  | 27 => 47538117820013022558757790307474970542557660685963
  | _ => 0

def resXRow15Dist : SplitDist 4 where
  num := resXRow15Num
  den := 190219297089820390800110483385623431827356592898048
  den_pos := by decide +kernel
  sum_num := by decide +kernel

end OmegaBound.ADVXXZCertificateSplitData
