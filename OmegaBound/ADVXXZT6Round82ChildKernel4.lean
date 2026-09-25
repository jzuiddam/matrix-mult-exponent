import OmegaBound.ADVXXZT6Round82ChildKernel
namespace OmegaBound.ADVXXZT6Round82
def ChildShard4 : Prop := forall t : Fin 126, 84 <= t.1 -> t.1 < 105 -> ReleasedChildLawFactsAt t
instance : Decidable ChildShard4 := by unfold ChildShard4; infer_instance
set_option maxHeartbeats 8000000 in theorem childShard4 : ChildShard4 := by native_decide
end OmegaBound.ADVXXZT6Round82
