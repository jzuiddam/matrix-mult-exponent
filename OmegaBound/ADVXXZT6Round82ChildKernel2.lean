import OmegaBound.ADVXXZT6Round82ChildKernel
namespace OmegaBound.ADVXXZT6Round82
def ChildShard2 : Prop := forall t : Fin 126, 42 <= t.1 -> t.1 < 63 -> ReleasedChildLawFactsAt t
instance : Decidable ChildShard2 := by unfold ChildShard2; infer_instance
set_option maxHeartbeats 8000000 in theorem childShard2 : ChildShard2 := by native_decide
end OmegaBound.ADVXXZT6Round82
