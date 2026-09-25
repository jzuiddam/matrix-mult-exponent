import OmegaBound.ADVXXZT6Round82ChildKernel
namespace OmegaBound.ADVXXZT6Round82
def ChildShard3 : Prop := forall t : Fin 126, 63 <= t.1 -> t.1 < 84 -> ReleasedChildLawFactsAt t
instance : Decidable ChildShard3 := by unfold ChildShard3; infer_instance
set_option maxHeartbeats 8000000 in theorem childShard3 : ChildShard3 := by native_decide
end OmegaBound.ADVXXZT6Round82
