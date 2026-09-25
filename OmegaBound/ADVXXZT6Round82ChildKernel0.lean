import OmegaBound.ADVXXZT6Round82ChildKernel
namespace OmegaBound.ADVXXZT6Round82
def ChildShard0 : Prop := forall t : Fin 126, t.1 < 21 -> ReleasedChildLawFactsAt t
instance : Decidable ChildShard0 := by unfold ChildShard0; infer_instance
set_option maxHeartbeats 8000000 in theorem childShard0 : ChildShard0 := by native_decide
end OmegaBound.ADVXXZT6Round82
