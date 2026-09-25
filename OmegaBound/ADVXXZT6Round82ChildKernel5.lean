import OmegaBound.ADVXXZT6Round82ChildKernel
namespace OmegaBound.ADVXXZT6Round82
def ChildShard5 : Prop := forall t : Fin 126, 105 <= t.1 -> ReleasedChildLawFactsAt t
instance : Decidable ChildShard5 := by unfold ChildShard5; infer_instance
set_option maxHeartbeats 8000000 in theorem childShard5 : ChildShard5 := by native_decide
end OmegaBound.ADVXXZT6Round82
