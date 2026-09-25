import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 2 of 21: parents 34 <= t < 43 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK2 : Prop := forall t : Fin 126, 34 <= t.1 -> t.1 < 43 -> ClearedC5At t
instance : Decidable C5ShardK2 := by unfold C5ShardK2; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK2 : C5ShardK2 := by native_decide
end OmegaBound.ADVXXZT6Round82
