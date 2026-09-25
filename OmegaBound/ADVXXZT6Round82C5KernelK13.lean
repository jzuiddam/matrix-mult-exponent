import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 13 of 21: parents 98 <= t < 102 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK13 : Prop := forall t : Fin 126, 98 <= t.1 -> t.1 < 102 -> ClearedC5At t
instance : Decidable C5ShardK13 := by unfold C5ShardK13; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK13 : C5ShardK13 := by native_decide
end OmegaBound.ADVXXZT6Round82
