import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 9 of 21: parents 80 <= t < 85 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK9 : Prop := forall t : Fin 126, 80 <= t.1 -> t.1 < 85 -> ClearedC5At t
instance : Decidable C5ShardK9 := by unfold C5ShardK9; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK9 : C5ShardK9 := by native_decide
end OmegaBound.ADVXXZT6Round82
