import OmegaBound.ADVXXZT6Round82C5Kernel
namespace OmegaBound.ADVXXZT6Round82
/-- Equal-cost C5 shard 18 of 21: parents 117 <= t < 120 (emitted by `release/emitters/emit_c5_reshard.py`). -/
def C5ShardK18 : Prop := forall t : Fin 126, 117 <= t.1 -> t.1 < 120 -> ClearedC5At t
instance : Decidable C5ShardK18 := by unfold C5ShardK18; infer_instance
set_option maxHeartbeats 8000000 in theorem c5ShardK18 : C5ShardK18 := by native_decide
end OmegaBound.ADVXXZT6Round82
