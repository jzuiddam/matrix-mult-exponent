import OmegaBound.ADVXXZT6Round82ChildKernel0
import OmegaBound.ADVXXZT6Round82ChildKernel1
import OmegaBound.ADVXXZT6Round82ChildKernel2
import OmegaBound.ADVXXZT6Round82ChildKernel3
import OmegaBound.ADVXXZT6Round82ChildKernel4
import OmegaBound.ADVXXZT6Round82ChildKernel5
namespace OmegaBound.ADVXXZT6Round82
/-- All actual released child CSD rows, assembled from six `native_decide` shards. -/
theorem released_child_law_facts (t : Fin 126) : ReleasedChildLawFactsAt t := by
  by_cases h0 : t.1 < 21
  · exact childShard0 t h0
  by_cases h1 : t.1 < 42
  · exact childShard1 t (by omega) h1
  by_cases h2 : t.1 < 63
  · exact childShard2 t (by omega) h2
  by_cases h3 : t.1 < 84
  · exact childShard3 t (by omega) h3
  by_cases h4 : t.1 < 105
  · exact childShard4 t (by omega) h4
  · exact childShard5 t (by omega)
end OmegaBound.ADVXXZT6Round82
