import torch

from aslmt_model_v18_algebra_multistep_64 import (
    AlgebraModelCfg,
    V18AlgebraCueOnlyBaseline,
    V18AlgebraMultistepModelA as _BaseModelA,
    V18AlgebraVisibleOnlyBaseline,
)


class V18AlgebraMultistepModelA_STZ(_BaseModelA):
    """
    Same as v18 Model A, but uses a straight-through hard mediator in the query logits
    so training-time `logits_query` matches rollout-time query behavior.
    """

    def logits_query(
        self,
        *,
        tables: torch.Tensor,
        sigma: torch.Tensor,
        base_obs: torch.Tensor,
        actions: torch.Tensor,
        responses: torch.Tensor,
        t: int,
    ) -> torch.Tensor:
        z_logits = self.z_logits(tables=tables, sigma=sigma, base_obs=base_obs, actions=actions, responses=responses, t=int(t))
        z = self._z_from_logits(z_logits)
        return self.query_from_z(z)

