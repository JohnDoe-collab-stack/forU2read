from __future__ import annotations

import torch
import torch.nn as nn
import torch.nn.functional as F


class _CategoricalOps:
    @staticmethod
    def greedy_action(logits: torch.Tensor) -> torch.Tensor:
        return logits.argmax(dim=-1)

    @staticmethod
    def dist_logprob_entropy(logits: torch.Tensor, action: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
        logp = F.log_softmax(logits, dim=-1).gather(dim=-1, index=action.unsqueeze(-1)).squeeze(-1)
        p = F.softmax(logits, dim=-1)
        ent = -(p * F.log_softmax(logits, dim=-1)).sum(dim=-1)
        return logp, ent


class LawV3MemoryPolicyV1(nn.Module):
    """
    State-locked policy:
    - internal memory z (GRU)
    - heads read only z (no direct visible bypass)
    """

    def __init__(self, *, vocab_size: int, n_queries: int, d_embed: int = 64, d_mem: int = 128):
        super().__init__()
        self.vocab_size = int(vocab_size)
        self.n_queries = int(n_queries)
        self.d_embed = int(d_embed)
        self.d_mem = int(d_mem)

        self.emb = nn.Embedding(self.vocab_size, self.d_embed)
        self.gru = nn.GRUCell(self.d_embed, self.d_mem)

        self.query_head = nn.Sequential(
            nn.Linear(self.d_mem, self.d_mem),
            nn.Tanh(),
            nn.Linear(self.d_mem, self.n_queries),
        )
        self.out_head = nn.Sequential(
            nn.Linear(self.d_mem, self.d_mem),
            nn.Tanh(),
            nn.Linear(self.d_mem, 2),
        )
        self.value_head = nn.Sequential(
            nn.Linear(self.d_mem, self.d_mem),
            nn.Tanh(),
            nn.Linear(self.d_mem, 1),
        )

    def init_mem(self, batch_size: int, device: str) -> torch.Tensor:
        return torch.zeros((int(batch_size), self.d_mem), device=device)

    def step_mem(self, mem: torch.Tensor, tok: torch.Tensor) -> torch.Tensor:
        x = self.emb(tok)
        return self.gru(x, mem)

    def logits_query(self, mem: torch.Tensor) -> torch.Tensor:
        return self.query_head(mem)

    def logits_out(self, mem: torch.Tensor) -> torch.Tensor:
        return self.out_head(mem)

    def value(self, mem: torch.Tensor) -> torch.Tensor:
        return self.value_head(mem).squeeze(-1)

    def greedy_action(self, logits: torch.Tensor) -> torch.Tensor:
        return _CategoricalOps.greedy_action(logits)

    def dist_logprob_entropy(self, logits: torch.Tensor, action: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
        return _CategoricalOps.dist_logprob_entropy(logits, action)


class LawV3VisibleOnlyPolicyV1(nn.Module):
    """
    Visible-only baseline:
    - no memory
    - heads read only the current token embedding
    """

    def __init__(self, *, vocab_size: int, n_queries: int, d_embed: int = 64):
        super().__init__()
        self.vocab_size = int(vocab_size)
        self.n_queries = int(n_queries)
        self.d_embed = int(d_embed)

        self.emb = nn.Embedding(self.vocab_size, self.d_embed)
        self.query_head = nn.Sequential(
            nn.Linear(self.d_embed, self.d_embed),
            nn.Tanh(),
            nn.Linear(self.d_embed, self.n_queries),
        )
        self.out_head = nn.Sequential(
            nn.Linear(self.d_embed, self.d_embed),
            nn.Tanh(),
            nn.Linear(self.d_embed, 2),
        )
        self.value_head = nn.Sequential(
            nn.Linear(self.d_embed, self.d_embed),
            nn.Tanh(),
            nn.Linear(self.d_embed, 1),
        )

    def logits_query(self, tok: torch.Tensor) -> torch.Tensor:
        x = self.emb(tok)
        return self.query_head(x)

    def logits_out(self, tok: torch.Tensor) -> torch.Tensor:
        x = self.emb(tok)
        return self.out_head(x)

    def value(self, tok: torch.Tensor) -> torch.Tensor:
        x = self.emb(tok)
        return self.value_head(x).squeeze(-1)

    def greedy_action(self, logits: torch.Tensor) -> torch.Tensor:
        return _CategoricalOps.greedy_action(logits)

    def dist_logprob_entropy(self, logits: torch.Tensor, action: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor]:
        return _CategoricalOps.dist_logprob_entropy(logits, action)

