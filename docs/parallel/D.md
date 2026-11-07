# Ordinary design parallel

[Parallel by merge](README.md) · [AD](AD.md)

Source: [utp_des_parallel.thy](../../deps/UTP-Designs/utp_des_parallel.thy).
[Shared notation](README.md#shared-notation).

## Design merge healthiness

```text
H1m M = M ∨ ¬ok
H2m M = M ;; J
H3m M ≡ M ;; II_D
HDM M = H1m (H2m M)
```

[H1m](../../deps/UTP-Designs/utp_des_parallel.thy#L18) permits any output before start. [H2m](../../deps/UTP-Designs/utp_des_parallel.thy#L24) permits termination after an accepted
divergence at the same output state. [H3m](../../deps/UTP-Designs/utp_des_parallel.thy#L30) releases the output after divergence.
The four transformers are monotone, idempotent and pairwise commuting.
They also apply to AD merges, whose prior and output alphabets differ.

## Generic Miracle zero laws

[par_by_merge_miracle](../../deps/UTP-Designs/utp_des_parallel.thy#L319) applies to arbitrary Design or AD merges:

```text
P is H1 ∧ M is H1m ⟹
  P ∥[M] Miracle = Miracle ∥[M] P = Miracle
```

Miracle is `¬ok`: it supplies no started branch observation.

## State-merge lifting

[merge_des_raw](../../deps/UTP-Designs/utp_des_parallel.thy#L336) lifts the state merge; [merge_des](../../deps/UTP-Designs/utp_des_parallel.thy#L348) completes it, and
[des_par](../../deps/UTP-Designs/utp_des_parallel.thy#L439) defines the parallel operator:

```text
merge_des_raw j ((ok,s),(okL,sL),(okR,sR),(ok',s')) =
  (ok' = (okL ∧ okR)) ∧ j(s,sL,sR,s')

merge_des j ≡ H3m (HDM (merge_des_raw j))
P ∥D[j] Q ≡ P ∥[merge_des j] Q
```

By [merge_des_expand](../../deps/UTP-Designs/utp_des_parallel.thy#L365), the completed merge accepts exactly

```text
¬ok ∨ ((∃u. j(s,sL,sR,u)) ∧
       (okL ∧ okR ⟶ ok' ∧ j(s,sL,sR,s'))).
```

Divergence releases the final observation but retains merge feasibility.
[merge_des_alt_def](../../deps/UTP-Designs/utp_des_parallel.thy#L353) gives `H1m (merge_des_raw j) ;; II_D`.
For every `j`:

| Healthiness of `merge_des j` | Lemma |
| --- | --- |
| [HDM](../../deps/UTP-Designs/utp_des_parallel.thy#L36), hence [H1m](../../deps/UTP-Designs/utp_des_parallel.thy#L18) and [H2m](../../deps/UTP-Designs/utp_des_parallel.thy#L24) | [merge_des_is_HDM](../../deps/UTP-Designs/utp_des_parallel.thy#L408) |
| [H3m](../../deps/UTP-Designs/utp_des_parallel.thy#L30) | [merge_des_is_H3m](../../deps/UTP-Designs/utp_des_parallel.thy#L412) |

## Healthiness closure

For generic `P ∥[M] Q`:

| Result | Operand premises | Merge premise | Lemma |
| --- | --- | --- | --- |
| [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10) | Both [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10) | [H1m](../../deps/UTP-Designs/utp_des_parallel.thy#L18) | [H1_par_by_merge](../../deps/UTP-Designs/utp_des_parallel.thy#L285) |
| [H2](../../deps/UTP-Designs/utp_des_healths.thy#L194) | None | [H2m](../../deps/UTP-Designs/utp_des_parallel.thy#L24) | [H2_par_by_merge](../../deps/UTP-Designs/utp_des_parallel.thy#L292) |
| [H3](../../deps/UTP-Designs/utp_des_healths.thy#L554) | None | [H3m](../../deps/UTP-Designs/utp_des_parallel.thy#L30) | [H3_par_by_merge](../../deps/UTP-Designs/utp_des_parallel.thy#L298) |
| [H](../../deps/UTP-Designs/utp_des_healths.thy#L328) | Both [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10) | [HDM](../../deps/UTP-Designs/utp_des_parallel.thy#L36) | [H_par_by_merge](../../deps/UTP-Designs/utp_des_parallel.thy#L304) |

For the completed merge, no mergeability premise is needed:

| Result of `P ∥D[j] Q` | Operand premises | Lemma |
| --- | --- | --- |
| [H3](../../deps/UTP-Designs/utp_des_healths.thy#L554) | None | [des_par_H3_closure](../../deps/UTP-Designs/utp_des_parallel.thy#L474) |
| [H](../../deps/UTP-Designs/utp_des_healths.thy#L328) | Both [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10) | [des_par_H_closure](../../deps/UTP-Designs/utp_des_parallel.thy#L465) |
| [N](../../deps/UTP-Designs/utp_des_healths.thy#L676) | Both [H1](../../deps/UTP-Designs/utp_des_healths.thy#L10) | [des_par_N_closure](../../deps/UTP-Designs/utp_des_parallel.thy#L478) |

## Algebra and zero laws

- [des_par_comm](../../deps/UTP-Designs/utp_des_parallel.thy#L543): commutativity when `j is SymMerge`; no operand premises.
- [des_par_assoc](../../deps/UTP-Designs/utp_des_parallel.thy#L549): associativity when `j is SymMerge`,
  `AssocMerge j` and `mergeable j`; no operand premises.
- [des_par_assoc_nondiv](../../deps/UTP-Designs/utp_des_parallel.thy#L580): associativity when `j is SymMerge` and
  `AssocMerge j`, for operands with `pre_D P = true`, which never diverge from a started
  observation. Completion then has no effect, so associativity follows from the uncompleted
  merge ([HDM_merge_des_raw_AssocMerge](../../deps/UTP-Designs/utp_des_parallel.thy#L424)) by
  [par_by_merge_assoc_on](../../deps/UTP/utp_concurrency.thy#L397), after establishing the guarded fold equality locally; no `mergeable` premise is needed.
- [des_par_chaos](../../deps/UTP-Designs/utp_des_parallel.thy#L519): `P ∥D[j] Chaos = Chaos ∥D[j] P = Chaos`
  when `P is H4` and `mergeable j`.
- [des_par_chaos_chaos](../../deps/UTP-Designs/utp_des_parallel.thy#L508): Chaos with Chaos is Chaos under the weaker
  premise `∀s. ∃sL sR u. j(s,sL,sR,u)`.
- [des_par_miracle](../../deps/UTP-Designs/utp_des_parallel.thy#L535): Miracle absorbs on both sides when `P is H1`,
  for arbitrary `j`.

Here Chaos is `true`; [H4](../../deps/UTP-Designs/utp_des_healths.thy#L839) means `P ;; true = true`.
A divergent branch still needs an accepted observation from the other operand
and a merge witness ([des_par_diverge](../../deps/UTP-Designs/utp_des_parallel.thy#L495)).

Associativity uses the [generic laws](README.md#generic-concurrency-laws).
Mergeability prevents an intermediate terminating pair from becoming infeasible
before meeting a divergent branch. The premises are sufficient, not proved
necessary. The file has no parallel identity theorem.

The four D/AD mapping laws are recorded once in
[AD](AD.md#ac2pd2ac-mapping-laws).
