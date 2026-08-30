# 2026-08-30 Peskun Phase 3b

## 새 이론

Reversible kernel `P`의 Dirichlet form을 다음처럼 정의했다.

```text
E_P(f) = (1/2) ∑ x ∑ y π(x) P(x,y) (f(x) - f(y))²
```

대각항에서는 `f(x) - f(x) = 0`이므로 값이 사라진다. 따라서 비대각
transition을 늘리는 Peskun ordering은 각 비음수 항을 늘려 Dirichlet
form 전체를 늘린다.

## 구현한 것

- source-square 유한합 정리
- stationarity를 사용한 target-square 유한합 정리
- cross-term과 `weightedInner π f (P f)`의 동일성
- `dirichletForm_eq_weightedInner_sub`
- `dirichletForm_mono_of_peskunDominates`
- `metropolisHastings_dirichletForm_maximal`

## 핵심 연결

```text
MH accepted-move maximality
  ⇒ off-diagonal Peskun domination
  ⇒ Dirichlet form maximality
```

## 다음 단계

- `π`-평균이 0인 함수 공간
- `I - P`와 Poisson equation
- inverse quadratic form ordering
