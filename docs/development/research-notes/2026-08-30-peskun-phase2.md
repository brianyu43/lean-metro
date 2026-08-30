# 2026-08-30 Peskun Phase 2

## 새 이론

비음수성과 행 합을 매번 별도 가정으로 전달하던 transition 함수를
`FiniteKernel` 구조체로 묶었다.

```text
FiniteKernel.prob
FiniteKernel.nonneg
FiniteKernel.row_sum
```

Target mass `π`에 대한 detailed balance와 stationarity는 각각
`ReversibleFor`와 `StationaryFor`로 정의했다.

## 구현한 것

- `FiniteKernel`
- `FiniteKernel.ReversibleFor`
- `FiniteKernel.StationaryFor`
- reversibility에서 stationarity 도출
- `ReversibleKernel`
- `PeskunDominates`
- Peskun domination의 reflexivity와 transitivity
- generic admissible accept/reject reversible kernel
- asymmetric MH finite/reversible kernel
- `metropolisHastingsKernel_peskunDominates`

## 방향 convention

```text
PeskunDominates P₁ P₂
```

는 모든 `x ≠ y`에 대해 `P₂(x,y) ≤ P₁(x,y)`라는 뜻이다. 즉 첫 번째
인자가 더 많이 움직이는 kernel이다.

## 예제 연결

비대칭 2상태 MH kernel이 reject-all kernel을 `PeskunDominates` 관계로
지배함을 일반 정리에서 도출했다. 기존 strict inequality 예제도 유지한다.

## 다음 단계

- `π`-가중 내적
- Markov operator
- reversibility에서 self-adjointness
- Dirichlet form과 Peskun ordering
