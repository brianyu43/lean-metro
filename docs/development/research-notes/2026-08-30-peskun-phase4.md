# 2026-08-30 Peskun Phase 4

## 새 이론

Poisson equation은 다음 식이다.

```text
(I - P)g = f
```

상수 함수에서는 `I-P`가 0이므로 전체 함수 공간에서는 역함수가 존재하지
않는다. 따라서 `π`-평균이 0인 함수만 모은 공간에서 해를 다룬다.

## 구현한 것

- `weightedMean`, `MeanZero`
- `laplacianOperator = I - P`
- stationarity에서 `(I-P)f`가 mean-zero임을 증명
- `FixedPointsAreConstants`
- mean-zero 공간에서 `I-P`의 injectivity
- `PoissonEquation`
- `MeanZeroPoissonSolvable`
- `MeanZeroPoissonInvertible`
- 선택된 centered `poissonSolution`과 그 방정식·유일성

## 가정 경계

일반적인 finite irreducibility의 경로 이론은 아직 구현하지 않았다. 대신
그 이론이 제공할 spectral 결론인 `FixedPointsAreConstants`와 Poisson 해의
존재를 정리문의 명시적 가정으로 둔다.

## 회귀 예제

- 원래 2상태 MH kernel: centered 해를 직접 구성해 invertibility 확인
- 2상태 identity kernel: 모든 함수가 고정점이므로
  `FixedPointsAreConstants`가 거짓임을 증명

## 다음 단계

- Poisson 해의 inverse quadratic form
- Dirichlet ordering에서 inverse ordering 도출
- algebraic asymptotic variance와 최종 MH Peskun theorem
