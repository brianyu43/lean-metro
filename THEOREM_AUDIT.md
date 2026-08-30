# LeanMetro theorem audit

## 최종 정리

```text
metropolisHastings_minimizes_algebraicAsymptoticVariance
```

고정된 target weight `w`와 proposal `q`에서 MH kernel의 algebraic
asymptotic variance가 임의의 admissible accept/reject kernel보다 크지
않음을 증명한다.

## 명시적 가정

- 상태 타입은 유한하고 비어 있지 않다.
- 모든 target weight는 양수다.
- proposal entry는 비음수이고 각 행의 합은 1이다.
- 비교 acceptance rule은 `[0,1]`에 있고 accepted flow detailed balance를
  만족한다.
- 관측량 `f`는 정규화된 target에 대해 mean-zero다.
- MH kernel과 비교 kernel 모두 mean-zero Poisson problem의 해가 존재하고
  유일하다.

마지막 조건은 `MeanZeroPoissonInvertible`이라는 theorem parameter다.
따라서 일반 irreducibility를 구현하지 않은 상태에서 invertibility를
암묵적으로 사용하지 않는다.

## Lean에서 증명된 연결

```text
admissible acceptance
  ⇒ MH accepted-move maximality
  ⇒ off-diagonal Peskun domination
  ⇒ Dirichlet-form ordering
  ⇒ inverse-quadratic-form ordering
  ⇒ algebraic asymptotic-variance ordering
```

## 조건부 variance-limit bridge

`stationaryScaledVariance_tendsto_algebraicAsymptoticVariance`는 Poisson
remainder covariance가 0으로 수렴한다는 명시적 가정 아래, stationary
covariance 형태의 유한시간 식이 algebraic asymptotic variance로 수렴함을
증명한다. 3상태 fast-kernel 예제에서는 이 decay와 극한값 `2/3`을 Lean이
검사한다.

## 아직 주장하지 않는 것

- irreducibility에서 `MeanZeroPoissonInvertible`을 자동 도출
- 실제 확률변수로 만든 stationary Markov chain의 CLT
- 실제 stationary random-variable process의 `lim n * Var(sample mean)`과
  `stationaryScaledVariance`의 동일성
- convergence rate 또는 mixing-time 최적성
- 부동소수점 구현의 수치적 정확성

따라서 현재 결과는 완성된 finite-dimensional algebraic Peskun theorem이며,
확률적 variance-limit theorem이라고 부르지 않는다.
