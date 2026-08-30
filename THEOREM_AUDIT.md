# LeanMetro theorem audit

## 최종 확률적 정리

```text
metropolisHastings_minimizes_sampleMeanAsymptoticVariance
```

고정된 target weight `w`와 proposal `q`에서 MH kernel과 임의의 admissible
accept/reject competitor를 비교한다. 두 kernel 각각에 대해 실제 finite-path
probability measure 위 표본평균의 scaled variance 극한을 제공하고, MH의
극한값이 competitor의 극한값보다 크지 않음을 동시에 증명한다.

## 명시적 가정

- 상태 타입은 유한하고 비어 있지 않다.
- 모든 target weight는 양수다.
- proposal entry는 비음수이고 각 행의 합은 1이다.
- 비교 acceptance rule은 `[0,1]`에 있고 accepted-flow detailed balance를
  만족한다.
- 관측량 `f`는 정규화된 target에 대해 mean-zero다.
- MH kernel과 비교 kernel 모두 mean-zero Poisson problem의 해가 존재하고
  유일하다.
- 두 kernel 모두 선택된 Poisson 해에 대한 covariance remainder가 0으로
  수렴한다.

마지막 두 조건은 각각 `MeanZeroPoissonInvertible`과 `Tendsto` theorem
parameter다. 따라서 irreducibility나 spectral gap을 구현하지 않은 상태에서
invertibility 또는 decay를 암묵적으로 사용하지 않는다.

## Lean에서 증명된 연결

```text
admissible acceptance
  ⇒ MH accepted-move maximality
  ⇒ off-diagonal Peskun domination
  ⇒ Dirichlet-form ordering
  ⇒ inverse-quadratic-form ordering
  ⇒ algebraic asymptotic-variance ordering

finite stationary path PMF/Measure
  ⇒ current-state marginal and path-sum moments
  ⇒ N * Var(actual sample mean) = stationaryScaledVariance
  ⇒ covariance decay 아래 algebraic asymptotic variance로 수렴
  ⇒ 실제 sample-mean asymptotic-variance Peskun ordering
```

표본 수는 항상 `N=n+1`이므로 0으로 나누는 경우가 없다. 경로의 초기분포는
`π`이고 이후 확률질량은 transition entry의 곱으로 정의된다. 경로질량의
비음수성과 전체 합 1, 그리고 `PMF.toMeasure`가 probability measure라는
사실까지 Lean이 검사한다.

## 수치 회귀 예제

3상태 uniform target에서 다음을 증명한다.

- fast uniform kernel: 실제 scaled sample-mean variance의 극한은 `2/3`
- lazy kernel: 실제 scaled sample-mean variance의 극한은 `2`
- lazy Poisson covariance는 `(4/3) * (1/2)^n`이므로 0으로 수렴
- `2/3 < 2`

## 아직 주장하지 않는 것

- irreducibility·aperiodicity에서 `MeanZeroPoissonInvertible` 또는 covariance
  decay를 자동 도출하는 일반 정리
- 하나의 무한 경로공간에서 모든 좌표과정을 동시에 구성하는 Kolmogorov
  extension
- Markov-chain central limit theorem 또는 분포수렴
- convergence rate 또는 mixing-time 최적성
- 일반 측도 상태공간의 MH
- 부동소수점 sampler 구현의 수치적 정확성

따라서 현재 결과는 실제 finite-horizon probability spaces의 표본평균
분산과 그 조건부 장시간 극한에 대한 finite-state Peskun theorem이다. 이는
CLT나 무한 경로공간을 증명했다는 주장은 아니다.
