# 2026-08-31 Peskun Phase 6b

## 실제 경로 확률공간

`ChainPath ι n`은 시각 `0`부터 `n`까지의 `n+1`개 상태를 담는다. 초기
질량 `π(x₀)`와 transition probability들의 곱으로 경로질량을 정의하고,
모든 경로질량의 합이 1임을 증명해 `PMF`와 `Measure`를 만들었다.

## 모멘트와 분산

stationarity에서 마지막 상태의 주변분포가 항상 `π`임을 보였다. 이를
재귀적으로 사용해 경로합의 교차 모멘트와 2차 모멘트를 계산했다.
mean-zero 관측량에 대해서는 mathlib의 실제 `ProbabilityTheory.variance`가
2차 모멘트와 같으므로 다음 정확한 식을 얻었다.

```text
(n+1) * Var(chainSampleMean n) = stationaryScaledVariance n
```

## 최종 정리

Poisson covariance decay를 명시적으로 가정해 실제 scaled variance의 극한을
algebraic asymptotic variance와 연결했다. 이를 기존 algebraic Peskun
ordering과 합성해
`metropolisHastings_minimizes_sampleMeanAsymptoticVariance`를 증명했다.

## 회귀 예제와 남은 경계

3상태 fast/lazy kernel의 실제 극한은 각각 `2/3`, `2`다. lazy kernel에서는
covariance가 `(4/3) * (1/2)^n`임을 증명했다. 하나의 무한 경로공간, CLT,
그리고 일반 irreducibility에서 decay를 자동 도출하는 정리는 포함하지
않는다.
