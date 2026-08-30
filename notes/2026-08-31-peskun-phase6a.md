# 2026-08-31 Peskun Phase 6a

## 새 이론

Markov operator를 반복 적용해 lag covariance를 정의하고, 표본 크기
`N=n+1`에 대한 stationary covariance 형태의 scaled variance를 만들었다.

## 정확한 finite-time 항등식

Poisson 해 `g`에 대해 다음 형태를 Lean으로 증명했다.

```text
stationaryScaledVariance(n)
  = algebraicAsymptoticVariance
    - 2/(n+1) * ∑_{k=1}^{n+1} <f, P^k g>_π
```

핵심은 `f=(I-P)g`에서 lag covariance가 인접한 두 항의 차이로 바뀌고,
가중 유한합이 telescoping한다는 것이다.

## 극한

`<f,P^n g>_π → 0`이면 mathlib의 Cesàro theorem으로 remainder 평균도
0으로 수렴한다. 따라서 finite-time 식은 algebraic asymptotic variance로
수렴한다.

## 예제

3상태 fast uniform kernel은 한 번 적용한 뒤 centered Poisson solution을
0으로 보내므로 decay가 즉시 성립한다. Lean은 scaled variance의 극한이
`2/3`임을 검증한다.

## 남은 확률론 경계

아직 random-variable Markov process를 구성해 실제 `Var(sample mean)`과
위 covariance 식을 동일시하지 않았다. 이것은 Phase 6b 후속 milestone다.
