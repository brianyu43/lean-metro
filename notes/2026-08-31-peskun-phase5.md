# 2026-08-31 Peskun Phase 5

## 새 이론

Centered Poisson solution `g=(I-P)⁻¹f`를 사용해 다음 양을 정의했다.

```text
inverseQuadraticForm = <f,g>_π
algebraicAsymptoticVariance = 2<f,g>_π - <f,f>_π
```

## 핵심 증명

`P₁`이 `P₂`를 Peskun 지배하고 각각의 Poisson 해가 `g₁`, `g₂`이면
다음 분해를 사용한다.

```text
<f,g₂>_π - <f,g₁>_π
  = E_{P₂}(g₂-g₁) + E_{P₁}(g₁) - E_{P₂}(g₁)
```

오른쪽의 첫 항은 제곱합이라 비음수이고, 나머지 차이는 Dirichlet ordering
때문에 비음수다. 따라서 더 많이 움직이는 kernel의 inverse quadratic
form과 algebraic asymptotic variance가 더 작다.

## 최종 정리

- `inverseQuadraticForm_mono_of_peskunDominates`
- `algebraicAsymptoticVariance_mono_of_peskunDominates`
- `metropolisHastings_minimizes_algebraicAsymptoticVariance`

## 수치 회귀 예제

- 2상태: MH `3/2`, lazy kernel `6`
- 3상태: fast uniform kernel `2/3`, lazy kernel `2`

각 예제는 명시적 Poisson 해를 확인하고, 직접 계산한 strict inequality와
일반 Peskun 정리의 non-strict inequality를 모두 컴파일한다.

## Claim boundary

현재 결과는 finite-dimensional algebraic theorem이다. 실제 stationary
chain의 variance limit와 동일하다는 확률론적 연결은 아직 증명하지 않았다.
