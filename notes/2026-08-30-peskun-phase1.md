# 2026-08-30 Peskun Phase 1

## 새 이론

임의의 acceptance rule `a`를 다음 세 조건으로 추상화했다.

```text
0 ≤ a(x,y)
a(x,y) ≤ 1
w(x)q(x,y)a(x,y) = w(y)q(y,x)a(y,x)
```

이를 `AdmissibleAcceptance w q a`로 묶었다.

## 구현한 것

- `acceptRejectAcceptedMove`
- `acceptRejectLeavingMass`
- `acceptRejectTransition`
- generic transition의 비음수성과 행 합 1
- generic transition의 detailed balance와 stationarity
- `mhAsymmetricAcceptance_admissible`
- generic MH transition과 기존 `mhAsymmetricTransition`의 일치
- `mhAcceptedMove_maximal`
- `mhTransition_offDiagonal_dominates`

## maximality의 핵심

```text
A = w(x)q(x,y)
B = w(y)q(y,x)
```

이라고 두면 admissibility에서

```text
A a(x,y) ≤ A
A a(x,y) = B a(y,x) ≤ B
```

이므로 `A a(x,y) ≤ min(A,B)`이다. 기존의 영점 안전 정리
`nonneg_mul_acceptance_eq_min`이 `min(A,B)`를 MH accepted flow로 바꾼다.
마지막으로 `w(x)>0`을 사용해 weight를 약분하면 accepted move maximality가
나온다.

## 수치 회귀 예제

`rejectAllAcceptance = 0`은 admissible하지만 모든 proposal을 거절한다.
기존 비대칭 2상태 proposal에서 Lean은 다음 strict inequality를 확인한다.

```text
P_rejectAll(0,1) < P_MH(0,1)
```

## 검증 기준

- `lake env lean LeanMetro/AcceptanceRule.lean`
- `lake env lean LeanMetro/AsymmetricExample.lean`
- `lake build`
- Lean 소스의 `sorry`, `admit`, `axiom` 부재
- `git diff --check`
