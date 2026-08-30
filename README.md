# 린메트로

[![Lean CI](https://github.com/brianyu43/lean-metro/actions/workflows/lean.yml/badge.svg)](https://github.com/brianyu43/lean-metro/actions/workflows/lean.yml)

유한 상태공간 Metropolis–Hastings(MH) 알고리즘의 transition matrix,
detailed balance, stationary distribution을 Lean 4로 형식 검증한 작은
프로젝트다.

프로젝트는 실수 `ℝ` 위의 양수 target weight와 유한합을 직접 사용한다.
완전한 확률론 라이브러리를 먼저 설계하지 않고, MH correctness의 수학적
골격이 Lean 코드에서 보이도록 구성했다.

## 최종 결과

유한하고 비어 있지 않은 상태공간에서 다음을 증명한다.

- 양수 target weight를 정규화하면 비음수이고 합이 1이다.
- proposal의 각 항이 비음수이고 각 행의 합이 1이면 완성된 MH transition도
  비음수이고 각 행의 합이 1이다.
- 대칭 proposal에서는 `min(1, w(y) / w(x))` acceptance가 detailed
  balance를 만족한다.
- 비대칭 proposal에서는

  ```text
  min(1, (w(y) * q(y,x)) / (w(x) * q(x,y)))
  ```

  acceptance가 detailed balance를 만족한다.
- 두 경우 모두 정규화된 target weight가 stationary distribution이다.

대각항은 다른 상태로 실제 이동하고 남은 확률로 정의한다.

```text
P(x,x) = 1 - ∑ y ≠ x, q(x,y) * acceptance(x,y)
```

## 증명 사다리

| 단계 | 주요 Lean 결과 | 파일 |
|---|---|---|
| 스칼라 acceptance 항등식 | `mh_balance_scalar` | `LeanMetro/Balance.lean` |
| 대칭 proposal 비대각 balance | `mh_balance_symmetric_proposal` | `LeanMetro/OffDiagonal.lean` |
| 대각항과 행 합 | `mhTransition_nonneg`, `mhTransition_row_sum` | `LeanMetro/Transition.lean` |
| 전체 detailed balance | `mhTransition_detailed_balance` | `LeanMetro/Stationary.lean` |
| detailed balance → stationary | `stationary_of_detailed_balance`, `mhTransition_stationary` | `LeanMetro/Stationary.lean` |
| 대칭 MH 최종 보증 | `mhTransition_correct` | `LeanMetro/Stationary.lean` |
| 비대칭 MH 전체 구성 | `mhAsymmetricTransition` | `LeanMetro/Asymmetric.lean` |
| 비대칭 MH 최종 보증 | `mhAsymmetricTransition_correct` | `LeanMetro/Asymmetric.lean` |

`mhTransition_correct`와 `mhAsymmetricTransition_correct`는 target의
정규화, transition의 비음수성과 행 합, detailed balance, stationarity를
한 정리로 묶는다.

## 수치 예제

### 대칭 proposal

Target weight와 proposal은 다음과 같다.

```text
w = (1, 3)
q = [[0, 1],
     [1, 0]]
```

Lean이 계산하는 transition과 stationary distribution은 다음과 같다.

```text
P  = [[0,   1],
      [1/3, 2/3]]
π  = (1/4, 3/4)
```

`LeanMetro/TwoState.lean`은 직접 수치 계산과 일반 정리에서의 도출을 모두
증명한다.

### 비대칭 proposal

```text
q = [[1/2, 1/2],
     [1/4, 3/4]]

P = [[1/2, 1/2],
     [1/6, 5/6]]
```

여기서는 `q(0,1) ≠ q(1,0)`이다. `LeanMetro/AsymmetricExample.lean`은
이 proposal이 비대칭임을 증명하고, 일반 비대칭 MH 정의가 위 transition을
정확히 생성하며 `π = (1/4, 3/4)`를 stationary하게 유지함을 검증한다.

## 프로젝트 구조

```text
LeanMetro/
├── Balance.lean
├── OffDiagonal.lean
├── Transition.lean
├── Stationary.lean
├── Asymmetric.lean
├── TwoState.lean
└── AsymmetricExample.lean
```

## 빌드

Lean `v4.33.1`과 고정된 mathlib revision을 사용한다.

```bash
lake update
lake exe cache get
lake build
```

개별 핵심 파일은 다음처럼 검사할 수 있다.

```bash
lake env lean LeanMetro/Stationary.lean
lake env lean LeanMetro/Asymmetric.lean
lake env lean LeanMetro/AsymmetricExample.lean
```

## 의도적인 범위 제한

이 프로젝트가 증명하는 것은 유한 상태 MH transition의 한 단계 correctness다.
다음은 포함하지 않는다.

- irreducibility와 aperiodicity
- 임의 초기분포에서 stationary distribution으로의 convergence
- convergence rate 또는 mixing time
- 일반 측도공간의 `ProbabilityTheory.Kernel`
- 부동소수점 sampler 구현의 정확성

detailed balance와 stationarity만으로 임의 초기상태에서의 convergence가
따라오는 것은 아니다.

## 관련 공개 작업

이 프로젝트의 수학적 구성은 표준 MH 알고리즘이다. 더 일반적인 Lean
형식화와 실행 계층을 포함하는 공개 프로젝트로
[`xukai92/mcmc-lean`](https://github.com/xukai92/mcmc-lean)이 있다.
린메트로는 학습과 검토가 쉬운 작은 실수·유한합 증명에 초점을 둔다.
