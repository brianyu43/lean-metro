# 린메트로

[![Lean CI](https://github.com/brianyu43/lean-metro/actions/workflows/lean.yml/badge.svg)](https://github.com/brianyu43/lean-metro/actions/workflows/lean.yml)

[English README](README.en.md)

유한 상태 Metropolis–Hastings correctness와 실제 stationary 표본평균의
Peskun asymptotic-variance ordering을 Lean 4로 형식 검증한다.

주정리 `metropolisHastings_minimizes_sampleMeanAsymptoticVariance`는 동일한
target·proposal을 쓰는 MH와 admissible competitor의 실제 scaled-variance
극한을 구성하고 MH의 극한값이 더 크지 않음을 증명한다. 유한 비공집합,
양의 target, stochastic proposal, centered observable, 양쪽 centered Poisson
invertibility와 covariance decay를 명시적으로 받는다. 다만 normalized
stationarity와 finite irreducibility에서는 Poisson invertibility를 프로젝트
내부 adapter로 자동 생성한다. 무한 path space, CLT, 일반 aperiodicity에서 covariance decay의
자동 도출은 아직 주장하지 않는다.
[정리 감사](THEOREM_AUDIT.md) · [증명 소유권 가이드](docs/PROOF_OWNERSHIP_GUIDE.md) · [변경 기록](CHANGELOG.md) · [MIT 라이선스](LICENSE)

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
- 같은 target과 proposal의 admissible accept/reject 규칙 중 MH가 모든
  비대각 transition을 최대화한다.
- Peskun domination은 Dirichlet form을 증가시키고 inverse quadratic form을
  감소시킨다.
- centered Poisson problem이 invertible이면 MH가 algebraic asymptotic
  variance를 최소화한다.
- 각 유한 horizon에 실제 stationary Markov path probability measure를
  구성한다.
- 표본 수 `N=n+1`에 대해 실제 random-variable 표본평균의 분산이

  ```text
  N * Var(sample mean) = stationaryScaledVariance
  ```

  를 만족함을 증명한다.
- Poisson remainder covariance가 0으로 수렴하면 이 실제 scaled variance가
  algebraic asymptotic variance로 수렴하며, 같은 가정 아래 MH의 극한값이
  임의 admissible accept/reject kernel보다 작거나 같다.

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

## Part II: Peskun ordering

[장기 로드맵](docs/development/PESKUN_ROADMAP.md)에 따라 “MH가 맞다”에서 “왜 MH가 같은
proposal의 다른 reversible accept/reject 규칙보다 효율적인가”로 확장하고
있다.

현재 `LeanMetro/AcceptanceRule.lean`에서 다음을 증명했다.

- `AdmissibleAcceptance`: acceptance의 범위와 accepted-flow balance
- generic `acceptRejectTransition`의 stochasticity, detailed balance,
  stationarity
- `mhAsymmetricAcceptance_admissible`
- `mhAcceptedMove_maximal`: MH가 accepted move를 최대화
- `mhTransition_offDiagonal_dominates`: 모든 비대각 transition에서 MH가
  임의 admissible rule을 지배

`LeanMetro/MarkovKernel.lean`은 `FiniteKernel`, `ReversibleKernel`,
`PeskunDominates`를 정의한다. `metropolisHastingsKernel_peskunDominates`는
MH maximality를 구조화된 kernel ordering으로 표현한다. 비대칭 2상태
예제에서는 모든 proposal을 거절하는 admissible rule보다 MH의 `0 → 1`
transition이 엄격히 큼을 계산하고 이 kernel ordering을 인스턴스화했다.

`LeanMetro/WeightedSpace.lean`은 `π`-가중 내적과 Markov operator를
정의하고, detailed balance를 이용해 reversible kernel의 Markov operator가
weighted self-adjoint임을 증명한다. `LeanMetro/DirichletForm.lean`은
Dirichlet identity와 Peskun ordering을 증명하며, 이를 앞 단계의 acceptance
maximality에 연결해 MH가 모든 admissible accept/reject 규칙보다 Dirichlet
form을 크게 만든다는 정리를 제공한다.

`LeanMetro/MeanZero.lean`과 `LeanMetro/Poisson.lean`은 mean-zero 함수에
대한 `I-P`의 injectivity와 Poisson 해의 존재·유일성 인터페이스를 만든다.
`LeanMetro/PoissonExample.lean`에서는 2상태 MH의 centered Poisson 해를
직접 구성한다. 반대로 identity chain은 모든 함수가 고정점이므로 필요한
고정점 조건을 만족하지 않는다는 singular 회귀 예제도 포함한다.

`LeanMetro/Irreducibility.lean`은 mathlib의 표준
`Matrix.IsIrreducible`을 finite kernel에 연결한다. 최대원리로
irreducibility에서 `FixedPointsAreConstants`를 도출하고, mean-zero
`Submodule` 위 `I-P`를 `LinearMap`으로 묶어 유한차원 단사⇒전사를 적용한다.
따라서 `meanZeroPoissonInvertible_of_irreducible`은 기존의 Poisson
invertibility 가정을 자동 생성한다. 2상태 MH와 lazy 예제가 이 adapter를
실제로 사용한다.

`LeanMetro/AsymptoticVariance.lean`은 Poisson 해로 inverse quadratic form과
algebraic asymptotic variance를 정의하고, Dirichlet ordering에서 inverse
ordering을 도출한다. `LeanMetro/Peskun.lean`의
`metropolisHastings_minimizes_algebraicAsymptoticVariance`는 MH acceptance
maximality부터 variance ordering까지를 한 정리로 합성한다.

`LeanMetro/PeskunExample.lean`의 2상태 예제에서는 MH와 lazy kernel의
분산이 각각 `3/2`, `6`이다. `LeanMetro/ThreeStateExample.lean`의 uniform
3상태 예제에서는 fast kernel과 lazy kernel의 분산이 각각 `2/3`, `2`다.
두 예제 모두 직접 계산과 일반 Peskun 정리 적용을 함께 검증한다.

`LeanMetro/VarianceLimit.lean`은 stationary covariance 형태의 유한시간 식이
Poisson remainder의 Cesàro 평균만큼 algebraic variance와 다르다는 정확한
항등식과, remainder covariance가 0으로 수렴할 때의 극한 정리를 증명한다.
`LeanMetro/FinitePath.lean`부터 `LeanMetro/ProbabilisticPeskun.lean`까지는
모든 horizon에 대해 실제 path PMF와 probability measure를 구성하고,
mathlib의 `ProbabilityTheory.variance`로 계산한 표본평균 분산을 위 식과
연결한다. 최종 정리는 다음이다.

```text
metropolisHastings_minimizes_sampleMeanAsymptoticVariance
```

3상태 회귀 예제에서는 fast kernel과 lazy kernel의 실제 표본평균
점근분산이 각각 `2/3`, `2`이고 전자가 엄격히 작음을 검증한다. 필요한
Poisson covariance decay도 fast와 lazy 양쪽에서 Lean으로 증명한다.
`LeanMetro/CrownExample.lean`은 동일한 2상태 target·proposal에서 MH와
half-acceptance competitor를 만들고 최종 probabilistic theorem을 직접
호출해 실제 극한 `3/2 ≤ 6`을 얻는 end-to-end integration test다.
[정리 가정 감사](THEOREM_AUDIT.md)는 정리의 가정과 남은 경계를 분리한다.

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
├── AcceptanceRule.lean
├── MarkovKernel.lean
├── WeightedSpace.lean
├── DirichletForm.lean
├── MeanZero.lean
├── Poisson.lean
├── PoissonExample.lean
├── Irreducibility.lean
├── IrreducibilityExample.lean
├── AsymptoticVariance.lean
├── Peskun.lean
├── PeskunExample.lean
├── ThreeStateExample.lean
├── VarianceLimit.lean
├── VarianceLimitExample.lean
├── FinitePath.lean
├── StationaryMoments.lean
├── SampleMeanVariance.lean
├── ProbabilisticPeskun.lean
├── SampleMeanVarianceExample.lean
├── CrownExample.lean
├── AxiomAudit.lean
├── TwoState.lean
└── AsymmetricExample.lean
```

핵심 의존성은 다음 순서다.

```text
AcceptanceRule → MarkovKernel → WeightedSpace → DirichletForm
                                             ↓
MeanZero → Poisson → AsymptoticVariance → Peskun
                                         ↓
                                  VarianceLimit
                                         ↓
FinitePath → StationaryMoments → SampleMeanVariance
                                         ↓
                               ProbabilisticPeskun
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
lake env lean LeanMetro/Peskun.lean
lake env lean LeanMetro/VarianceLimit.lean
lake env lean LeanMetro/SampleMeanVariance.lean
lake env lean LeanMetro/ProbabilisticPeskun.lean
```

## 의도적인 범위 제한

이 프로젝트는 finite-state MH correctness와, normalized stationarity 및
finite irreducibility에서 자동 생성한 Poisson invertibility, 그리고 명시적 covariance-decay 가정 아래
실제 stationary 표본평균의 점근분산 Peskun ordering을 증명한다. 다음은
포함하지 않는다.

- 일반 aperiodicity·spectral gap에서 covariance decay를 자동 도출하는
  adapter
- 임의 초기분포에서 stationary distribution으로의 convergence
- convergence rate 또는 mixing time
- 일반 측도공간의 `ProbabilityTheory.Kernel`
- 부동소수점 sampler 구현의 정확성
- 하나의 무한 경로공간 위에서 모든 시간 좌표를 동시에 구성하는
  Kolmogorov extension 또는 Markov-chain CLT

detailed balance와 stationarity만으로 임의 초기상태에서의 convergence가
따라오는 것은 아니다.

## 관련 공개 작업

이 프로젝트의 수학적 구성은 표준 MH 알고리즘이다. 더 일반적인 Lean
형식화와 실행 계층을 포함하는 공개 프로젝트로
[`xukai92/mcmc-lean`](https://github.com/xukai92/mcmc-lean)이 있다.
린메트로는 학습과 검토가 쉬운 작은 실수·유한합 증명에 초점을 둔다.
