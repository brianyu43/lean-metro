# 린메트로

[![Lean CI](https://github.com/brianyu43/lean-metro/actions/workflows/lean.yml/badge.svg)](https://github.com/brianyu43/lean-metro/actions/workflows/lean.yml)

[English README](README.en.md)

유한 상태 Metropolis–Hastings correctness와 실제 stationary 표본평균의
Peskun asymptotic-variance ordering을 Lean 4로 형식 검증한다.

주정리
`metropolisHastings_minimizes_sampleMeanAsymptoticVariance_of_irreducible`은
동일한 양의 target·stochastic proposal을 쓰는 MH와 admissible competitor가
각각 finite irreducible이면 실제 scaled-variance 극한이 존재하고 MH의
극한값이 더 크지 않음을 증명한다. Poisson inverse는 최대원리와 유한차원
선형대수로 만들고, reversibility가 exact remainder를 망원합으로 바꾸므로
covariance decay나 aperiodicity를 가정하지 않는다. 무한 path space, CLT,
mixing rate는 주장하지 않는다.
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
- reversible kernel에서는 Poisson remainder의 Cesàro 합이 두 endpoint의
  차이로 망원합되고, finite stochastic iterate가 균일하게 bounded이므로
  별도 covariance-decay 가정 없이 실제 scaled variance가 algebraic
  asymptotic variance로 수렴한다.
- normalized stationary finite irreducible MH와 irreducible admissible
  competitor에 대해 Poisson inverse와 두 실제 극한을 내부에서 만들고, MH의
  극한값이 더 크지 않음을 증명한다.

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
항등식을 증명한다. `LeanMetro/ReversibleVarianceLimit.lean`은

```text
∑ k=0..n, <f, P^(k+1)g>_π
  = <g, Pg>_π - <g, P^(n+2)g>_π
```

를 증명하고 finite Markov iterate의 uniform bound로 remainder를 0에 보낸다.
따라서 pointwise covariance decay, aperiodicity, spectral theorem 없이도
variance limit이 성립한다. `LeanMetro/FinitePath.lean`부터
`LeanMetro/ReversibleSampleMeanVariance.lean`까지는 실제 path PMF와
mathlib의 `ProbabilityTheory.variance`를 이 극한에 연결한다. 표준 가정형
최종 정리는 다음이다.

```text
metropolisHastings_minimizes_sampleMeanAsymptoticVariance_of_irreducible
```

3상태 회귀 예제에서는 fast kernel과 lazy kernel의 실제 표본평균
점근분산이 각각 `2/3`, `2`이고 전자가 엄격히 작음을 검증한다. 필요한
기존 decay 기반 정리와 구체적 geometric decay 증명도 더 강한 spectral
성질을 설명하는 호환 API로 유지한다.
`LeanMetro/CrownExample.lean`은 동일한 2상태 target·proposal에서 MH와
half-acceptance competitor를 만들고 새 irreducibility-facing theorem을 직접
호출해 실제 극한 `3/2 ≤ 6`을 얻는다. 이 호출에는 `hinv`와 `hdecay` 인자가
없다. `LeanMetro/PeriodicVarianceExample.lean`은 deterministic two-cycle의
Poisson covariance가 `(-1)^n/2`라서 0으로 수렴하지 않지만 실제 scaled
variance는 0으로 수렴함을 검증한다.
[정리 가정 감사](THEOREM_AUDIT.md)는 정리의 가정과 남은 경계를 분리한다.

## Part III: 일반 상태공간 확장 (개발 중)

기존 finite 이론을 그대로 보존하면서 `LeanMetroGeneral` namespace에서
measure-theoretic 이론층을 별도로 만들고 있다. 현재 컴파일되는 첫 결과는
다음 사슬이다.

```text
proposalFlow π Q = π(dx)Q(x,dy)
swap symmetry = measure-level reversibility
measure-level reversibility => stationarity
reference-reversible target flow density: h(x) / h(y)
balanced competitor accepted density <= min(h(x), h(y))
```

`referenceMH_largest_reversibleAcceptedFlow`은 reference proposal flow가
swap-symmetric이고 `h`와 acceptance가 measurable이며 acceptance가 1 이하이고
accepted density가 양방향으로 balance된다는 조건 아래 다음 세 결론을 함께
증명한다.

- competitor accepted flow가 swap-symmetric이다.
- MH accepted flow가 swap-symmetric이다.
- competitor accepted flow가 MH accepted flow 이하이다.

즉 finite의 `Aa ≤ A`, `Aa = Baᵀ ≤ B`, 따라서 `Aa ≤ min(A,B)` 논증을 joint
measure의 a.e. density와 `Measure.withDensity_mono`로 옮겼다.
`FiniteAdapter.lean`은 counting measure 위에서 이 결과가 대칭·양의 finite
proposal에 대한 기존 accepted-move maximality를 복원함을 검증한다.

아직 general accept/reject Markov kernel, Dirichlet/L²/Poisson ordering,
Ionescu--Tulcea trajectory variance, spectral-gap adapter, Gaussian pCN은
증명하지 않았다. 단계별 완료선과 full Tierney 정리까지의 범위는
[general-state 로드맵](docs/development/GENERAL_STATE_ROADMAP.md)에 고정했다.

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
├── ReversibleVarianceLimit.lean
├── VarianceLimitExample.lean
├── FinitePath.lean
├── StationaryMoments.lean
├── SampleMeanVariance.lean
├── ReversibleSampleMeanVariance.lean
├── ProbabilisticPeskun.lean
├── IrreduciblePeskun.lean
├── SampleMeanVarianceExample.lean
├── CrownExample.lean
├── PeriodicVarianceExample.lean
├── AxiomAudit.lean
├── TwoState.lean
└── AsymmetricExample.lean

LeanMetroGeneral/
├── JointFlow.lean
├── Reversibility.lean
├── ReferenceProposal.lean
├── AcceptedFlow.lean
├── FiniteAdapter.lean
└── AxiomAudit.lean
```

핵심 의존성은 다음 순서다.

```text
AcceptanceRule → MarkovKernel → WeightedSpace → DirichletForm
                                             ↓
MeanZero → Poisson → AsymptoticVariance → Peskun
                                         ↓
                    VarianceLimit → ReversibleVarianceLimit
                                         ↓
FinitePath → StationaryMoments → SampleMeanVariance
                                         ↓
                          ReversibleSampleMeanVariance
                                         ↓
                     ProbabilisticPeskun → IrreduciblePeskun
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
lake env lean LeanMetro/ReversibleVarianceLimit.lean
lake env lean LeanMetro/SampleMeanVariance.lean
lake env lean LeanMetro/ReversibleSampleMeanVariance.lean
lake env lean LeanMetro/ProbabilisticPeskun.lean
lake env lean LeanMetro/IrreduciblePeskun.lean
lake env lean LeanMetro/CrownExample.lean
lake env lean LeanMetro/PeriodicVarianceExample.lean
lake env lean LeanMetro/AxiomAudit.lean
lake env lean LeanMetroGeneral/AcceptedFlow.lean
lake env lean LeanMetroGeneral/FiniteAdapter.lean
lake env lean LeanMetroGeneral/AxiomAudit.lean
```

## 의도적인 범위 제한

이 프로젝트는 finite-state MH correctness와, normalized stationarity 및
finite irreducibility에서 자동 생성한 Poisson invertibility, reversible
telescoping으로 얻은 실제 stationary 표본평균의 점근분산 Peskun ordering을
증명한다. 다음은 포함하지 않는다.

- `P^n g → 0`의 pointwise 또는 norm decay와 이를 주는 일반 spectral adapter
- 임의 초기분포에서 stationary distribution으로의 convergence
- convergence rate 또는 mixing time
- 일반 상태공간의 완성된 accept/reject Markov kernel과 Peskun variance theorem
- Gaussian measure 위 무한차원 pCN 적용
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
