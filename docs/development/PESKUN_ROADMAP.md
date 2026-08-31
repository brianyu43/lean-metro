# Lean Metro Part II: Machine-Checked Peskun Ordering

## 1. 출발점

`lean-metro` v0.1은 유한 상태공간에서 Metropolis–Hastings(MH)의 한 단계
correctness를 완성했다.

```text
scalar acceptance identity
  → accepted move
  → diagonal residual
  → stochastic transition
  → detailed balance
  → stationarity
```

기준 커밋은 `901d916`이다. Part II는 이 코드를 대체하는 마무리 작업이
아니라, 다음 질문을 다루는 별도 이론 층이다.

> 같은 proposal과 target을 사용하는 reversible accept/reject 규칙 중
> MH가 MCMC estimator의 asymptotic variance를 최소화하는가?

현재 진행 상태:

- [x] Phase 0 — GitHub Actions clean build
- [x] Phase 1 — generic acceptance, accept/reject transition, MH maximality
- [x] Phase 2 — finite reversible kernel 계층
- [x] Phase 3 — weighted operator와 Dirichlet ordering
- [x] Phase 4 — mean-zero 공간과 Poisson equation
- [x] Phase 5 — algebraic asymptotic variance와 Peskun theorem
- [x] Phase 6a — covariance/Cesàro variance-limit bridge
- [x] Phase 6b — finite-path 확률공간과 실제 sample-mean variance identity
- [x] Phase 7a — normalized stationary finite irreducibility에서 centered Poisson inverse 자동 생성
- [x] Phase 7b — reversible Poisson telescope로 covariance-decay 가정 제거
- [ ] Phase 7c — pointwise decay, mixing, rate를 위한 spectral adapter

## 2. 최종 목표

유한 상태공간 `S`, 양의 target weight `w`, stochastic proposal `q`,
admissible acceptance `a`, 생성된 MH/competitor kernel 각각의
irreducibility, 평균 0 함수 `f`에 대해 다음 최종 정리를 완료했다.

```text
metropolisHastings_minimizes_sampleMeanAsymptoticVariance_of_irreducible:
  HasSampleMeanAsymptoticVariance(MH, σMH)
  ∧ HasSampleMeanAsymptoticVariance(competitor, σA)
  ∧ σMH ≤ σA
```

v1.0의 완료선은 finite-state Poisson-equation 표현으로 증명한 algebraic
Peskun ordering이었다. Phase 6b에서는 각 유한 horizon의 실제 Markov path
probability measure를 구성하고, 확률변수의 장시간 scaled variance 극한과
이 algebraic 표현을 연결했다. Phase 7은 normalized target 아래 두 생성
kernel의 finite irreducibility만으로 Poisson inverse를 만들고, reversibility의
bounded telescoping argument로 pointwise covariance-decay 가정 없이 실제
극한을 닫았다.

## 3. 수학적 범위와 설계 원칙

- 상태공간은 `Fintype`으로 유지한다.
- 확률과 함수값은 우선 `ℝ`로 유지한다.
- general-state `ProbabilityTheory.Kernel`로 확장하지 않는다.
- stochasticity, reversibility, irreducibility 같은 가정을 구조체 또는
  명시적 predicate로 보존한다.
- MH 전용 계산과 일반 finite reversible-kernel 이론을 분리한다.
- `sorry`, `admit`, 사용자 정의 `axiom`은 허용하지 않는다.
- 각 단계는 개별 파일 컴파일과 전체 `lake build`를 통과해야 다음 단계로
  넘어간다.

## 4. 단계별 구현 계획

### Phase 0 — 재현성 기준선

산출물:

- `.github/workflows/lean.yml`
- clean environment에서 `lake exe cache get`과 `lake build`
- `sorry`/`admit`/`axiom` 정적 검사

완료 기준:

- workflow 문법 검토
- 로컬 `lake build` 통과
- GitHub Actions의 첫 성공 실행

### Phase 1 — Generic acceptance와 MH maximality

산출물:

- `LeanMetro/AcceptanceRule.lean`
- `AdmissibleAcceptance w q a`
- `acceptRejectAcceptedMove`
- generic leaving mass와 `acceptRejectTransition`
- stochasticity, detailed balance, stationarity
- `mhAcceptedMove_maximal`
- `mhTransition_offDiagonal_dominates`

핵심 논리:

```text
A = w(x)q(x,y), B = w(y)q(y,x)
A a(x,y) ≤ A
A a(x,y) = B a(y,x) ≤ B
따라서 A a(x,y) ≤ min(A,B) = A α_MH(x,y)
```

완료 기준:

- proposal의 영점 항을 포함해 컴파일
- 비대칭 2상태 예제로 strict domination 사례 확인
- v0.2 릴리스 후보

### Phase 2 — Finite reversible kernel 계층

산출물:

- `LeanMetro/MarkovKernel.lean`
- `FiniteKernel`
- `StationaryFor π P`
- `ReversibleFor π P`
- `PeskunDominates P₁ P₂`
- detailed balance에서 stationarity로 가는 기존 정리의 구조화

완료 기준:

- 대칭 MH, 비대칭 MH, arbitrary accept/reject transition을 같은 인터페이스로
  표현
- 기존 v0.1 예제의 회귀 빌드 유지

### Phase 3 — 가중 내적과 Dirichlet form

진행 상태:

- [x] `weightedInner`와 `markovOperator` 정의
- [x] Markov operator의 선형성 및 상수 함수 보존
- [x] reversibility에서 weighted self-adjointness
- [x] Dirichlet identity
- [x] Peskun domination에서 Dirichlet ordering

산출물:

- `LeanMetro/WeightedSpace.lean`
- `weightedInner π f g = ∑ x, π x * f x * g x`
- `markovOperator P f x = ∑ y, P x y * f y`
- reversibility에서 weighted self-adjointness
- `LeanMetro/DirichletForm.lean`
- Dirichlet identity
- Peskun domination에서 Dirichlet ordering

목표 정리:

```lean
theorem dirichletForm_mono_of_peskunDominates ... :
    dirichletForm π P₂ f ≤ dirichletForm π P₁ f
```

완료 기준:

- 모든 유한합 재배열을 명시적으로 검증
- v0.3 릴리스 후보

### Phase 4 — Mean-zero 공간과 Poisson equation

진행 상태:

- [x] weighted mean과 `MeanZero`
- [x] `laplacianOperator P = I - P`
- [x] `FixedPointsAreConstants`에서 mean-zero injectivity
- [x] Poisson 해의 존재·유일성 인터페이스
- [x] 정상 2상태 예제와 singular identity-kernel 반례

산출물:

- `LeanMetro/MeanZero.lean`
- `MeanZero π f`
- `L_P = I - P`
- 적절한 irreducibility 또는 고정점 가정
- mean-zero 부분공간에서 `L_P`의 injectivity와 invertibility
- `LeanMetro/Poisson.lean`
- `(I-P)g=f`의 해와 유일성

주요 위험:

- 일반 irreducibility를 경로 언어로 처음부터 구축하면 범위가 급증한다.
- 먼저 `FixedPointsAreConstants P` 같은 정확한 spectral 가정을 사용하고,
  이후 finite irreducibility에서 이를 도출하는 순서를 허용한다.

완료 기준:

- inverse 사용에 필요한 모든 조건이 theorem statement에 드러남
- singular한 예제를 잘못 허용하지 않는 회귀 예제

### Phase 5 — Algebraic asymptotic variance와 Peskun theorem

진행 상태:

- [x] inverse quadratic form
- [x] algebraic asymptotic variance
- [x] inverse ordering 분해 정리
- [x] 최종 MH 합성 정리
- [x] 2상태·3상태 수치 예제
- [x] 가정과 claim boundary audit

산출물:

- `LeanMetro/AsymptoticVariance.lean`
- Poisson 해를 통한 algebraic variance 정의

  ```text
  σ²_P(f) = 2⟨f,(I-P)⁻¹f⟩π - ⟨f,f⟩π
  ```

- inverse quadratic-form monotonicity
- `LeanMetro/Peskun.lean`
- MH maximality부터 variance ordering까지의 최종 합성 정리

완료 기준:

- `metropolisHastings_minimizes_algebraicAsymptoticVariance` 컴파일
- 2상태와 3상태 수치 예제
- 가정 누락 여부에 대한 별도 theorem audit

### Phase 6 — Variance-limit 연결

완료한 6a:

- [x] `markovIterate`와 lag covariance
- [x] stationary covariance 형태의 finite-time scaled variance
- [x] Poisson 식과의 정확한 finite-time remainder identity
- [x] Cesàro 정리를 사용한 조건부 variance-limit theorem
- [x] 3상태 fast kernel에서 극한값 `2/3` 검증

후속 6b:

- [x] 모든 유한 horizon의 stationary Markov path PMF와 measure 구성
- [x] 현재 상태의 주변분포와 path-sum second moment 도출
- [x] 실제 random-variable sample mean의 variance를 covariance 공식과 연결
- [x] 실제 scaled variance의 조건부 극한 정리
- [x] MH와 admissible competitor의 실제 극한 및 ordering을 한 정리로 합성
- [x] reversibility와 bounded Poisson telescope로 decay 가정 없는 극한 도출

구현한 산출물:

- `LeanMetro/VarianceLimit.lean`
- `stationaryScaledVariance_eq_algebraic_sub_remainder`
- `stationaryScaledVariance_tendsto_algebraicAsymptoticVariance`
- `LeanMetro/VarianceLimitExample.lean`
- `three_state_fast_scaledVariance_limit`
- `LeanMetro/FinitePath.lean`
- `ChainPath`, `stationaryPathPMF`, `stationaryPathMeasure`
- `LeanMetro/StationaryMoments.lean`
- `stationaryPath_current_expectation`, `stationaryPath_sum_secondMoment`
- `LeanMetro/SampleMeanVariance.lean`
- `chainSampleMean_scaledVariance_eq`, `chainSampleMean_scaledVariance_tendsto`
- `LeanMetro/ProbabilisticPeskun.lean`
- `metropolisHastings_minimizes_sampleMeanAsymptoticVariance`
- `LeanMetro/SampleMeanVarianceExample.lean`
- fast/lazy 3상태 실제 점근분산 극한 `2/3`, `2`
- `LeanMetro/ReversibleVarianceLimit.lean`
- `stationaryScaledVariance_tendsto_algebraicAsymptoticVariance_of_reversible`
- `LeanMetro/ReversibleSampleMeanVariance.lean`
- `chainSampleMean_scaledVariance_tendsto_of_reversible`

진행 조건:

- 기존 6a 극한 정리는 Poisson remainder covariance가 0으로 수렴한다는 가정을
  받는 호환 API로 유지한다. 새 reversible 정리는 그 가정을 받지 않는다.
- 표본 수는 `N=n+1`이며 Lean은
  `N * Var(chainSampleMean n) = stationaryScaledVariance n`을 증명한다.
- 하나의 무한 경로공간과 일반 Markov-chain CLT는 독립 후속 milestone로
  유지한다.

### Phase 7 — 표준 irreducibility와 decay-free variance adapter

완료한 7a:

- [x] `FiniteKernel.Irreducible P := Matrix.IsIrreducible P.prob`
- [x] finite maximum principle로 fixed points가 상수임을 증명
- [x] mean-zero 함수들을 실제 `Submodule`로 구성
- [x] `I-P`를 mean-zero subspace의 `LinearMap`으로 구성
- [x] 유한차원 injective → surjective로 centered Poisson solvability 도출
- [x] `meanZeroPoissonInvertible_of_irreducible` 완성
- [x] 2상태 MH와 lazy competitor에서 새 adapter를 실제 사용

완료한 7b:

- [x] Poisson 식과 self-adjointness에서 lag covariance를 이웃한 두
  quadratic form의 차로 표현
- [x] finite sum을 정확한 endpoint difference로 telescoping
- [x] stochastic Markov iterate와 endpoint quadratic form의 uniform bound
- [x] covariance-decay 가정 없는 actual sample-mean variance limit
- [x] 두 generated kernel의 irreducibility만 받는 public Peskun wrapper
- [x] period-2 reversible chain에서 pointwise decay 실패와 variance limit
  성공을 동시에 검증

남은 7c:

- [ ] irreducible·aperiodic reversible kernel의 mean-zero pointwise 또는
  norm decay
- [ ] spectral gap에서 quantitative mixing rate 도출

7a는 Poisson-invertibility 가정을 normalized stationarity와 표준
irreducibility로 닫는다. 7b는 실제 표본평균 분산 극한에 더 강한 pointwise
decay가 필요하지 않음을 증명한다. 7c의 spectral adapter는 `P^n g → 0`,
mixing, rate를 위한 독립 후속 범위이지 crown theorem의 미완성 가정이 아니다.

## 5. 파일 구조

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
```

실제 의존성이 더 단순해지는 경우 파일을 합칠 수 있지만, 서로 다른 이론
층을 한 파일에 섞어 컴파일 성공만 노리지는 않는다.

## 6. 일정 기준

| 기간 | 목표 | 릴리스 기준 |
|---|---|---|
| 8월 30일–9월 13일 | CI, generic transition, MH maximality | v0.2 |
| 9월 14일–10월 4일 | finite kernel, weighted operator, Dirichlet ordering | v0.3 |
| 10월 5일–11월 초 | mean-zero, Poisson, inverse inequality | v0.4 |
| 11월–12월 초 | 최종 Peskun 합성, 예제, 문서 | v1.0 후보 |
| 8월 31일 | finite-path variance-limit 직접 연결 | v1.1 |
| 8월 31일 | irreducibility adapter, crown integration, audit·포장 | v1.2 |
| 8월 31일 | reversible telescope, decay-free crown, periodic regression | v1.3 |

## 7. 검증과 릴리스 게이트

각 milestone에서 다음을 실행한다.

```bash
lake env lean <changed-module>
lake build
rg -n '\b(sorry|admit|axiom)\b' LeanMetro LeanMetro.lean
git diff --check
git status --short
```

원격 배포 후에는 다음도 확인한다.

```bash
git ls-remote origin refs/heads/main
```

릴리스 문서에는 반드시 다음을 분리한다.

- Lean kernel이 검사한 정리
- theorem statement에 둔 수학적 가정
- 아직 연결하지 않은 확률적 해석
- 수치 예제 또는 테스트로만 확인한 내용

## 8. 진행 알림 규칙

다음 이론 층을 시작하기 전에 사용자에게 먼저 알린다.

1. Generic acceptance와 MH maximality
2. Finite reversible kernel
3. Weighted operator와 Dirichlet form
4. Mean-zero 공간과 Poisson equation
5. Inverse inequality와 asymptotic variance
6. 확률적 variance-limit 연결
7. 표준 irreducibility와 reversible telescoping adapter
8. 필요할 때만 pointwise decay·mixing·rate용 spectral adapter

알림에는 새 정의, 필요한 가정, 이전 단계에서 재사용하는 정리, 이번 단계의
컴파일 완료 기준을 짧게 포함한다.
