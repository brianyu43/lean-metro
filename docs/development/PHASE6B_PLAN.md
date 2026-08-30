# Lean Metro Phase 6b: Probabilistic sample-mean variance

## 1. 목표

Phase 6a의 `stationaryScaledVariance`를 실제 유한 확률공간 위 표본평균의
분산과 연결한다. 최종적으로 다음 세 층을 Lean에서 합성한다.

```text
stationary finite Markov path law
  ⇒ (N * Var(sample mean)) = stationaryScaledVariance
  ⇒ Poisson covariance decay 아래 algebraic asymptotic variance로 수렴
  ⇒ MH의 실제 sample-mean asymptotic variance ordering
```

`N=0`에서의 나눗셈 문제를 피하기 위해 모든 horizon은 표본 수
`N=n+1`로 색인한다.

## 2. 수학적 가정

- `ι`는 유한하고 비어 있지 않은 상태공간이다.
- `π : ι → ℝ`는 비음수이고 합이 1이다.
- `P : FiniteKernel ι`는 비음수이고 각 행의 합이 1이다.
- `π`는 `P`에 대해 stationary하다.
- 관측량 `f`는 `π`에 대해 mean-zero다.
- 극한 정리에서는 centered Poisson problem의 invertibility와
  `<f, P^n g>_π → 0`을 명시적으로 가정한다.

일반 irreducibility·aperiodicity에서 마지막 decay를 자동 도출하는 spectral
adapter는 별도 보조 정리로 분리한다. 확률적 분산 동일성 자체에는 그 가정이
필요하지 않다.

## 3. 구현 계층

### Phase 6b.1 — 실제 finite-horizon path probability space

파일: `LeanMetro/FinitePath.lean`

- `ChainPath ι n`: 시각 `0,…,n`의 상태를 담는 유한 경로 타입
- `chainPathMass π P n`: 초기질량과 transition들의 곱
- 경로질량의 비음수성과 전체 합 1
- `stationaryPathPMF`
- `stationaryPathMeasure = PMF.toMeasure`
- `IsProbabilityMeasure stationaryPathMeasure` instance 확인
- 적분을 유한 가중합으로 바꾸는 정리

완료 기준:

- PMF 정규화가 `π`와 `P`의 가정에서 도출됨
- 임의 horizon에 대해 실제 mathlib `Measure`와 probability-measure instance가
  존재함

### Phase 6b.2 — Stationary moment identities

파일: `LeanMetro/StationaryMoments.lean`

- `chainPathCurrent`, `chainPathSum`
- 현재 상태의 주변분포가 모든 horizon에서 `π`
- 임의 `h`에 대한 current-state expectation
- cross moment

  ```text
  E[(∑ₜ f(Xₜ)) h(Xₙ)]
    = ∑ₖ₌₀ⁿ <f, P^k h>_π
  ```

- partial-sum 평균과 second moment
- mean-zero일 때 `Var(partial sum)`이 second moment와 같음

완료 기준:

- 경로 PMF의 유한합에서 모든 moment 식을 직접 도출
- stationary 가정이 사용되는 위치가 theorem statement에 나타남

### Phase 6b.3 — 실제 sample-mean variance identity

파일: `LeanMetro/SampleMeanVariance.lean`

- `chainSampleMean`
- mathlib의 `ProbabilityTheory.variance` 사용
- 정확한 유한시간 정리

  ```text
  (n+1) * Var[chainSampleMean n]
    = stationaryScaledVariance π P f n
  ```

- Phase 6a와 합성한 실제 variance-limit 정리

  ```text
  Tendsto (fun n => (n+1) * Var[chainSampleMean n])
    atTop (𝓝 (algebraicAsymptoticVariance ...))
  ```

완료 기준:

- `stationaryScaledVariance`가 더 이상 해석용 정의에 머물지 않고 실제
  probability measure의 variance와 Lean에서 동일시됨

### Phase 6b.4 — Probabilistic Peskun theorem

파일: `LeanMetro/ProbabilisticPeskun.lean`

- `HasSampleMeanAsymptoticVariance` predicate
- MH와 arbitrary admissible accept/reject kernel 각각의 실제 variance limit
- 기존 algebraic Peskun theorem으로 limit 값 ordering 합성
- 최종 정리:

  ```text
  metropolisHastings_minimizes_sampleMeanAsymptoticVariance
  ```

완료 기준:

- 두 kernel의 stationarity, Poisson invertibility, covariance decay가 모두
  정리문에 명시됨
- 실제 sample-mean variance limit 값과 그 Peskun ordering을 동시에 반환

### Phase 6b.5 — 회귀 예제와 릴리스

- 3상태 fast uniform kernel의 실제 sample-mean variance limit `2/3`
- 가능하면 2상태 또는 3상태 lazy kernel의 비자명한 decay 예제
- 한국어·영어 README, roadmap, theorem audit 갱신
- `lake build`, proof-placeholder 검사, `git diff --check`
- GitHub Actions 성공 후 `v1.1.0` 태그

## 4. 의존성

```text
FinitePath
  ↓
StationaryMoments
  ↓
SampleMeanVariance ← VarianceLimit
  ↓
ProbabilisticPeskun ← Peskun
```

## 5. 주장 경계

Phase 6b가 끝나면 실제 finite-horizon path probability measures와 그
sample-mean variance limit을 주장할 수 있다. 다만 하나의 무한 경로공간
위에서 모든 좌표과정을 동시에 구성하는 Kolmogorov-extension 정리는 이번
범위에 필수적이지 않다. 모든 `n`에 대한 일관된 finite-horizon law가
sample-mean 분산과 그 극한을 정의하기에 충분하며, 이 선택을 문서에
명시한다.

## 6. 완료 상태

- [x] `ChainPath`와 finite-horizon path PMF/measure
- [x] stationary current marginal과 cross/second moments
- [x] mathlib `ProbabilityTheory.variance`를 사용한 정확한 sample-mean identity
- [x] 실제 scaled variance의 조건부 극한
- [x] probabilistic Peskun 합성 정리
- [x] fast/lazy 3상태 회귀 예제 (`2/3` 대 `2`)

일반 irreducibility·aperiodicity에서 decay를 자동 도출하는 adapter와 하나의
무한 path space는 의도적으로 다음 범위에 남긴다.
