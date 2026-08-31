# LeanMetro theorem audit

## 표준 가정형 최종 정리

```text
metropolisHastings_minimizes_sampleMeanAsymptoticVariance_of_irreducible
```

고정된 target weight `w`와 proposal `q`에서 MH kernel과 임의 admissible
accept/reject competitor를 비교한다. 두 kernel 각각에 대해 실제 finite-path
probability measure 위 표본평균의 scaled variance 극한을 제공하고, MH의
극한값이 competitor의 극한값보다 크지 않음을 동시에 증명한다.

### 명시적 입력 가정

- 상태 타입은 유한하고 비어 있지 않다.
- 모든 target weight는 양수다.
- proposal entry는 비음수이고 각 행의 합은 1이다.
- 비교 acceptance rule은 `[0,1]`에 있고 accepted-flow detailed balance를
  만족한다.
- 생성된 MH kernel과 competitor kernel은 각각 finite irreducible이다.
- 관측량 `f`는 정규화된 target에 대해 mean-zero다.

호출자는 `MeanZeroPoissonInvertible`, covariance decay, aperiodicity, spectral
gap을 넘기지 않는다. 두 Poisson inverse는 normalized stationarity와
irreducibility에서 내부적으로 만들며, variance-limit remainder는
reversibility로 망원합한다.

## Lean에서 증명된 연결

```text
admissible acceptance
  ⇒ MH accepted-move maximality
  ⇒ off-diagonal Peskun domination
  ⇒ Dirichlet-form ordering
  ⇒ inverse-quadratic-form ordering
  ⇒ algebraic asymptotic-variance ordering

finite irreducibility + normalized stationarity
  ⇒ maximum principle
  ⇒ fixed points are constants
  ⇒ I-P is bijective on the mean-zero Submodule
  ⇒ centered Poisson inverse

reversibility + (I-P)g=f
  ⇒ <f,P^k g>π = <g,P^k g>π - <g,P^(k+1)g>π
  ⇒ Cesàro remainder = (c₁-cₙ₊₂)/(n+1)
  ⇒ finite stochastic bound로 remainder → 0

finite stationary path PMF/Measure
  ⇒ N * Var(actual sample mean) = stationaryScaledVariance
  ⇒ actual sample-mean asymptotic-variance Peskun ordering
```

표본 수는 항상 `N=n+1`이므로 0으로 나누는 경우가 없다. 경로의 초기분포는
`π`이고 이후 질량은 transition entry의 곱이다. 경로질량의 비음수성과 전체
합 1, `PMF.toMeasure`가 probability measure라는 사실까지 Lean이 검사한다.

## Telescoping이 제거한 가정

기존 저수준 정리는 다음 pointwise 조건을 받았다.

```text
<f, P^n g>π → 0
```

새 정리는 이것을 사용하지 않는다. `c_n=<g,P^n g>π`라고 하면 Lean이

```text
∑ k in range (n+1), <f,P^(k+1)g>π = c₁-cₙ₊₂
```

를 증명한다. finite Markov operator는 함수의 uniform absolute bound를
보존하므로 `c_n`은 uniformly bounded이고, endpoint 차이를 `n+1`로 나눈
값은 0으로 간다. 이 covariance-formula 단계에는 `π≥0`이나 `∑π=1`도
필요하지 않다. 두 조건은 실제 path probability measure를 만들 때만 쓴다.

## 유지되는 저수준 API

- `metropolisHastings_minimizes_sampleMeanAsymptoticVariance`: Poisson inverse와
  pointwise decay를 직접 받는 v1.2 호환 정리
- `metropolisHastings_minimizes_sampleMeanAsymptoticVariance_of_invertible`:
  Poisson inverse는 받지만 decay는 받지 않는 중간 정리
- `hasSampleMeanAsymptoticVariance_of_reversible`: 임의 normalized reversible
  kernel의 decay-free 실제 variance limit
- `hasSampleMeanAsymptoticVariance_of_irreducible`: inverse까지 내부 생성하는
  generic finite-kernel 정리

## 공리 의존성 감사

`LeanMetro/AxiomAudit.lean`은 `#guard_msgs in #print axioms`로 다음 경로를
각각 고정한다.

- 기존 conditional crown theorem
- decay-free reversible variance theorem
- irreducibility-facing crown theorem
- concrete `3/2 ≤ 6` end-to-end theorem
- periodic two-cycle의 actual variance-limit theorem

모든 결과는 다음 표준 Lean 공리만 사용한다.

```text
[propext, Classical.choice, Quot.sound]
```

`sorryAx`나 프로젝트 고유 공리가 추가되어 출력이 바뀌면 audit 모듈과 CI가
실패한다.

## 개발 중인 general-state crown theorem

```text
LeanMetroGeneral.referenceMH_largest_reversibleAcceptedFlow
```

이 정리는 아직 transition kernel이나 variance를 말하지 않는다. 임의의
measurable state space `X`, reference measure `μ`, proposal kernel `Q`, target
density `h : X → ℝ≥0∞`, acceptance `a : X → X → ℝ≥0∞`에서 다음을 입력으로
받는다.

- joint reference proposal flow `μ(dx)Q(x,dy)`가 swap-symmetric이다.
- `h`와 uncurried `a`가 measurable이다.
- 모든 `x,y`에서 `a(x,y) ≤ 1`이다. 비음수성은 codomain `ℝ≥0∞`에 내장된다.
- joint reference flow 거의 모든 `(x,y)`에서
  `h(x)a(x,y)=h(y)a(y,x)`이다.

그리고 다음을 증명한다.

```text
acceptedFlow μ Q h a is swap-symmetric
referenceMHAcceptedFlow μ Q h is swap-symmetric
acceptedFlow μ Q h a ≤ referenceMHAcceptedFlow μ Q h
```

마지막 부등식의 density는 정확히

```text
h(x)a(x,y) ≤ min(h(x),h(y))
```

이다. `LeanMetroGeneral/AxiomAudit.lean`은 이 정리가
`[propext, Classical.choice, Quot.sound]` 이외의 공리에 의존하지 않음을
고정한다. `FiniteAdapter.lean`의 첫 회귀 정리는 proposal이 대칭이고 모든
entry가 양수인 finite 특수화만 복원한다. zero proposal entry와 비대칭
proposal 전체를 복원하는 measure-common-part adapter는 아직 없다.

## 수치·경계 회귀 예제

- 2상태 MH/lazy: actual scaled-variance limits `3/2`, `6`, 그리고 `3/2 ≤ 6`
- 3상태 fast/lazy: actual limits `2/3`, `2`, 그리고 `2/3 < 2`
- deterministic two-cycle: Poisson covariance는 `(-1)^n/2`라서 0으로
  수렴하지 않지만 actual scaled variance는 0으로 수렴
- identity kernel: fixed functions가 상수뿐이라는 조건을 만족하지 않아
  Poisson inverse adapter에서 제외

`two_state_crown_actual_limits_and_order_of_irreducible`은 새 최종 wrapper를
직접 호출하며 `hinv`나 `hdecay`를 전달하지 않는다. periodic 예제는
aperiodicity가 sample-mean variance limit의 필요조건이 아님을 실제로
검증한다.

## 아직 주장하지 않는 것

- `P^n g → 0`의 pointwise 또는 norm convergence
- spectral gap에서 quantitative decay나 mixing rate를 도출하는 정리
- 하나의 무한 경로공간에서 모든 좌표과정을 동시에 구성하는 Kolmogorov
  extension
- Markov-chain central limit theorem 또는 분포수렴
- 임의 초기분포에서 stationary distribution으로의 convergence
- 일반 상태공간의 완성된 accept/reject MH transition kernel
- 일반 상태공간의 Dirichlet, Poisson, actual variance Peskun theorem
- Gaussian reference measure 위 무한차원 pCN crown theorem
- 부동소수점 sampler 구현의 수치적 정확성

따라서 완결된 variance 결과는 여전히 finite irreducible reversible MH와
irreducible admissible competitor의 실제 stationary sample-mean
asymptotic-variance Peskun ordering이다. general-state namespace의 현재 결과는
measure-level accepted-flow maximality까지이며, CLT, 무한 경로 variance,
mixing-rate 또는 pCN 정리가 아니다.
