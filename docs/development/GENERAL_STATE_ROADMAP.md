# Lean Metro general-state and pCN roadmap

## 1. 프로젝트 목표

finite-state `lean-metro`의 증명 사슬을 보존하면서 다음 두 이론층을 새로
형식화한다.

1. 임의의 measurable state space에서 Tierney--Peskun ordering을 증명한다.
2. 이 결과를 Gaussian reference measure 위의 무한차원 pCN proposal에
   적용한다.

최종 포트폴리오 문장은 다음을 목표로 한다.

> 유한 행렬의 Metropolis--Hastings correctness에서 출발해, 일반 measurable
> state space의 Peskun ordering을 거쳐, Gaussian measure 위 함수공간 pCN의
> 실제 stationary sample-mean asymptotic-variance optimality까지 Lean으로
> 검증한다.

여기서 optimality는 **같은 target과 같은 proposal을 사용하는 reversible
accept/reject 규칙 사이의 비교**다. pCN이 RWM, HMC 또는 서로 다른 proposal을
사용하는 모든 MCMC 알고리즘보다 최적이라는 뜻이 아니다.

## 2. 문헌과 mathlib 감사

### 2.1 원정리의 정확한 위치

Luke Tierney의 1998년 논문은 general measurable state space에서 detailed
balance를 product measure equality로 정의하고, general-state off-diagonal
domination에서 reversible kernel의 sample-path-average asymptotic variance
ordering을 도출한다.

- [Tierney, *A Note on Metropolis-Hastings Kernels for General State Spaces*
  (1998)](https://doi.org/10.1214/aoap/1027961031)

Tierney의 Theorem 4는 Poisson solution을 가정하는 정리보다 강하다. 가역 Markov
operator의 spectral representation과 resolvent를 사용하여 extended
asymptotic variance가 무한대인 경우까지 비교한다. 따라서 이 프로젝트의
Poisson 정리는 구현 가능한 중간 crown theorem이고, full Tierney theorem은
마지막 spectral/extended-real 단계다.

pCN의 함수공간 설정과 acceptance 식은 다음 논문을 기준으로 한다.

- [Cotter--Roberts--Stuart--White, *MCMC Methods for Functions* (2013)]
  (https://doi.org/10.1214/13-STS421)

해당 논문은 centered Gaussian reference measure `μ₀`를 보존하는 pCN proposal과

```text
v = sqrt(1 - β²) u + β ξ,   ξ ~ μ₀
α(u,v) = min(1, exp(Φ(u) - Φ(v)))
```

를 사용한다.

### 2.2 고정된 mathlib에서 확인한 기반

현재 저장소는 Lean `v4.33.1`, mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`를 고정한다. 이 revision에서 다음을
직접 확인했다.

- `Measure.compProd`, notation `μ ⊗ₘ κ`:
  `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean`
- deterministic `Kernel.swap`와 measurable `Prod.swap`:
  `Mathlib/Probability/Kernel/Basic.lean`
- `Kernel.withDensity`와 적분 공식:
  `Mathlib/Probability/Kernel/WithDensity.lean`
- `Measure.withDensity_mono`:
  `Mathlib/MeasureTheory/Measure/WithDensity.lean`
- measure의 `CompleteLattice`, 특히 `ν ⊓ νᵀ`:
  `Mathlib/MeasureTheory/Measure/MeasureSpace.lean`
- kernel Radon--Nikodym decomposition과 posterior/disintegration:
  `Mathlib/Probability/Kernel/RadonNikodym.lean`,
  `Mathlib/Probability/Kernel/Posterior.lean`
- Ionescu--Tulcea `trajMeasure`:
  `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean`
- centered Gaussian product measure의 rotation invariance와 Fernique theorem:
  `Mathlib/Probability/Distributions/Gaussian/Fernique.lean`

두 가지 adapter는 프로젝트에서 새로 증명해야 한다.

1. swap pushforward가 measure infimum을 보존한다는 involution 전용 lemma;
2. 공통 기준 measure `R` 아래
   `R.withDensity f ⊓ R.withDensity g = R.withDensity (f ⊓ g)` 형태의 density
   common-part lemma.

## 3. 저장소와 namespace 설계

새 저장소를 만들지 않고 현재 저장소에 독립 namespace를 추가한다.

이유:

- finite adapter가 기존 정리를 직접 재사용할 수 있다.
- 기존 8,000여 build job이 회귀검사 역할을 한다.
- finite 교육용 API와 general measure-theoretic API를 파일/namespace 수준에서
  분리할 수 있다.

```text
LeanMetroGeneral.lean
LeanMetroGeneral/
├── JointFlow.lean
├── Reversibility.lean
├── ReferenceProposal.lean
├── AcceptedFlow.lean
├── MetropolisHastings.lean
├── FiniteAdapter.lean
├── DirichletForm.lean
├── RawMarkovOperator.lean
├── L2MarkovOperator.lean
├── Poisson.lean
├── VarianceTelescope.lean
├── Trajectory.lean
├── SampleMeanVariance.lean
├── SpectralGap.lean
├── Tierney.lean
├── PCN.lean
├── PCNExample.lean
└── AxiomAudit.lean
```

namespace는 `LeanMetroGeneral`을 사용한다. 기존 `LeanMetro` 정의를 이름만 바꿔
복사하지 않는다. finite compatibility file만 두 namespace를 함께 import한다.

## 4. 가정의 단계적 사용

모든 파일에 처음부터 `StandardBorelSpace`를 요구하지 않는다.

| 층 | 최소 가정 |
|---|---|
| joint/reverse flow | `[MeasurableSpace X]` |
| `π ⊗ₘ Q` 계산 | `SFinite π`, `IsSFiniteKernel Q` |
| MH probability kernel | `IsProbabilityMeasure π`, `IsMarkovKernel Q` |
| conditional kernel/disintegration | `StandardBorelSpace X`, `Nonempty X` |
| infinite trajectory | Ionescu--Tulcea에 필요한 coordinate measurable spaces |
| L² theory | Borel real-valued functions, `MemLp`, stationary probability measure |
| pCN | separable complete real normed space, Borel structure, centered Gaussian measure |

`StandardBorelSpace`는 full Tierney accepted measure를 다시 kernel로 분해하거나
trajectory conditional distribution을 사용할 때 도입한다.

## 5. Phase G0--G4: 첫 general-state milestone

이 구간이 완료되기 전에는 L², Poisson, trajectory, pCN으로 넘어가지 않는다.

### G0 — 기반과 명명 고정

산출물:

- 이 계획 문서
- `LeanMetroGeneral.lean`
- 최소 smoke-test module
- source audit와 theorem-name map

완료 기준:

- [x] Tierney Theorem 4와 pCN 원문 범위 확인
- [x] 고정 mathlib의 compProd, swap, withDensity, measure inf, trajectory,
  Gaussian rotation API 확인
- [x] 새 root module이 단독 컴파일

### G1 — joint flow와 reversibility

파일:

- `JointFlow.lean`
- `Reversibility.lean`

정의:

```lean
proposalFlow (π : Measure X) (Q : Kernel X X) : Measure (X × X)
reverseFlow (ν : Measure (X × X)) : Measure (X × X)
FlowSymmetric (ν : Measure (X × X)) : Prop
ReversibleFor (π : Measure X) (P : Kernel X X) : Prop
StationaryFor (π : Measure X) (P : Kernel X X) : Prop
```

수학적 의미:

```text
proposalFlow π Q = π(dx) Q(x,dy)
reverseFlow ν = swap_# ν
ReversibleFor π P ↔ reverseFlow (proposalFlow π P) = proposalFlow π P
```

첫 정리:

```text
reverseFlow_reverseFlow
flowSymmetric_reverseFlow
reversibleFor_implies_stationaryFor
```

`reversibleFor_implies_stationaryFor`는 joint measure의 두 marginal이 같다는
사실로 증명한다. point probability를 사용하지 않는다.

G1 gate:

- [x] swap을 두 번 적용하면 원래 measure로 돌아옴
- [x] reversibility에서 stationarity 도출
- [x] equality가 필요한 곳과 `=ᵐ`가 필요한 곳을 구분

### G2 — reference-reversible proposal

파일:

- `ReferenceProposal.lean`

정의:

```lean
ReferenceReversible (μ : Measure X) (Q : Kernel X X) : Prop
referenceFlow μ Q := μ ⊗ₘ Q
targetFlow μ Q h := (referenceFlow μ Q).withDensity (fun z => h z.1)
```

`ReferenceReversible μ Q`는 `referenceFlow μ Q`가 swap-symmetric라는 뜻이다.
목표 density `h : X → ℝ≥0∞`에 대해 forward/reverse target flow는 공통 기준
measure `R = μ ⊗ₘ Q` 아래 각각 `h(x)`, `h(y)` density를 가진다는 것을
증명한다.

G2 gate:

- [x] `reverse_referenceTargetFlow` density 공식
- [x] `h` normalization과 probability target은 correctness layer에서만 요구
- [x] pCN이 나중에 바로 이 interface를 구현할 수 있는 signature

### G3 — accepted flow와 MH maximality

파일:

- `AcceptedFlow.lean`

첫 구현은 reference-density 버전이다.

```lean
acceptedFlow μ Q h a :=
  (referenceFlow μ Q).withDensity (fun z => h z.1 * a z.1 z.2)

referenceMHAcceptedFlow μ Q h :=
  (referenceFlow μ Q).withDensity (fun z => min (h z.1) (h z.2))
```

admissibility의 첫 안정된 API는 pointwise probability bound와 density-level
a.e. balance를 사용한다.

```text
0 ≤ a ≤ 1                    pointwise (`ℝ≥0∞`이므로 lower bound는 자동)
h(x)a(x,y)=h(y)a(y,x)       R-a.e.
```

이는 accepted-flow swap symmetry와 동치가 되도록 별도 theorem으로 연결한다.
처음부터 measure equality에서 density equality를 매번 복원하지 않는다.

핵심 증명:

```text
h(x)a(x,y) ≤ h(x)            because a≤1
h(x)a(x,y) = h(y)a(y,x) ≤ h(y)
therefore h(x)a(x,y) ≤ min(h(x),h(y))
```

그 뒤 `Measure.withDensity_mono`를 적용한다.

첫 crown theorem:

```lean
theorem referenceMH_acceptedFlow_maximal :
    acceptedFlow μ Q h a ≤ referenceMHAcceptedFlow μ Q h
```

G3 gate:

- [x] density balance와 비교를 joint reference flow에 대한 a.e. statement로 처리
- [x] competitor와 MH accepted-flow symmetry 증명
- [x] maximality theorem에 Poisson, irreducibility, spectral 가정 없음

### G4 — finite compatibility

파일:

- `FiniteAdapter.lean`

첫 adapter는 counting measure와 finite proposal kernel을 만들고, 대칭이며
모든 항이 양수인 proposal에서 density-level theorem이 기존
`mhAcceptedMove_maximal`의 reference-reversible 특수화를 복원함을 증명한다.
proposal zero를 포함한 대칭 a.e. adapter와 완전한 비대칭 복원은 각각 atom
계산과 G6의 common-part flow가 준비된 뒤 강화한다.

목표:

```text
finiteProposalKernel
finiteProposalKernel_referenceReversible
finite_admissibleAcceptance_to_general
finite_referenceMH_acceptedFlow_maximal
finite_referenceMH_largest_reversibleAcceptedFlow
general_reference_maximality_recovers_finite_mhAcceptedMove_maximal
```

처음부터 measure equality 전체를 기존 matrix 구조와 동일시하지 않는다.
현재 adapter는 실제 counting measure와 finite kernel을 사용해 proposal-flow
swap symmetry, 두 accepted-flow의 symmetry, flow inequality를 한 번에 닫고,
각 `(x,y)`에서 기존 accepted-move inequality도 함께 제공한다.

G4 gate:

- [x] min-density가 symmetric-positive finite case에서 기존 `min(A,B)` 계산으로 환원
- [x] 기존 finite API를 import하여 regression theorem 작성
- [x] 기존 `LeanMetro` 전체 build 유지 (`lake build`: 8,746 jobs)

## 6. Phase G5--G7: kernel correctness와 Dirichlet ordering

### G5 — accept/reject Markov kernel

파일:

- `MetropolisHastings.lean`

```text
Qacc(x,dy) = a(x,y) Q(x,dy)
r(x)       = 1 - Qacc(x,X)
Pa(x,dy)   = Qacc(x,dy) + r(x) δx(dy)
```

`Kernel.withDensity`로 accepted kernel을 만들고, measurable rejection mass와
Dirac stay-put kernel을 더한다.

목표 정리:

```text
acceptRejectKernel_isMarkov
acceptRejectKernel_reversible
acceptRejectKernel_stationary
referenceMHKernel_correct
referenceMHKernel_offDiagonalDominates
```

대각 singleton을 직접 제거하는 Tierney의 off-diagonal order는 singleton
measurability가 필요하다. accepted-flow ordering을 primary API로 두고,
measurable singleton/standard Borel 환경에서 kernel off-diagonal order를
corollary로 제공한다.

### G6 — measure common part와 full accepted-flow MH

reference version이 안정된 뒤 general proposal flow

```text
ν  = π ⊗ₘ Q
νᵀ = reverseFlow ν
```

에 대해

```text
maximalAcceptedFlow ν := ν ⊓ νᵀ
```

를 도입한다.

먼저 measure lattice 수준에서 다음을 증명한다.

```text
maximalAcceptedFlow_le_forward
maximalAcceptedFlow_le_reverse
maximalAcceptedFlow_symmetric
acceptedFlow_le_maximal
```

이 단계에서는 RN acceptance density나 transition kernel을 아직 복원하지 않아도
된다. `ν ⊓ νᵀ`의 universal property 자체가 maximality proof다.

### G7 — Dirichlet form ordering

파일:

- `DirichletForm.lean`

처음에는 raw measurable function과 joint flow 적분으로 정의한다.

```text
E_M(f) = 1/2 ∫ (f(x)-f(y))² dM(x,y)
```

accepted-flow ordering과 nonnegative integrand의 integral monotonicity로

```text
dirichletForm competitor f ≤ dirichletForm MH f
```

를 증명한다. 이 단계까지 Poisson solution, irreducibility, spectral gap은
필요하지 않다.

## 7. Phase G8--G10: L², Poisson, actual variance

### G8 — raw operator에서 L² operator로

파일:

- `RawMarkovOperator.lean`
- `L2MarkovOperator.lean`

먼저 대표함수 수준에서

```text
(Pf)(x) = ∫ f(y) ∂P(x)
```

를 정의하고 `MemLp`와 a.e. congruence 정리를 안정시킨다. 그 뒤에만
`Lp ℝ 2 π →L[ℝ] Lp ℝ 2 π`로 bundle한다.

목표:

- stationarity와 Jensen에서 L² contraction;
- reversibility에서 self-adjointness;
- `E_P(f)=<f,(I-P)f>`;
- centered closed subspace 보존.

가장 큰 Lean 공학 위험은 `Lp`가 a.e. equivalence class라는 점이다. 대표함수
선택과 적분 가능성 보조정리를 한 파일에 섞지 않는다.

### G9 — Poisson variational ordering

파일:

- `Poisson.lean`

무한차원에서는 injective `I-P`가 자동으로 surjective가 아니다. 따라서 첫
정리는 두 kernel에 centered Poisson solution이 있다고 가정한다.

```text
(I-P)g=f
F_P(h)=2<f,h>-<h,(I-P)h>
F_P(g)-F_P(h)=<g-h,(I-P)(g-h)> ≥ 0
```

Dirichlet ordering에서 variational supremum ordering을 얻고

```text
metropolisHastings_minimizes_algebraicAsymptoticVariance_of_poisson
```

을 증명한다. 전역 inverse operator를 만들지 않는다.

### G10 — Ionescu--Tulcea trajectory와 variance telescope

파일:

- `Trajectory.lean`
- `SampleMeanVariance.lean`
- `VarianceTelescope.lean`

`trajMeasure`는 history-dependent kernel family를 받으므로, homogeneous Markov
kernel `P : Kernel X X`를 이 interface로 올리는 adapter를 먼저 만든다.

무한 trajectory `ω : ℕ → X` 위 coordinate process를 사용해

```text
X_n(ω)=ω n
sampleMean N = (1/N) sum k<N, f(X_k)
```

를 정의한다. stationarity에서 lag covariance 공식을 얻고, finite v1.3과 같은
Poisson telescope를 사용한다.

L² contraction으로

```text
|<g,P^n g>| ≤ ||g||₂²
```

이므로 pointwise covariance decay와 aperiodicity 없이

```text
N * Var(sampleMean N) → 2<f,g> - ||f||₂²
```

를 증명한다.

## 8. Phase G11--G13: spectral adapter, pCN, full Tierney

### G11 — spectral-gap Poisson adapter

파일:

- `SpectralGap.lean`

centered L² 공간에서 `||P||≤ρ<1`이면 Neumann series

```text
g = sum' n, P^n f
```

가 수렴하고 `(I-P)g=f`임을 증명한다. MH와 competitor 각각에 gap이 필요하다.

### G12 — infinite-dimensional pCN

파일:

- `PCN.lean`
- `PCNExample.lean`

목표:

1. centered Gaussian probability measure `μ₀`와 pCN affine proposal kernel;
2. mathlib Gaussian product rotation invariance에서 `μ₀`-reversibility;
3. target density `h(u)=Z⁻¹ exp(-Φ(u))`;
4. acceptance density `min(1, exp(Φ(u)-Φ(v)))`;
5. reference-reversible MH maximality와 Dirichlet ordering 적용;
6. Poisson 또는 spectral-gap 가정 아래 actual variance crown theorem.

대표 정리의 정확한 claim:

```text
pCN_metropolisHastings_minimizes_sampleMeanAsymptoticVariance
```

동일한 pCN proposal과 target을 사용하는 admissible reversible acceptance
rules 사이의 비교다.

### G13 — full Tierney와 extended variance

파일:

- `Tierney.lean`
- `ExtendedVariance.lean`

1. `ν ⊓ νᵀ`의 RN density를 maximal acceptance로 복원;
2. general proposal에 대한 accept/reject kernel construction;
3. resolvent `(I-λP)⁻¹(I+λP)` for `0≤λ<1`;
4. spectral representation 또는 variational extended real quantity;
5. Poisson solution이 없고 variance가 무한대인 경우까지 ordering.

이 단계가 Tierney Theorem 4에 해당하는 최종 일반 정리다. pCN crown theorem을
끝내기 전에 이 난도를 선행시키지 않는다.

## 9. 릴리스 사다리

| 릴리스 | 완료선 |
|---|---|
| v2.0 | joint flow, reference reversibility, MH accepted-flow maximality, finite adapter |
| v2.1 | general accept/reject Markov kernel correctness와 stationarity |
| v2.2 | accepted-flow 및 Dirichlet/Peskun ordering |
| v2.3 | Poisson 가정 아래 actual trajectory sample-mean variance ordering |
| v2.4 | L² spectral-gap에서 Poisson solution 자동 생성 |
| v2.5 | infinite-dimensional Gaussian pCN crown theorem |
| v3.0 | full Tierney joint-measure/Radon--Nikodym MH construction |
| v3.1 | extended asymptotic variance와 Poisson 가정 제거 |

각 릴리스는 이전 릴리스를 깨지 않고 독립적인 theorem audit와 concrete
regression example을 가져야 한다.

현재 상태: v2.0 gate는 구현·전체 build·finite regression·공리 감사까지
완료되었다. 다음 구현 대상은 v2.1의 general accept/reject Markov kernel이다.

## 10. 첫 구현 배치

이번 `/goal`의 첫 concrete gate는 다음 네 작업이다.

1. `JointFlow.lean`: `proposalFlow`, `reverseFlow`, involution.
2. `Reversibility.lean`: flow symmetry, reversibility, stationarity.
3. `ReferenceProposal.lean`과 `AcceptedFlow.lean`: density-level accepted flow와
   `referenceMH_acceptedFlow_maximal`.
4. `FiniteAdapter.lean`: atom에서 현재 `min(A,B)` 정리를 복원.

이 네 작업이 모두 컴파일되기 전에는 L²나 pCN 파일을 만들지 않는다.

## 11. 검증과 claim gate

각 단계에서 다음을 수행한다.

```text
changed modules compile individually
lake build succeeds
no sorry/admit/user-declared axiom
git diff --check
relative Markdown links resolve
#print axioms guard for each public crown theorem
finite regression modules remain green
```

문서에서 항상 다음을 구분한다.

- product-measure equality로 증명한 reversibility;
- a.e. density identity로 증명한 reference-case balance;
- actual trajectory variance limit;
- Poisson 가정형 결과와 extended Tierney 결과;
- same-proposal acceptance optimality와 different-proposal algorithm comparison.

## 12. 주요 위험과 fallback

### Measure infimum

`Measure`에는 complete lattice가 있지만 swap map이 infimum을 보존하는 전용
lemma는 확인되지 않았다. swap이 measurable involution이라는 사실과
greatest-lower-bound universal property로 직접 증명한다.

### Accepted-flow equality와 density equality

첫 reference API는 a.e. density balance를 primary field로 사용하고 measure
symmetry를 theorem으로 제공한다. full Tierney 단계에서 RN uniqueness로
measure-level formulation과 동치를 증명한다.

### Lp engineering

곧바로 bundled continuous linear operator를 만들지 않는다. raw measurable
function + `MemLp` theorem을 먼저 안정화한 뒤 quotient-respecting operator로
올린다.

### pCN Gaussian proof

mathlib은 centered Gaussian product rotation invariance를 제공하지만, 임의의
`β`에 해당하는 정확한 affine map과 proposal kernel symmetry adapter는 새로
필요하다. 이 adapter가 닫히기 전에는 mesh-independent mixing rate를
주장하지 않는다.

### Claim boundary

v2.x에서 “general state”는 state type이 finite가 아니라는 뜻이지 자동으로
모든 Hilbert/Banach-space pCN 조건이 닫혔다는 뜻이 아니다. 진짜 무한차원
대표 예제는 pCN proposal, Gaussian reversibility, target density, variance
theorem이 한 end-to-end theorem에서 연결된 v2.5에서만 주장한다.
