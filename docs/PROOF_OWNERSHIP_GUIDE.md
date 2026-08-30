# Lean Metro 증명 소유권 가이드

이 문서는 코드를 외우기 위한 문서가 아니다. 다음 다섯 질문을 코드 없이
칠판에서 설명하고, 필요할 때 정확한 Lean 정리로 되돌아가기 위한 구두시험
가이드다.

각 절은 다음 순서로 읽으면 된다.

1. **60초 답변**을 소리 내어 말한다.
2. **5분 칠판 설명**을 식을 직접 쓰면서 재현한다.
3. **Lean 지도**에서 수학의 각 단계가 어느 파일과 정리에 들어 있는지 확인한다.
4. **자기점검 질문**에 코드를 보지 않고 답한다.

## 먼저 고정할 기호

- 상태공간은 유한집합 `S`다.
- `π(x)`는 stationary mass, `P(x,y)`는 transition probability다.
- 가중 내적은
  $$
  \langle f,g\rangle_\pi=\sum_x\pi(x)f(x)g(x)
  $$
  이다.
- Markov operator는
  $$
  (Pf)(x)=\sum_yP(x,y)f(y),
  $$
  Laplacian은 `L_P = I-P`다.
- Dirichlet form은
  $$
  \mathcal E_P(h)
  =\frac12\sum_{x,y}\pi(x)P(x,y)(h(x)-h(y))^2.
  $$
  가역성 아래에서는
  $$
  \mathcal E_P(h)=\langle h,(I-P)h\rangle_\pi
  $$
  다.
- `f`가 centered라는 말은
  $$
  \sum_x\pi(x)f(x)=0
  $$
  이라는 뜻이다.
- centered Poisson solution `g_P`는
  $$
  (I-P)g_P=f,
  \qquad \sum_x\pi(x)g_P(x)=0
  $$
  을 만족하는 유일한 함수다.

다섯 질문의 관계는 다음 한 줄로 기억하면 된다.

```text
MH accepted-flow 최대성
  → off-diagonal Peskun domination
  → Dirichlet form 증가
  → Poisson inverse quadratic form 감소
  → algebraic asymptotic variance 감소
  → finite-path variance identity와 decay를 통해 실제 표본평균 분산 극한 비교
```

여기서 irreducibility adapter는 Poisson inverse의 존재와 유일성을 공급한다.
아직 일반 정리로 남아 있는 spectral adapter는 covariance decay를 공급해야 한다.

---

## 1. 왜 `mhAcceptedMove_maximal`이 성립하는가?

### 60초 답변

상태 `x`에서 `y`로 가는 두 방향의 proposal flow를

$$
A=w(x)q(x,y),\qquad B=w(y)q(y,x)
$$

라고 두자. 임의의 admissible acceptance rule을 `a`라고 하면 그 규칙의
가중 accepted flow는 `F=Aa(x,y)`다. `a(x,y)≤1`이므로 `F≤A`다. 또 detailed
balance로 `F=Ba(y,x)`이고 `a(y,x)≤1`이므로 `F≤B`다. 따라서

$$
F\le \min(A,B).
$$

MH acceptance는 정확히 이 상한을 달성한다.

$$
A\min(1,B/A)=\min(A,B).
$$

그러므로 가중 accepted flow에서 MH가 최대이고, `w(x)>0`이므로 `w(x)`를
제거해 실제 accepted move `q(x,y)a(x,y)`도 MH보다 클 수 없다고 결론낸다.
이 증명은 `A=0`이어도 성립하도록 별도의 zero-safe 항등식을 사용한다.

### 5분 칠판 설명

#### 1단계: 비교 대상이 만족해야 할 조건

임의의 acceptance rule `a(x,y)`에 다음 세 조건을 요구한다.

$$
0\le a(x,y)\le1,
$$

$$
w(x)q(x,y)a(x,y)=w(y)q(y,x)a(y,x).
$$

마지막 식은 accepted probability flow의 detailed balance다. 아무 acceptance
rule이나 MH와 비교하는 것이 아니라, 같은 target과 proposal을 사용하면서
이 balance를 보존하는 규칙과 비교한다.

#### 2단계: 두 개의 상한

`F=Aa(x,y)`라 두면

$$
F\le A
$$

는 `a(x,y)≤1`에서 바로 나온다. 반대 방향 balance를 사용하면

$$
F=Ba(y,x)\le B
$$

도 얻는다. 둘을 합치면

$$
F\le\min(A,B).
$$

여기서 반대 방향 acceptance가 필요한 이유가 보인다. `F≤A`만으로는
target 쪽에서 허용하는 역방향 flow `B`를 넘지 못한다는 사실을 알 수 없다.

#### 3단계: MH가 상한을 정확히 채운다

MH acceptance는

$$
\alpha_{MH}(x,y)=\min\left(1,\frac{B}{A}\right)
$$

이므로 가중 accepted flow는

$$
A\alpha_{MH}(x,y)=A\min(1,B/A)=\min(A,B).
$$

`A>0`인 경우에는 `A≤B`와 `B<A`로 나누면 익숙한 계산이 된다. 하지만
proposal이 0일 수 있으므로 `A=0`도 처리해야 한다. 프로젝트의
`nonneg_mul_acceptance_eq_min`은 `A,B≥0`만으로 위 식을 증명해 영점에서의
나눗셈 문제를 닫는다.

#### 4단계: 가중 flow에서 transition으로

지금까지 얻은 것은

$$
w(x)q(x,y)a(x,y)
\le
w(x)q(x,y)\alpha_{MH}(x,y).
$$

이다. `w(x)>0`이므로 양변에서 양의 인자를 제거할 수 있다.

$$
q(x,y)a(x,y)
\le
q(x,y)\alpha_{MH}(x,y).
$$

이것이 `mhAcceptedMove_maximal`의 결론이다. 이후 `x≠y`이면 transition의
off-diagonal entry가 accepted move와 같으므로 Peskun domination으로 이어진다.

### Lean 지도

| 수학 단계 | Lean 이름 | 파일 |
|---|---|---|
| admissible rule의 범위와 balance | `AdmissibleAcceptance` | `LeanMetro/AcceptanceRule.lean` |
| generic accepted move `q*a` | `acceptRejectAcceptedMove` | `LeanMetro/AcceptanceRule.lean` |
| MH acceptance와 accepted move | `mhAsymmetricAcceptance`, `mhAsymmetricAcceptedMove` | `LeanMetro/Asymmetric.lean` |
| 영점을 포함한 `A α = min A B` | `nonneg_mul_acceptance_eq_min` | `LeanMetro/Asymmetric.lean` |
| MH accepted move 최대성 | `mhAcceptedMove_maximal` | `LeanMetro/AcceptanceRule.lean` |
| off-diagonal transition 비교 | `mhTransition_offDiagonal_dominates` | `LeanMetro/AcceptanceRule.lean` |
| kernel 수준 Peskun domination | `metropolisHastingsKernel_peskunDominates` | `LeanMetro/MarkovKernel.lean` |

코드에서 눈여겨볼 점은 마지막 양의 인자 제거를 억지로 나눗셈 rewrite로 하지
않고, `hw x`와 가중 부등식을 `nlinarith`에 주어 닫는다는 것이다.

### 현재 증명 경계

- 이 정리는 비대칭 proposal과 proposal entry가 0인 경우까지 다룬다.
- 비교 대상은 `AdmissibleAcceptance` 조건을 만족해야 한다.
- `mhAcceptedMove_maximal` 자체는 전체 transition의 대각항이 크다고 말하지
  않는다. Peskun order는 off-diagonal entry만 비교한다.
- 이 단계만으로 분산 비교가 끝나는 것은 아니다. Dirichlet form과 Poisson
  inverse를 거쳐야 한다.

### 자기점검 질문

1. `F≤A`만으로 충분하지 않고 `F≤B`도 필요한 이유는 무엇인가?
2. detailed balance가 없으면 어느 부등식을 잃는가?
3. `q(x,y)=0`일 때 `B/A`가 등장해도 증명이 안전한 이유는 무엇인가?
4. accepted move의 최대성과 대각 transition의 최대성이 같은 말이 아닌 이유는
   무엇인가?
5. `w(x)>0` 대신 `w(x)≥0`만 알면 마지막 단계가 왜 실패할 수 있는가?

---

## 2. `inverseQuadraticForm_mono_of_peskunDominates`의 분해는 왜 작동하는가?

### 60초 답변

`P₁`이 `P₂`를 Peskun-dominate하고, `g₁,g₂`가 각각

$$
(I-P_1)g_1=f,\qquad (I-P_2)g_2=f
$$

를 푼다고 하자. 증명의 핵심은 다음 항등식이다.

$$
\mathcal E_{P_2}(g_2-g_1)
+\bigl(\mathcal E_{P_1}(g_1)-\mathcal E_{P_2}(g_1)\bigr)
=\langle f,g_2\rangle_\pi-\langle f,g_1\rangle_\pi.
$$

왼쪽 첫 항은 Dirichlet form이므로 0 이상이다. 둘째 항은 `P₁`의
off-diagonal transition이 더 커서 Dirichlet form도 더 크기 때문에 0 이상이다.
따라서 오른쪽도 0 이상이고

$$
\langle f,(I-P_1)^{-1}f\rangle_\pi
\le
\langle f,(I-P_2)^{-1}f\rangle_\pi
$$

를 얻는다. 분해를 전개할 때 가역성이 `I-P₂`의 자기수반성을 주고, Poisson
방정식이 교차항을 `⟨f,g₁⟩`로 바꿔 준다.

### 5분 칠판 설명

#### 1단계: 방향을 먼저 확인한다

`P₁`이 `P₂`를 Peskun-dominate한다는 것은 `x≠y`일 때

$$
P_2(x,y)\le P_1(x,y)
$$

라는 뜻이다. Dirichlet form의 각 off-diagonal summand에는
`P(x,y)(h(x)-h(y))²`가 들어 있으므로

$$
\mathcal E_{P_2}(h)\le\mathcal E_{P_1}(h)
$$

이다. kernel이 더 잘 움직일수록 Dirichlet form은 커지고, inverse quadratic
form과 asymptotic variance는 작아지는 방향이다.

#### 2단계: 두 Poisson 해를 둔다

$$
L_1=I-P_1,\qquad L_2=I-P_2,
$$

$$
L_1g_1=f,\qquad L_2g_2=f.
$$

목표는

$$
\langle f,g_1\rangle_\pi\le\langle f,g_2\rangle_\pi
$$

다. inverse 기호를 직접 조작하는 대신 선택된 centered Poisson solution을
사용한다.

#### 3단계: 명백히 비음수인 두 양을 만든다

첫 번째 양은

$$
D_1=\mathcal E_{P_2}(g_2-g_1)\ge0.
$$

이는 `π(x)≥0`, `P₂(x,y)≥0`, 제곱의 비음수성만 사용한다.

두 번째 양은

$$
D_2=\mathcal E_{P_1}(g_1)-\mathcal E_{P_2}(g_1)\ge0.
$$

이고, Peskun domination에서 나온다. 따라서 `D₁+D₂≥0`이다.

#### 4단계: `D₁+D₂`를 전개한다

가역성 아래에서 `\mathcal E_{P_2}(u)=\langle u,L_2u\rangle_π`이고,
polarization을 쓰면

$$
\begin{aligned}
\mathcal E_{P_2}(g_2-g_1)
={}&\mathcal E_{P_2}(g_2)+\mathcal E_{P_2}(g_1)\\
&-\langle g_2,L_2g_1\rangle_\pi
-\langle g_1,L_2g_2\rangle_\pi.
\end{aligned}
$$

각 항을 바꿔 보자.

$$
\mathcal E_{P_2}(g_2)
=\langle g_2,L_2g_2\rangle_\pi
=\langle f,g_2\rangle_\pi.
$$

자기수반성과 `L₂g₂=f`를 사용하면

$$
\langle g_2,L_2g_1\rangle_\pi
=\langle L_2g_2,g_1\rangle_\pi
=\langle f,g_1\rangle_\pi.
$$

다른 교차항도

$$
\langle g_1,L_2g_2\rangle_\pi
=\langle g_1,f\rangle_\pi
=\langle f,g_1\rangle_\pi
$$

다. 마지막으로 `L₁g₁=f`이므로

$$
\mathcal E_{P_1}(g_1)=\langle f,g_1\rangle_\pi.
$$

`D₁`의 `+E_{P₂}(g₁)`와 `D₂`의 `-E_{P₂}(g₁)`가 지워지고, `⟨f,g₁⟩`도
하나만 남는다. 결과는 정확히

$$
D_1+D_2=\langle f,g_2\rangle_\pi-\langle f,g_1\rangle_\pi
$$

다.

#### 5단계: asymptotic variance로 옮긴다

프로젝트의 algebraic asymptotic variance는

$$
\sigma_P^2(f)=2\langle f,g_P\rangle_\pi-\langle f,f\rangle_\pi
$$

다. 두 kernel에서 `f`와 `π`가 같으므로 마지막 `⟨f,f⟩` 항은 공통이다.
따라서 inverse quadratic form ordering이 그대로 asymptotic-variance ordering이
된다.

### Lean 지도

| 수학 단계 | Lean 이름 | 파일 |
|---|---|---|
| Dirichlet form 정의 | `dirichletForm` | `LeanMetro/DirichletForm.lean` |
| `E_P(h)=⟨h,(I-P)h⟩` | `dirichletForm_eq_weightedInner_laplacian` | `LeanMetro/MeanZero.lean` |
| Peskun order가 Dirichlet form을 키움 | `dirichletForm_mono_of_peskunDominates` | `LeanMetro/DirichletForm.lean` |
| Laplacian 자기수반성 | `weightedInner_laplacian_selfAdjoint` | `LeanMetro/AsymptoticVariance.lean` |
| `E_P(g₂-g₁)` polarization | `dirichletForm_sub` | `LeanMetro/AsymptoticVariance.lean` |
| Dirichlet form 비음수 | `dirichletForm_nonneg` | `LeanMetro/AsymptoticVariance.lean` |
| 중앙 inverse ordering | `inverseQuadraticForm_mono_of_peskunDominates` | `LeanMetro/AsymptoticVariance.lean` |
| algebraic variance ordering | `algebraicAsymptoticVariance_mono_of_peskunDominates` | `LeanMetro/AsymptoticVariance.lean` |

`inverseQuadraticForm_mono_of_peskunDominates` 안의 핵심 지역 명제는
`hdiff_nonneg`, `horder`, `hcross₂₁`, `hcross₁₂`, `hdecomposition`,
`hnonneg`다. 이름의 순서가 위 칠판 증명과 거의 일치한다.

### 현재 증명 경계

- 이 비교 정리는 두 kernel 모두 `π`에 대해 reversible이라고 가정한다.
  가역성이 없으면 사용한 자기수반성 식이 바로 성립하지 않는다.
- 두 centered Poisson inverse의 존재와 유일성은 theorem parameter다. 다만
  현재 저장소에는 finite irreducibility로 이 parameter를 만드는 adapter가
  별도 정리로 추가되어 있다.
- 이 정리는 covariance decay나 실제 표본평균의 극한을 직접 말하지 않는다.
  그 연결은 `VarianceLimit.lean`과 `SampleMeanVariance.lean`에서 한다.

### 자기점검 질문

1. `P₁`이 더 큰 kernel일 때 왜 `E_{P₁}`은 더 크고 inverse form은 더 작은가?
2. 분해의 두 비음수 항을 식으로 정확히 쓸 수 있는가?
3. 첫 항을 `E_{P₁}(g₂-g₁)`가 아니라 `E_{P₂}(g₂-g₁)`로 잡은 이유는
   무엇인가?
4. `⟨g₂,L₂g₁⟩=⟨f,g₁⟩`에서 쓰인 두 사실은 무엇인가?
5. 두 kernel의 observable이 서로 다르면 마지막 variance 비교가 왜 그대로
   나오지 않는가?

---

## 3. normalized stationary finite chain에서 irreducibility는 왜 Poisson invertibility를 주는가?

### 60초 답변

centered 함수들의 공간을 `H₀={f:⟨1,f⟩π=0}`라고 하자. 상태공간이
유한하므로 `H₀`도 유한차원이다. Stationarity 때문에 `L=I-P`는 `H₀`를
자기 자신으로 보낸다. Irreducibility의 maximum principle에 따르면 `Ph=h`인
함수는 상수뿐이다. 따라서 `Lh=0`이고 `h∈H₀`이면 `h`는 상수이면서 평균이
0이므로 `h=0`이다. 즉 `L:H₀→H₀`는 injective다. 유한차원 endomorphism에서는
injective이면 surjective이므로 모든 centered `f`에 대해 `Lg=f`인 centered
`g`가 존재한다. Injectivity가 uniqueness도 주므로 centered Poisson inverse가
생긴다.

현재 저장소는 이 adapter를 `meanZeroPoissonInvertible_of_irreducible`로 실제
증명한다. 따라서 평가 당시 지적된 Poisson-invertibility 공백은 현재 작업
트리에서는 닫혔다. 다만 covariance decay adapter까지 닫힌 것은 아니다.

### 5분 칠판 설명

#### 1단계: centered subspace를 만든다

$$
H_0=\left\{h:S\to\mathbb R:\sum_x\pi(x)h(x)=0\right\}.
$$

이는 덧셈과 scalar multiplication에 닫힌 선형부분공간이다. `S`가 유한하므로
전체 함수공간 `ℝ^S`와 그 부분공간 `H₀`는 유한차원이다.

#### 2단계: `I-P`가 centeredness를 보존한다

`πP=π`이면

$$
\sum_x\pi(x)(Ph)(x)=\sum_x\pi(x)h(x).
$$

따라서

$$
\sum_x\pi(x)((I-P)h)(x)=0.
$$

즉 `L=I-P`를 `H₀→H₀`인 linear map으로 제한할 수 있다. Irreducibility만으로
이 단계가 나오는 것이 아니라 stationarity가 필요하다.

#### 3단계: irreducibility로 fixed point를 분류한다

`Ph=h`인 함수 `h`를 잡고 `h`가 최대가 되는 상태 `x₀`를 고른다. 그러면

$$
0=h(x_0)-(Ph)(x_0)
=\sum_yP(x_0,y)(h(x_0)-h(y)).
$$

합의 각 항은 0 이상이다. 따라서 `P(x₀,y)>0`인 모든 `y`에 대해
`h(y)=h(x₀)`다. 같은 논리를 positive-probability path를 따라 반복한다.
Irreducibility는 `x₀`에서 모든 `y`로 그런 path가 있음을 보장하므로 `h`는
전체 상태공간에서 상수다.

#### 4단계: kernel이 자명함을 보인다

`Lh=0`이면 `Ph=h`이므로 방금 결과에 따라 `h(x)=c`다. 그런데 `h∈H₀`이고
`∑x π(x)=1`이므로

$$
0=\sum_x\pi(x)c=c.
$$

따라서 `h=0`이다. 더 일반적으로 `Lf=Lg`이면 `L(f-g)=0`이므로 `f=g`다.
즉 `L:H₀→H₀`는 injective다.

#### 5단계: 유한차원성을 딱 한 번 사용한다

무한차원에서는 injective linear map이 surjective일 필요가 없다. 그러나
유한차원 endomorphism에서는 rank-nullity에 의해 둘이 동치다. 그러므로

$$
L:H_0\to H_0
$$

는 surjective이고, 모든 centered `f`에 대해 centered solution `g`가 존재한다.
Injectivity는 그 solution이 유일함도 보장한다. 이것이
`MeanZeroPoissonInvertible π P`의 두 필드인 existence와 uniqueness다.

### Lean 지도

| 수학 단계 | Lean 이름 | 파일 |
|---|---|---|
| centered 함수 부분공간 | `meanZeroSubmodule` | `LeanMetro/Irreducibility.lean` |
| 전체 함수공간의 `I-P` linear map | `laplacianLinearMap` | `LeanMetro/Irreducibility.lean` |
| `H₀→H₀` 제한 | `meanZeroLaplacianLinearMap` | `LeanMetro/Irreducibility.lean` |
| mathlib matrix irreducibility와 연결 | `FiniteKernel.Irreducible` | `LeanMetro/Irreducibility.lean` |
| maximum principle | `fixedPointsAreConstants_of_irreducible` | `LeanMetro/Irreducibility.lean` |
| centered restriction의 injectivity | `laplacianOperator_injective_on_meanZero` | `LeanMetro/MeanZero.lean` |
| injective `⇒` surjective | `meanZeroPoissonSolvable_of_fixedPoints` | `LeanMetro/Irreducibility.lean` |
| fixed-point 조건에서 inverse 구성 | `meanZeroPoissonInvertible_of_fixedPoints` | `LeanMetro/Irreducibility.lean` |
| irreducibility에서 최종 adapter | `meanZeroPoissonInvertible_of_irreducible` | `LeanMetro/Irreducibility.lean` |

Lean 코드에서 유한차원 핵심 한 줄은
`LinearMap.surjective_of_injective hL_injective`다. 그 전에 submodule과 restricted
linear map을 만들었기 때문에 mathlib의 표준 유한차원 정리를 사용할 수 있다.

### 현재 증명 경계

- 현재 `FiniteKernel.Irreducible`은 mathlib의 `Matrix.IsIrreducible`을 사용하며,
  strictly positive transition edge의 quiver가 strongly connected라는 뜻이다.
- 정리는 finite state, normalized stationary mass, stationarity를 요구한다.
- 이 adapter는 Poisson solution의 존재와 유일성을 닫지만 `Pⁿg→0`이나
  covariance decay는 닫지 않는다.
- irreducible만으로 decay는 충분하지 않다. 예를 들어 deterministic two-cycle은
  irreducible이지만 period가 2이고 eigenvalue `-1` 때문에 진동할 수 있다.

### 자기점검 질문

1. stationarity는 `I-P`가 `H₀`를 보존하는 어느 계산에 쓰이는가?
2. maximum principle에서 합의 각 항이 비음수인 이유는 무엇인가?
3. irreducibility는 maximum value가 모든 상태로 전파되는 데 어떻게 쓰이는가?
4. fixed point가 상수라는 사실만으로 왜 centered fixed point가 0인가?
5. injective에서 surjective로 넘어갈 때 유한 상태성이 정확히 어디에 쓰이는가?
6. irreducibility가 Poisson invertibility에는 충분하지만 covariance decay에는
   충분하지 않은 예를 들 수 있는가?

---

## 4. aperiodicity 또는 spectral gap은 왜 covariance decay를 주는가?

### 60초 답변

finite reversible chain에서 `P`는 `L²(π)`의 self-adjoint operator다. 따라서
orthonormal eigenbasis를 갖고 eigenvalue는 실수다. Irreducibility는 eigenvalue
`1`의 eigenspace가 상수함수뿐임을 보장한다. Centered subspace에서는 그
상수방향이 제거된다. Aperiodicity까지 있으면 나머지 eigenvalue는 모두

$$
|\lambda_i|<1
$$

이고, 유한개이므로 `ρ=max |λᵢ|<1`이다. 따라서 centered Poisson solution을
`g=∑cᵢeᵢ`로 쓰면

$$
P^ng=\sum_i c_i\lambda_i^n e_i\to0.
$$

Cauchy–Schwarz로 `|⟨f,Pⁿg⟩π|≤‖f‖π‖Pⁿg‖π→0`이므로 프로젝트가 요구하는
covariance decay가 나온다. 여기서 필요한 것은 보통 gap `1-λ₂`만이 아니라
negative eigenvalue까지 제어하는 **absolute spectral gap**이다.

이 논증은 현재 프로젝트의 다음 자연스러운 adapter 설계지만, 일반 theorem으로
아직 Lean에 들어 있지 않다. 현재 crown theorem은 decay를 명시적 parameter로
받고, 구체 예제에서는 geometric formula를 직접 증명해 그 parameter를 닫는다.

### 5분 칠판 설명

#### 1단계: 왜 reversibility가 spectral argument를 가능하게 하는가

Detailed balance

$$
\pi(x)P(x,y)=\pi(y)P(y,x)
$$

를 쓰면

$$
\langle f,Pg\rangle_\pi=\langle Pf,g\rangle_\pi.
$$

즉 `P`는 weighted inner product에서 self-adjoint다. `π(x)>0`이면 이 weighted
form은 실제 inner product가 되고, finite-dimensional spectral theorem을 적용할
수 있다.

#### 2단계: eigenvalue `1` 방향을 제거한다

Markov kernel은 `P1=1`을 만족하므로 상수함수는 eigenvalue `1`의 eigenvector다.
Irreducibility의 maximum principle은 `Ph=h`인 함수가 상수뿐이라고 말한다.
따라서 `1`-eigenspace는 정확히 상수방향이고, centered subspace `H₀`에는 이
방향이 남지 않는다.

#### 3단계: 왜 aperiodicity가 필요한가

Irreducible이기만 한 chain에는 modulus가 1인 다른 eigenvalue가 있을 수 있다.
reversible chain에서는 대표적으로 `-1`이 문제다. 두 상태를 매번 번갈아 가는
chain은 `Pⁿg=(-1)ⁿg`처럼 진동하므로 0으로 가지 않는다.

finite irreducible aperiodic chain에서는 `1` 이외의 peripheral eigenvalue가
없다. Reversible이라 eigenvalue가 실수이므로 centered subspace의 모든
eigenvalue가 `(-1,1)` 안에 놓인다. eigenvalue가 유한개라

$$
\rho=\max_{\lambda_i\ne1}|\lambda_i|<1
$$

을 잡을 수 있다.

#### 4단계: geometric decay

centered `g`를 eigenbasis로 전개하면

$$
g=\sum_i c_ie_i,
\qquad
P^ng=\sum_i c_i\lambda_i^ne_i.
$$

따라서

$$
\|P^ng\|_\pi^2
=\sum_i c_i^2|\lambda_i|^{2n}
\le\rho^{2n}\|g\|_\pi^2.
$$

그리고

$$
|\langle f,P^ng\rangle_\pi|
\le\|f\|_\pi\|P^ng\|_\pi
\le\|f\|_\pi\|g\|_\pi\rho^n\to0.
$$

이 마지막 결론이 `stationaryScaledVariance_tendsto_...`가 받는 `hdecay`와
정확히 같은 형태다.

#### 5단계: “spectral gap”이라는 말을 조심한다

일부 문헌의 spectral gap은 `1-λ₂`만 뜻한다. 이것만으로는 `λ=-1`을 막지
못한다. 여기서 바로 필요한 양은

$$
1-\max_{i\ge2}|\lambda_i|,
$$

즉 absolute spectral gap이다. 또는 finite irreducibility와 aperiodicity를 함께
사용해 모든 nonconstant eigenvalue의 절댓값이 1보다 작음을 도출해야 한다.

### Lean 지도

현재 **이미 있는 조각**은 다음과 같다.

| 역할 | Lean 이름 | 파일 |
|---|---|---|
| Markov iterate `Pⁿ` | `markovIterate` | `LeanMetro/VarianceLimit.lean` |
| 요구되는 decay 형태 | `stationaryScaledVariance_tendsto_algebraicAsymptoticVariance`의 `hdecay` | `LeanMetro/VarianceLimit.lean` |
| 실제 variance limit에서 같은 가정 사용 | `chainSampleMean_scaledVariance_tendsto` | `LeanMetro/SampleMeanVariance.lean` |
| 최종 비교에서 양쪽 decay 가정 | `metropolisHastings_minimizes_sampleMeanAsymptoticVariance` | `LeanMetro/ProbabilisticPeskun.lean` |
| 구체적 geometric iterate | `two_state_mh_iterate_solution`, `two_state_competitor_iterate_solution` | `LeanMetro/CrownExample.lean` |
| 구체적 decay discharge | `two_state_crown_mh_poisson_covariance_tendsto_zero`, `two_state_crown_competitor_poisson_covariance_tendsto_zero` | `LeanMetro/CrownExample.lean` |

현재 **아직 없는 일반 adapter**는 다음 사슬이다.

```text
finite + π>0 + reversible + irreducible + aperiodic
  → P is self-adjoint on weighted L²(π)
  → 1-eigenspace is constants
  → every centered eigenvalue has absolute value < 1
  → geometric norm bound for Pⁿ on H₀
  → ⟨f, Pⁿg⟩π → 0
```

### 현재 증명 경계

- 일반적인 `aperiodic → covariance decay` theorem은 아직 증명하지 않았다.
- 구체 예제의 decay는 행렬에 대한 일반 spectral theorem을 호출한 것이 아니라,
  `Pⁿg=c λⁿg`를 직접 귀납하고 실수 geometric sequence의 극한을 사용한다.
- Markov-chain CLT, mixing-time bound, convergence rate의 일반 이론은 없다.
- decay는 실제 최종 theorem에서 숨겨진 가정이 아니라 `hdecayMH`, `hdecayA`로
  드러난 parameter다.

### 자기점검 질문

1. reversibility는 `P`의 어떤 operator 성질로 번역되는가?
2. irreducibility와 aperiodicity는 각각 spectrum의 어떤 문제를 없애는가?
3. deterministic two-cycle이 decay의 반례가 되는 이유는 무엇인가?
4. ordinary spectral gap과 absolute spectral gap의 차이는 무엇인가?
5. `Pⁿg→0`에서 `⟨f,Pⁿg⟩→0`으로 가는 부등식은 무엇인가?
6. 현재 예제의 geometric proof와 아직 없는 일반 spectral adapter의 차이를
   설명할 수 있는가?

---

## 5. horizon마다 probability space가 달라도 왜 variance limit을 말할 수 있는가?

### 60초 답변

각 `n`에 대해 길이 `n+1`인 path들의 유한 확률공간

$$
\Omega_n=S^{n+1},
\qquad
\mu_n(x_0,\ldots,x_n)
=\pi(x_0)\prod_{t=0}^{n-1}P(x_t,x_{t+1})
$$

를 따로 만든다. 그 공간 위 sample mean `\bar f_{n+1}`의 variance는 실수 하나다.
그러므로

$$
a_n=(n+1)\operatorname{Var}_{\mu_n}(\bar f_{n+1})
$$

는 확률공간이 n마다 달라도 평범한 실수열 `a:ℕ→ℝ`이다. `Tendsto a`를 말하는
데 모든 random variable이 같은 `Ω` 위에 있을 필요는 없다. 프로젝트는 각
finite horizon에서 exact covariance identity를 증명하고, 남는 Cesàro remainder가
0으로 가는 것을 이용해 이 실수열의 극한을 증명한다.

대신 하나의 infinite path process를 만든 것은 아니므로, 모든 n을 동시에
포함하는 사건, almost-sure convergence, filtration, stopping time, Markov-chain
CLT를 증명했다고 말하면 안 된다.

### 5분 칠판 설명

#### 1단계: horizon별 실제 확률측도

`N=n+1`이라 두고 path를 `(x₀,…,xₙ)`라 하자. 질량은

$$
\mu_n(x_0,\ldots,x_n)
=\pi(x_0)P(x_0,x_1)\cdots P(x_{n-1},x_n).
$$

각 항이 비음수이고, 마지막 상태부터 차례로 row sum `1`을 사용하면 전체
path에 대한 질량 합도 `1`이다. 따라서 이는 이름만 확률인 함수가 아니라 실제
`PMF`, `Measure`, `IsProbabilityMeasure`가 된다.

#### 2단계: 각 공간 위의 실제 random variable

$$
\bar f_N(x_0,\ldots,x_n)
=\frac1N\sum_{t=0}^{n}f(x_t).
$$

프로젝트는 이 함수에 mathlib의 `ProbabilityTheory.variance`를 적용한다.
stationary initialization과 `f`의 centeredness를 사용하면 평균은 0이고,
second moment를 lag covariance의 합으로 전개할 수 있다.

#### 3단계: exact finite-time identity

프로젝트가 증명하는 핵심 식은

$$
N\operatorname{Var}_{\mu_n}(\bar f_N)
=\texttt{stationaryScaledVariance}(n).
$$

이는 정의가 아니라 theorem이다. 왼쪽은 실제 path measure 위의 실제 variance고,
오른쪽은 stationary covariance를 유한합으로 쓴 식이다.

#### 4단계: Poisson 식과 remainder

`g`가 `(I-P)g=f`를 풀면 exact telescoping으로

$$
\texttt{stationaryScaledVariance}(n)
=\sigma^2_{alg}
-\frac{2}{N}\sum_{k=0}^{N-1}
  \langle f,P^{k+1}g\rangle_\pi,
$$

$$
\sigma^2_{alg}=2\langle f,g\rangle_\pi-\langle f,f\rangle_\pi
$$

를 얻는다. `d_k=⟨f,P^kg⟩π→0`이면 Cesàro 평균도 0으로 가므로

$$
N\operatorname{Var}_{\mu_n}(\bar f_N)\to\sigma^2_{alg}.
$$

#### 5단계: 공통 sample space가 필요 없는 이유와 필요한 경우

수열의 각 항은 계산이 끝난 실수다.

$$
\operatorname{Var}_{\mu_0}(\bar f_1),
\operatorname{Var}_{\mu_1}(\bar f_2),
\operatorname{Var}_{\mu_2}(\bar f_3),\ldots
$$

서로 다른 공간에서 얻은 적분값이어도 모두 `ℝ`에 있으므로 그 수렴을 비교할
수 있다. 반면 “거의 모든 하나의 무한 path에서 sample mean이 수렴한다”처럼
여러 horizon의 random variable을 같은 outcome에 대해 동시에 비교하려면 하나의
`S^ℕ` probability space와 coordinate process가 필요하다.

### Lean 지도

| 수학 단계 | Lean 이름 | 파일 |
|---|---|---|
| 길이 `n+1` path type | `ChainPath` | `LeanMetro/FinitePath.lean` |
| path probability mass | `chainPathMass` | `LeanMetro/FinitePath.lean` |
| mass 합이 1 | `chainPathMass_sum_one` | `LeanMetro/FinitePath.lean` |
| 실제 PMF와 measure | `stationaryPathPMF`, `stationaryPathMeasure` | `LeanMetro/FinitePath.lean` |
| probability-measure instance | `stationaryPathMeasure_isProbabilityMeasure` | `LeanMetro/FinitePath.lean` |
| stationary finite-path moments | `stationaryPath_current_expectation`, `stationaryPath_sum_secondMoment` | `LeanMetro/StationaryMoments.lean` |
| 실제 sample mean | `chainSampleMean` | `LeanMetro/SampleMeanVariance.lean` |
| exact scaled-variance identity | `chainSampleMean_scaledVariance_eq` | `LeanMetro/SampleMeanVariance.lean` |
| exact Poisson remainder identity | `stationaryScaledVariance_eq_algebraic_sub_remainder` | `LeanMetro/VarianceLimit.lean` |
| 실제 variance limit | `chainSampleMean_scaledVariance_tendsto` | `LeanMetro/SampleMeanVariance.lean` |
| 결과를 명명하는 predicate | `HasSampleMeanAsymptoticVariance` | `LeanMetro/ProbabilisticPeskun.lean` |

`ChainPath`는 구현상 최신 상태를 앞에 저장하지만, path mass와 path sum은
수학적으로 위의 `(x₀,…,xₙ)` 표현과 같은 내용을 갖는다.

### 현재 증명 경계

- 실제 finite-horizon PMF, measure, expectation, variance, 실수열의 극한은
  증명되어 있다.
- horizon 사이의 projective consistency는 별도 theorem으로 형식화하지 않았다.
- `S^ℕ` 위 하나의 infinite path measure와 coordinate process를 만들지 않았다.
- almost-sure law of large numbers나 Markov-chain CLT를 증명하지 않았다.
- 따라서 정확한 표현은 “stationary finite-path sample-mean scaled variance의
  극한”이지 “CLT 전체의 형식화”가 아니다.

### 자기점검 질문

1. `chainPathMass_sum_one`에서 row-sum 조건은 어떤 순서로 쓰이는가?
2. stationarity는 path measure를 만드는 데 필요한가, moment를 lag만의 함수로
   만드는 데 필요한가?
3. `chainSampleMean_scaledVariance_eq`의 왼쪽과 오른쪽은 각각 무엇인가?
4. covariance decay에서 variance limit으로 갈 때 Cesàro 정리가 왜 등장하는가?
5. 서로 다른 확률공간 위 variance들의 극한과 almost-sure convergence의 차이는
   무엇인가?
6. 이 프로젝트가 Markov-chain CLT를 증명했다고 말하면 왜 과장인가?

---

## 다섯 질문을 하나의 발표로 연결하는 법

10분 발표라면 다음 흐름이 가장 안전하다.

1. MH의 accepted flow가 `min(A,B)`라는 양방향 상한을 정확히 달성한다고
   설명한다.
2. 이것이 off-diagonal Peskun domination과 Dirichlet-form ordering을 준다고
   연결한다.
3. 두 Poisson 해의 decomposition을 칠판에 쓰고, 왼쪽의 두 항이 왜 비음수인지
   각각 말한다.
4. finite irreducibility가 centered `I-P`의 injectivity와 surjectivity를 통해
   Poisson inverse를 공급한다고 설명한다.
5. actual variance 해석은 horizon별 path measure와 exact finite-n identity가
   담당한다고 말한다.
6. 마지막으로 일반 covariance decay adapter는 아직 없고, 현재는 명시적
   `hdecay` 또는 구체 예제의 geometric proof로 닫는다고 경계를 긋는다.

## 최종 구두시험 체크리스트

다음 문장을 코드 없이 완성할 수 있으면 핵심 proof architecture를 소유하고
있다고 볼 수 있다.

- “admissible accepted flow는 `A`보다 작고, balance 때문에 `B`보다도 작다.
  그래서 …”
- “inverse ordering에서 더하는 두 비음수 항은 … 와 … 다.”
- “`E₂(g₂-g₁)`을 전개할 때 cross term이 `⟨f,g₁⟩`이 되는 이유는 …”
- “irreducibility가 fixed points를 constants로 만드는 maximum-principle 계산은
  …”
- “finite-dimensionality는 `I-P`가 … 이면 … 임을 보장하는 딱 한 곳에 쓰인다.”
- “aperiodicity가 없으면 eigenvalue … 때문에 decay가 실패할 수 있다.”
- “horizon별 sample space만 있어도 variance limit을 말할 수 있는 이유는 각
  variance가 결국 … 이기 때문이다.”
- “현재 최종 theorem이 아직 외부에서 받는 핵심 조건은 … 이며, 일반 adapter로
  아직 증명되지 않은 것은 … 이다.”

마지막 문장의 정답은 다음과 같다. Poisson invertibility는 이제 finite
irreducibility adapter로 만들 수 있다. 일반적인 covariance decay는 여전히
explicit `Tendsto` 가정이며, irreducible·aperiodic reversible finite kernel에서
이를 자동 도출하는 spectral adapter는 아직 남아 있다.
