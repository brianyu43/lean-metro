# Lean Metro external-evaluation remediation plan

## 1. 평가를 받아들이는 기준

현재 v1.1.0의 정확한 위치는 다음과 같다.

> 실제 finite-horizon probability measure와 sample-mean variance limit까지
> 연결한 비자명한 conditional finite-state Peskun formalization이다. 다만
> 표준 irreducibility·aperiodicity 가정에서 Poisson invertibility와 covariance
> decay를 자동 생성하는 층은 아직 없다.

이번 개선은 코드 줄 수를 늘리는 것이 아니라 외부 검토자가 가장 먼저
확인할 신뢰성, 최종 API의 사용 가능성, 표준 가정과의 연결을 강화한다.

## 2. 수정 백로그

| 우선순위 | 평가 지적 | 조치 | 완료 기준 |
|---|---|---|---|
| P0 | 라이선스와 GitHub metadata 부재 | MIT `LICENSE`, description, topics, homepage 추가 | GitHub 공개 화면에서 확인 |
| P0 | crown theorem 직접 사용 예제 부재 | 같은 `w`, `q`, competitor `a`로 최종 probabilistic theorem을 직접 호출 | 전용 예제 모듈 컴파일 |
| P0 | grep 중심 공리 감사 | crown theorem의 `#print axioms` 결과를 전용 모듈과 CI log에 남김 | 예상 공리만 출력되고 CI 성공 |
| P0 | 루트에 계획·일지 파일이 많음 | 개발 계획과 일지를 `docs/development/`, 릴리스 상세를 `docs/releases/`로 이동 | 루트에는 핵심 공개 문서만 유지 |
| P0 | README 첫 화면이 길음 | 주정리, 핵심 가정, claim boundary를 첫 10줄 안팎에 요약 | 한·영 README 갱신 |
| P1 | `MeanZeroPoissonInvertible`을 외부 가정으로 받음 | normalized stationarity와 finite irreducibility에서 fixed points가 상수임을 도출하고 finite-dimensional injective→surjective로 Poisson inverse 생성 | 일반 adapter theorem 컴파일 |
| P2 | covariance decay를 외부 가정으로 받음 | finite irreducible aperiodic reversible kernel의 spectral decay adapter 설계 | 후속 milestone과 필요한 operator refactor 명시 |
| P2 | 함수 중심 선형대수 API | `LinearMap`, mean-zero `Submodule`, finite-dimensional operator로의 점진적 adapter | 기존 교육용 API를 깨지 않는 별도 계층 설계 |
| P2 | 무한 경로/CLT 부재 | 현재 정리에는 불필요함을 유지하고 별도 연구 범위로 둠 | README와 theorem audit에서 과장 금지 |

## 3. 이번 목표의 구현 순서

### A. 신뢰성과 포장

- [x] MIT license
- [x] GitHub description, topics, homepage
- [x] root 문서 정리와 `CHANGELOG.md`
- [x] 한국어·영어 README 첫 화면 압축
- [x] crown theorem axiom audit와 CI 연결

### B. 최종 API integration test

- [x] 구체적인 2상태 `w`, `q`, competitor acceptance 정의
- [x] competitor가 `AdmissibleAcceptance`임을 검증
- [x] 일반 생성 kernel이 기존 MH/lazy numerical kernel과 같음을 검증
- [x] 양쪽 Poisson invertibility와 covariance decay를 닫음
- [x] `metropolisHastings_minimizes_sampleMeanAsymptoticVariance` 직접 호출
- [x] 실제 limit 값 `3/2 ≤ 6`까지 연결

### C. 표준 가정 adapter

- [x] finite irreducibility의 정확한 predicate 정의
- [x] irreducibility에서 `FixedPointsAreConstants` 도출
- [x] mean-zero 함수를 finite-dimensional subspace로 표현
- [x] `I-P`의 injectivity에서 surjectivity 도출
- [x] `MeanZeroPoissonInvertible` 자동 생성
- [x] 작은 예제에서 새 adapter 사용

### D. 검증과 공개

- [x] 새 모듈 개별 컴파일
- [x] 전체 `lake build`
- [x] `sorry`, `admit`, 사용자 `axiom` 0개
- [x] `git diff --check`
- [ ] GitHub Actions 성공
- [ ] 버전 태그와 release

## 4. 의도적으로 분리하는 범위

이번 목표는 normalized stationary finite kernel의 irreducibility에서 Poisson
invertibility까지를 우선 닫는다.
aperiodicity/spectral gap에서 covariance decay를 자동 생성하는 정리는
operator 계층과 mathlib spectral API를 검토한 뒤 독립 milestone로 둔다.
하나의 무한 path space, Markov-chain CLT, mixing-rate optimality도 이번
수정의 완료 조건이 아니다.

## 5. 포트폴리오 소유권 보강

코드 개선과 별개로 다음 다섯 질문에 대한 칠판 설명 문서를 후속 학습
자료로 유지한다.

1. `mhAcceptedMove_maximal`의 두 upper bound 논증
2. inverse quadratic-form decomposition의 두 비음수 항
3. irreducibility가 Poisson invertibility를 주는 finite-dimensional 이유
4. aperiodicity/spectral gap과 covariance decay의 관계
5. horizon별 확률공간만으로 scaled-variance limit을 정의할 수 있는 이유

이 설명 가능성은 기계검증과 별개인 포트폴리오 평가 기준이다.
