# 2026-08-30 Peskun Phase 3a

## 새 이론

유한 상태공간의 함수 `f`, `g`를 target mass `π`로 가중해 비교하는
쌍선형 pairing과 kernel이 함수에 작용하는 Markov operator를 도입했다.

```text
weightedInner π f g = ∑ x, π(x) f(x) g(x)
markovOperator P f x = ∑ y, P(x,y) f(y)
```

## 구현한 것

- `weightedInner`의 대칭성, 덧셈과 스칼라곱 호환성
- `markovOperator`의 덧셈과 스칼라곱 호환성
- 행 합이 1이라는 사실에서 `P 1 = 1` 도출
- detailed balance에서 weighted self-adjointness 도출

마지막 정리는 다음 수학적 등식을 모든 유한합을 직접 재배열해 검증한다.

```text
<f, Pg>_π = <Pf, g>_π
```

## 다음 단계

- Dirichlet form 정의
- `E_P(f) = <f, f>_π - <f, Pf>_π` 증명
- Peskun domination에서 Dirichlet ordering 도출
