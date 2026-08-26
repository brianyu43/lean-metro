# 린메트로

## 프로젝트 목표

유한 상태공간 Metropolis–Hastings 알고리즘의 detailed balance와 stationary distribution을 Lean으로 형식 검증한다.

## 증명 사다리

- 양수 두 개에 대한 acceptance ratio 항등식
- 대칭 proposal에서 off-diagonal detailed balance
- 대각항을 포함한 transition kernel 정의
- 각 행의 합이 1임을 증명
- detailed balance로부터 stationary distribution 도출
- 이후 일반적인 비대칭 proposal로 확장

## 오늘 하지 않을 것

- 비대칭 proposal
- irreducibility·aperiodicity
- convergence rate
- Markov chain 전체 라이브러리 설계
- LLM 에이전트 루프 연결

처음부터 일반적인 MH를 구현하면 나눗셈, 영점, 확률 타입, 유한합 처리에 한꺼번에 걸린다. 오늘은 실수 ℝ 위의 양수 가중치와 대칭 proposal만 다룬다.
