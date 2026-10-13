# 실제 Paper I 체크포인트 보존 기록

이 자료는 `jaehwoo/lean-checkpoint-backup` 비공개 저장소(ID `1417233863`)에 보존한 실제 연구 자료의 목록과 복원 도구입니다. 원본 원고·프로젝트에는 쓰지 않았으며, 보존본을 내려받아 별도 디렉터리로 복원했습니다.

## 기존 체크포인트의 확인 범위

- 보존한 원본 파일명/경로: 67개. 내용 기준으로 서로 다른 SHA-256은 64개입니다. 중복 3개도 `sources.json`에 원래 이름과 대응을 기록했습니다.
- 확인된 번호: 초기 Pilot, 2–71, 76–93. 초기 Pilot을 목록에서 1번으로 취급하는 것은 명시적인 색인 규칙이며, 원래 파일명은 바꾸지 않았습니다.
- **72–75번은 확인하지 못했습니다.** 다른 환경에 없다는 뜻도, 복구되었다는 뜻도 아닙니다.
- 아카이브 검사 기록: ZIP 118개, XZ 3개, 총 121개 컨테이너. 파일별 SHA-256과 검사 결과는 `Paper_I_Lean_Archive_Audit.json.gz`에 있습니다.
- 93번 원격 보존본을 시험 복원하여 2,560개 파일을 다시 읽고 해시를 확인했습니다. 그중 `.lean` 경로 618개는 보존된 과거 소스를 포함하며 현재 활성 모듈 수와 다릅니다.

실제 프로젝트 ZIP에는 당시의 원고, Lean 소스, 원고 대응 보고서, 의존성 자료, 컴파일·axioms 검증 기록이 원래 바이트로 함께 보존되어 있습니다. 이번 작업은 파일 보존과 복원 검사입니다. Lean 재컴파일이나 수학적 정확성 검증을 새로 실행한 기록은 아닙니다.

## 저장 위치와 복원

[비공개 Releases](https://github.com/jaehwoo/lean-checkpoint-backup/releases)의 **Paper I Lean checkpoints through 93 — private archive** 초안에 7개 첨부 파일이 있습니다. 초안으로 유지하며 공개 발행하지 않았습니다. 저장소도 비공개입니다.

큰 원본은 Release 첨부 파일로, 목록·해시·복원 코드는 Git 커밋으로 보존합니다. **Git clone만으로는 첨부 파일이 내려오지 않습니다.** 로그인한 소유자 계정에서 `assets.json`에 나열된 7개 파일을 원래 파일명으로 한 디렉터리에 내려받으십시오. Parts 01–03은 각각 완전한 ZIP이며, 그 안에 변경하지 않은 원본 파일들이 있습니다. 분할 ZIP 조각처럼 이어 붙이지 마십시오.

Python 3.11 이상에서 저장소 루트를 기준으로 실행합니다. 별도 패키지 설치나 Lean 실행은 필요 없습니다.

```bash
python3 checkpoint-import/restore.py verify --assets /backup/downloaded-assets
python3 checkpoint-import/restore.py restore --assets /backup/downloaded-assets --checkpoint 93 --destination /backup/restored-93-new
```

복원 대상은 존재하지 않는 새 경로여야 합니다. 도구는 해시로 식별한 원본에서 중첩 ZIP/XZ 경로를 따라 요청 번호를 찾고, 파일별 SHA-256을 검사한 뒤 디스크에 쓴 파일을 다시 읽습니다. 확인되지 않은 번호는 오류로 거부합니다. 오류 후 생긴 부분 복원물을 성공으로 간주하지 말고 새 경로로 재시도하십시오.

## 증거 파일

| 파일 | 내용 |
| --- | --- |
| `sources.json` | 원본별 이름·경로·크기·SHA-256·복원 위치 |
| `assets.json`, `SHA256SUMS` | 7개 원격 첨부 파일의 크기와 SHA-256 |
| `coverage.json` | 번호별 아카이브 해시, 누락 번호, 검사 범위 |
| `ASSET_VERIFY_RECEIPT.json` | 다시 내려받은 첨부 파일 및 67개 원본 바이트 검사 결과 |
| `RESTORE_VERIFY_RECEIPT.json` | 93번 시험 복원 및 디스크 재검사 결과 |
| `REMOTE_VERIFICATION.json` | 저장소 신원·비공개 관측·원격 자료 확인 기록 |

이 목록은 해시가 확인된 원격 보존본에서 재구성했습니다. 원래 파일명·바이트·확인된 중복 경로는 보존하지만, 이전 저장 서비스의 파일 버전 ID는 재구성하지 않았습니다.

93번 본문 원고 SHA-256: `91c19e28f6e6a0733505ce066d6a42be9bfb6df1c8c31185849bc4b34b0ab914`.

93번 보충 원고 SHA-256: `31b5340997aac383d037029596d1c52c88679cab366263b25ecda7d594aef312`.

## 앞으로의 백업

이 디렉터리는 기존 아카이브 보존 기록입니다. 앞으로의 매 체크포인트 생성은 저장소 루트의 `lean_backup.py`와 그 README를 따릅니다. 둘은 별도의 이력입니다. 과거 아카이브를 새 도구가 생성한 Git 체크포인트인 것처럼 표시하지 않습니다.

새 운영용 bare 저장소와 빈 비공개 원격을 준비하고 실제 파일 경로·필수 보고서/로그를 지정해야 합니다. 초기 `RECOVERY_STATUS.md`, `IMPLEMENTATION_REPORT.md` 및 합성 시험 로그는 초기 도구 시험 시점의 기록입니다. 실제 연구 자료의 현재 보존 범위는 이 디렉터리를 기준으로 확인하십시오.
