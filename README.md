> **Complete checkpoint backup:** All 1,087 inventoried originals are saved. [Verified catalog and recovery report](checkpoint-import/updates/2026-10-24-all-checkpoints/BACKUP_STATUS.md). Historical checkpoints 72–75 remain unconfirmed.

> 실제 연구 자료 보존: 확인된 Paper I 체크포인트 원본은 이 비공개 저장소의 Release 첨부 파일에, 목록·해시·복원 도구·원격 재다운로드 검사 결과는 [checkpoint-import](checkpoint-import/README.md)에 있습니다. 72–75번은 미확인입니다. 전체 합성 시험 자료는 `artifacts/Lean_Checkpoint_Backup_2026-10-13.zip`에 있습니다.

# Lean checkpoint backup

원본을 읽기만 하고, 별도 bare Git 저장소에 체크포인트를 남기는 Python 도구입니다. 프로젝트, 고정 원고, 원고–Lean 대응 보고서·의존성 체인, 검증 로그, 지속 체크리스트를 함께 보존합니다. Git 커밋 생성만으로 성공을 판정하지 않습니다.

도구 패키지에는 설정 예시, 33개 자동 테스트, 합성 프로젝트 두 버전과 복원 결과가 들어 있습니다. `RECOVERY_STATUS.md`, `IMPLEMENTATION_REPORT.md`는 실제 자료 업로드 이전의 초기 시험 기록입니다. 이후 보존한 실제 원고·프로젝트의 범위와 원격 확인 결과는 [checkpoint-import/README.md](checkpoint-import/README.md)를 보십시오.

## 실행 환경과 빠른 시험

Python 3.11 이상, Git 2.40 이상, POSIX 파일 잠금이 필요합니다. 이번에는 Linux, Python 3.12.14, Git 2.51.1에서 실행했습니다. 다른 조합은 시험하지 않았습니다. Windows에서는 WSL 환경을 사용하십시오. 별도 Python 패키지를 설치할 필요가 없습니다. 실제 GitHub 연동에는 로그인된 `gh` CLI가 추가로 필요합니다.

압축을 푼 디렉터리에서 실행합니다. 아래 명령은 재현용 사용법입니다. 이번에 실행한 명령과 출력은 `evidence/`에 따로 남아 있습니다.

```bash
python3 -m unittest discover -s tests -v
python3 examples/run_demo.py --output /tmp/lean-backup-demo-new
```

`--output`은 아직 없는 경로여야 합니다. 데모는 합성 자료만 생성합니다. Lean 코드를 컴파일하거나 `#print axioms`를 실행하지 않으며, 예제 로그에도 이 사실을 표시합니다. 원격 경로는 테스트 안에서만 별도의 로컬 Git 저장소로 대체합니다. 테스트의 `REMOTE_VERIFIED`는 이 대체 전송에 대한 결과이며 GitHub 저장 증거가 아닙니다.

## 실제 프로젝트용 설정

`example-config.json`을 작업 원본 밖에 복사하고 절대 경로 및 `required` 목록을 실제 파일명으로 바꿉니다. 이 예시의 파일명은 실제 프로젝트에서 확인한 파일명이라는 뜻이 아닙니다. 원고가 여러 개면 `manuscript` 역할의 입력을 추가할 수 있습니다.

| 설정 | 의미 |
| --- | --- |
| `name` | 백업 안에서의 이름. 각 입력은 `payload/<name>` 아래에 저장됩니다. 파일 입력은 해당 이름의 파일이 됩니다. |
| `path` | 읽을 파일 또는 디렉터리의 절대 경로 |
| `role` | `project`, `manuscript`, `correspondence`, `verification`, `checklist` 중 하나. 다섯 역할이 모두 필요합니다. |
| `required` | 디렉터리 안에서 반드시 포함할 상대 파일 경로. 빌드 결과·axioms 출력·전체 의존성 체인의 실제 경로를 지정합니다. |
| `exclude` | 명시적으로 제외할 상대 파일·디렉터리 경로. 글로브 패턴이 아닙니다. 기본값은 제외 없음입니다. |
| `expected_sha256` | 파일 입력의 사전 확인된 SHA-256. 원고에 알려진 기준 해시가 있으면 지정하십시오. `null`이면 첫 체크포인트가 기준이 됩니다. |

모든 원고 입력은 첫 체크포인트 이후 바이트, 파일 목록, 실행 권한을 포함한 파일 모드가 고정됩니다. 정상적인 원고 개정으로 기준이 바뀌면 새 백업 저장소를 사용하십시오. 도구에는 원고를 자동 수정하거나 해시 기준을 덮어쓰는 옵션이 없습니다.

프로젝트 입력에는 `.lean` 파일, `lean-toolchain`, `lake-manifest.json`, `lakefile.lean` 또는 `lakefile.toml`이 필요합니다. 핀 파일을 보존하지만 그 핀이 유효한 설치를 가리키거나 실제 빌드가 성공했다고 판정하지는 않습니다. 검증 로그도 필수 파일 존재와 바이트 무결성을 확인할 뿐, 로그 내용을 증명으로 승인하지 않습니다.

원본의 `.git` 메타데이터는 모든 깊이에서 제외하고 그 경로를 manifest에 기록합니다. 원본 저장소의 브랜치·reflog는 복사하지 않습니다. 그 외에는 `.gitignore`와 무관하게 파일을 포함하므로, 미추적·ignored Lean 파일도 보존됩니다. `.gitattributes` 변환이나 LFS 필터는 실행하지 않습니다. LFS 포인터만 있는 파일, 심볼릭 링크, FIFO 등 일반 파일이 아닌 입력은 거부합니다.

파일당 한도는 95 MiB입니다. 큰 프로젝트 ZIP을 그대로 Git에 넣는 방식이 아니라, 별도로 풀어 놓은 프로젝트의 개별 파일을 입력으로 사용하십시오. `.lake` 등 캐시를 빼려면 `exclude`에 직접 지정합니다. 제외 목록과 실제 제외 경로는 모든 버전에 기록됩니다. 캐시·도구 체인을 제외하면 오프라인 재컴파일 환경 전체를 보존했다고 볼 수 없습니다. 숨은 자동 제외나 자동 LFS 전환은 없습니다.

## 로컬 체크포인트와 복원

`/backup`처럼 원본 밖의 부모 디렉터리를 먼저 준비합니다. 저장소를 원본 안에 만들 수 없으며, 원본을 담는 상위 디렉터리로 지정할 수도 없습니다.

```bash
python3 lean_backup.py init --config /backup/config.json --vault /backup/paper-I.git
python3 lean_backup.py checkpoint --vault /backup/paper-I.git --id 93
python3 lean_backup.py verify --vault /backup/paper-I.git
python3 lean_backup.py list --vault /backup/paper-I.git
python3 lean_backup.py restore --vault /backup/paper-I.git --id 93 --destination /backup/restored-93
```

93은 사용법의 예시 번호입니다. 첫 저장이 93이면 1–92가 보존된 것처럼 만들지 않고 `missing_before_first: [1, 92]`로 표시합니다. 이후에는 번호가 하나씩 증가해야 합니다. 실제로 중간 번호가 없는 자료를 받아들여야 할 때만 `--allow-gap`을 지정하며, 이 경우에도 `sequence_gaps`에 누락 구간이 남습니다. 중복 번호, 기존 태그 덮어쓰기, force-push, 삭제 기능은 제공하지 않습니다.

`restore`는 존재하지 않는 새 디렉터리에만 복원합니다. 원본과 겹치는 위치나 기존 디렉터리는 거부합니다. 복원물에는 `payload/`, `manifest.json`, `RESTORE_RECEIPT.json`이 들어갑니다. payload의 모든 파일을 Git에서 읽고 SHA-256을 비교한 뒤, 실제로 쓴 파일을 다시 읽어 비교합니다. 원본이 없어도 복원할 수 있습니다. 입력별 이름과 원래 경로의 대응은 manifest에 남습니다. 원래 경로에 자동으로 되돌려 쓰지 않습니다.

입력 경로와 포함 정책은 이 버전에서 저장소별로 고정됩니다. 다른 컴퓨터로 옮겨 같은 저장소에 계속 저장하려면 원래 입력 경로를 별도로 준비해야 합니다. 새 경로에 복원하는 기능과 입력 경로 재설정 기능은 구분되며, 후자는 제공하지 않습니다.

## 비공개 GitHub 백업

**이미 존재하는 빈 비공개 저장소**와 GitHub CLI 인증을 준비한 다음 실행합니다. 이 도구는 저장소를 생성하거나 공개 범위를 변경하지 않습니다. 개인 홈페이지나 프로필 저장소를 대상에 사용하지 않습니다.

```bash
python3 lean_backup.py remote-set --vault /backup/paper-I.git --github jaehwoo/lean-checkpoints-private
python3 lean_backup.py sync --vault /backup/paper-I.git
```

`remote-set`은 설정만 저장하며 업로드 성공을 뜻하지 않습니다. GitHub REST 응답의 `private=true`, `visibility=private`, 전체 저장소 이름과 숫자 ID를 확인합니다. 그 ID를 고정하여 동일 이름으로 대체된 다른 저장소도 거부합니다. URL은 확인한 GitHub 신원으로부터 만들며 임의 remote alias를 받지 않습니다. 인증 정보는 설정·manifest·영수증에 넣지 않습니다. 전역 Git URL 재작성 설정을 사용하지 않으며, 도구 저장소에 추가된 로컬 재작성 설정도 거부합니다.

원격을 설정한 뒤에는 매 `checkpoint`가 자동으로 원격 검증까지 시도합니다. 실패하면 로컬 커밋은 남겨 두고 종료 코드 3을 반환합니다. 원인을 해결한 뒤 새 번호를 만들지 말고 같은 저장소에 `sync`를 실행하십시오. 자동 반복 재시도나 무한 대기는 없습니다. 외부 명령별 제한 시간은 구현에 명시되어 있습니다.

원격 검증 절차는 다음과 같습니다.

1. GitHub 비공개 여부와 고정 ID를 확인합니다.
2. 기존 원격 참조가 로컬 이력과 충돌하지 않는지 검사합니다.
3. 브랜치와 모든 체크포인트 태그를 `git push --atomic`으로 전송합니다. 강제 갱신이나 삭제를 하지 않습니다.
4. `git ls-remote` 결과의 참조 이름과 커밋 ID 전체를 비교합니다.
5. 새 빈 저장소에 다시 fetch하고, 모든 이력의 `git fsck`, manifest, SHA-256, catalog를 검증합니다. 기존 로컬 객체나 alternates를 재사용하지 않습니다.
6. 내려받은 최신 체크포인트를 새 디렉터리에 시험 복원하여 디스크에 쓴 바이트까지 확인합니다.
7. 원격 참조와 비공개 여부를 다시 확인한 뒤에만 `REMOTE_VERIFIED`를 기록합니다.

공개 전환을 막는 GitHub 관리 잠금을 설정하는 도구는 아닙니다. 외부 관리자가 확인 사이 또는 확인 후 공개 범위를 바꾸는 일까지 막지는 못합니다. 비공개 상태는 기록된 확인 시점의 사실입니다.

## 결과와 종료 코드

| 상태 | 종료 코드 | 의미 |
| --- | --- | --- |
| `INITIALIZED_NO_CHECKPOINT`, `EMPTY_NO_CHECKPOINT` | 0 | 저장소 준비/검사만 완료. 보존된 체크포인트 없음 |
| `LOCAL_VERIFIED` | 0 | 로컬 커밋·객체·파일 해시·참조·체크포인트 목록 검증 완료. `remote_verified=false` |
| `REMOTE_CONFIGURED_NOT_UPLOADED` | 0 | 비공개 대상 설정 완료. 아직 업로드 확인 안 됨 |
| `LOCAL_VERIFIED_REMOTE_UNCONFIRMED` | 3 | 로컬은 검증했으나 원격 저장 성공을 확인하지 못함 |
| `REMOTE_VERIFIED` | 0 | 실제 설정된 GitHub 대상에 대해 위 7단계를 통과 |
| `RESTORE_VERIFIED` | 0 | 지정 버전의 파일 복원과 바이트 비교 통과 |
| `REMOTE_RECOVERY_VERIFIED` | 0 | 원격에서 별도 저장소로 다시 가져오고 복원 검증 통과 |
| `FAILED` | 2 | 해당 명령을 성공으로 인증하지 않음. 부분 작업이 남아 있을 수 있음 |

자동화에서는 종료 코드와 `status`, `remote_verified`를 함께 검사하십시오. `init`/`remote-set`의 종료 코드 0이나 push 자체의 성공만으로 “원격 백업 완료”를 알리면 안 됩니다.

## 저장소를 잃은 경우

원격에 저장되어 있다는 사실이 먼저 확인되어야 합니다. 전에 발급된 영수증의 최신 커밋을 사용하면 예상한 마지막 버전과 맞는지도 검사할 수 있습니다.

```bash
python3 lean_backup.py recover --github jaehwoo/lean-checkpoints-private --vault /backup/recovered.git --expect-commit ACTUAL_COMMIT_FROM_RECEIPT
python3 lean_backup.py list --vault /backup/recovered.git
python3 lean_backup.py restore --vault /backup/recovered.git --id 93 --destination /backup/recovered-files-93
```

`--expect-commit`은 사용자의 실제 영수증 값으로 바꾸십시오. 이를 생략하면 현재 원격에서 받은 이력의 내부 무결성만 검사하며, 과거에 마지막으로 저장한 상태와 일치하는지까지 확인할 수 없습니다. SHA-256과 Git 해시는 전자서명이 아니며, 이력·manifest·영수증을 모두 함께 바꾸는 행위까지 식별하지는 못합니다.

운영 영수증은 bare 저장소의 `receipts/`에 별도 JSON으로 남습니다. 해당 명령의 커밋 ID·manifest 해시·상태·실제 Git 명령·종료 코드를 포함합니다. 커밋 자신의 ID를 그 커밋 안에 넣을 수 없으므로, 최종 저장 확인 영수증은 커밋 바깥에 둡니다. 중요한 영수증의 커밋 ID는 별도로 보관하십시오. 원격 이력에서는 프로젝트 검증 로그와 catalog를 복구할 수 있지만 과거 로컬 운영 영수증 자체를 자동 복구하지는 않습니다.

## 무결성 범위

Git tree에는 원본 payload, 파일마다 SHA-256·바이트 수·모드와 빈 디렉터리 목록을 담은 manifest, 누적 catalog가 함께 커밋됩니다. `git update-ref --stdin` 트랜잭션으로 브랜치와 새 체크포인트 태그를 같이 만들고, 이전 브랜치 값과 새 태그 부재를 확인합니다. 마지막 검증 커밋은 별도 로컬 기준값으로 남겨 전체 참조 소실이나 이전 버전으로의 되돌림을 감지합니다. 동시 도구 실행은 잠금으로 차단합니다.

저장 전후에 파일 내용과 메타데이터·목록을 두 차례 읽어 비교합니다. 작업 중 원고·코드·로그를 쓰는 프로세스는 저장 동안 멈추는 것이 전제입니다. 이 검사는 운영체제의 원자적 파일시스템 스냅샷이나 모든 외부 작성자와의 공통 잠금을 제공하지 않습니다. 실제 원자적 시점의 보존이 필요하면 정지된 복사본 또는 파일시스템 스냅샷을 입력으로 사용하십시오.

파일 바이트, 일반 권한, 실행 권한, 빈 디렉터리를 보존합니다. 소유자, ACL, xattr, 시각 정보, 하드링크 관계와 원본 Git 이력은 복원 범위에 포함하지 않습니다. 저장장치 자체 고장이나 향후 원격 삭제에 대한 보장은 하지 않습니다. `verify`/`sync`의 결과는 실행 시점의 확인입니다. 이 도구는 Lean 컴파일러나 증명 감사를 대신하지 않습니다.

구현 참고: [Git update-ref](https://git-scm.com/docs/git-update-ref), [Git push](https://git-scm.com/docs/git-push), [GitHub Get a repository](https://docs.github.com/en/rest/repos/repos#get-a-repository).

