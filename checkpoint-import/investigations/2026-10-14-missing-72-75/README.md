# 체크포인트 72–75 원본 추적 결과

조사일: 2026-10-14 (Asia/Seoul). 기준 커밋: `ea1aa6765b694fb8944eed4b1083fc6ea969bd46`.

**조사한 범위에서 72·73·74·75번의 원본은 발견하지 못했습니다. 이번에 복구한 누락 번호는 없습니다.** 71번과 76번의 기존 원본을 별도 경로에 복원하여 파일 단위로 비교했습니다. 아래의 차이는 두 보존본에서 관측한 결과이며, 72–75번의 작업 내용이나 원본을 재구성한 결과가 아닙니다.

## 보존 범위와 조사 범위

- 기존 비공개 GitHub 보존 범위는 초기 Pilot, 2–71, 76–93입니다. Pilot을 1번으로 세는 것은 기존 색인 규칙입니다. `coverage.json`과 기존 Release 첨부 파일은 변경하지 않았습니다.
- 저장소 ID `1417233863`, 비공개 상태, `main` 한 개, 커밋 3개, 초안 Release 한 개와 첨부 7개를 확인했습니다. 첨부의 서버 제공 SHA-256은 기존 기록과 일치했습니다. 이번에 7개 첨부를 모두 다시 다운로드한 것은 아닙니다.
- 기존 `sources.json`의 원본 이름·경로 67개, 서로 다른 SHA-256 64개 및 `coverage.json`을 대조했습니다. 앞선 ZIP 118개·XZ 3개 검사는 기존 검증 기록으로 인용하며, 이번의 신규 검사 수에 합산하지 않습니다.
- 현재 Library에서 `Paper_I`, `Lean`, `Checkpoint_7`, 72·73·74·75, 정확한 71·76번 파일명, 이력·백업 관련 이름을 검색했습니다. 2026-10-08 이후 생성 항목의 전체 조회는 133개 항목과 종료 커서 없음으로 반환되었습니다. 이 목록에 해당 번호의 원본 파일은 없었습니다. 숫자만 일치하는 다른 원고·이미지는 체크포인트 후보로 취급하지 않았습니다.
- 원본 이력을 담을 가능성이 있는 현재 아카이브 27개를 다운로드하여 바이트를 검사했습니다. 이력 묶음 82·93·104, 108번 프로젝트·작업본·체크리스트·보고서·빌드 증거·진행본, 109번 진행본, 93–108번 전달 확인 묶음 및 별도 원래 증명 경로 묶음이 포함됩니다. 정확한 파일 ID·버전·원래 경로·해시는 `source_provenance.json`에 있습니다.
- 중복 해시를 합쳐 컨테이너 72개를 만났습니다. 이 중 71개를 새로 열었습니다: ZIP 61개, XZ 5개, TAR 5개. 이미 검증된 70번 ZIP 1개는 해시를 대조한 뒤 기존 목록을 재사용했습니다. 73,726개 멤버 레코드의 SHA-256을 계산했습니다. 이는 아카이브 사이의 중복과 XZ 해제 스트림을 포함하며, 서로 다른 파일의 수가 아닙니다.
- 처음에 미지원으로 남았던 TAR 5개도 후속 단계에서 모두 열어 검사했습니다. 최종 미처리 오류는 없습니다. 전체 멤버 이름을 대상으로 한 72–75번 체크포인트·배치 이름 검색의 일치 항목은 0개입니다. 본문에서 발견된 관련 언급은 누락·재구성에 관한 기록이며, 해당 번호의 원본 파일이나 신뢰할 만한 원본 SHA-256을 제공하지 않았습니다.
- 과거 기록에 실제로 등장한 세 작업 경로는 현재 실행 환경에 존재하지 않았습니다. 다른 실행 환경이나 접근 불가능한 저장소에도 사본이 없다는 의미는 아닙니다.

현재 파일이 같은 Library 항목의 여러 버전으로 갱신된 사실도 확인했습니다. 예를 들어 76번에 보존된 당시 조회 기록은 같은 프로젝트 항목의 54번 버전을 `Paper_I_Lean_Checkpoint_71.zip`으로 표시합니다. 현재 조회는 87번 버전을 `Paper_I_Lean_Checkpoint_108.zip`으로 표시합니다. **이 사실만으로 중간 버전의 내용이나 72–75번 저장 여부를 추정하지 않았습니다.** 현재 도구에는 과거 버전을 나열하거나 특정 과거 바이트를 별도 다운로드하는 인터페이스가 노출되지 않았습니다. 기존 파일을 과거 버전으로 되돌리는 동작은 실행하지 않았습니다.

## 출처와 중첩 압축 경로

다운로드한 `Paper_I_Lean_History_Through_82.zip`은 기존 Release의 같은 이름 원본과 SHA-256이 일치합니다:

`9a76d1d59bdfa6028bf7af407a56857007cb58760c6d9e4127c18ccfb6de3b55`

이 파일에서 각 ZIP의 `PaperILean/checkpoints/` 멤버를 따라 81 → 80 → 79 → 78 → 77 → 76 → 71 순서로 원본에 도달했습니다. **76번의 직접 부모는 71번이며, 이 중첩 경로에는 72–75번이 없습니다.** 각 단계의 원본 이름, 부모 해시, 멤버 경로, 자식 해시가 `archive_scan.json.xz`와 `endpoint_routes.json`에 기록되어 있습니다.

별도로 다운로드한 `Paper_I_Lean_History_Through_93.zip`도 기존 기록의 `Paper_I_Lean_Checkpoint_93.zip`과 같은 바이트입니다. 이름이 다르다는 이유로 새 원본으로 세지 않았습니다. 104번 및 이후 후보에서는 후속 이력이 확인되었으나, 이를 기존 GitHub Release에 새로 보존한 것처럼 `coverage.json`에 추가하지 않았습니다.

## 실제 복원 결과

| 항목 | 71번 | 76번 |
| --- | --- | --- |
| 원본 ZIP 크기 | 396,049,451 bytes | 407,803,767 bytes |
| 복원된 파일 | 1,153 | 1,196 |
| `.lean` 경로 전체 | 407 | 419 |
| `PaperILean/PaperILean/` 바로 아래 모듈 파일 | 387 | 398 |
| 원본 해시 대조 | 기존 목록과 일치 | 기존 목록과 일치 |
| 복원 후 디스크 재검사 | 모든 파일 SHA-256 일치 | 모든 파일 SHA-256 일치 |

71번 ZIP SHA-256:

`621a0aca6001bf8a3d569b7be7603344efd3c33e6ba5f98ac403f7226aca99a8`

76번 ZIP SHA-256:

`6b8eb62da8232b05c7779343a786ec904ffd1a3c39a8f9009562044d02906c05`

복원은 서로 다른 새 디렉터리에 수행했습니다. 경로 이탈·중복 파일명·특수 파일을 거부하고, ZIP에서 읽은 바이트를 쓴 뒤 디스크의 SHA-256을 다시 계산했습니다. 전체 결과는 `restored_71_manifest.json.gz`와 `restored_76_manifest.json.gz`에 있습니다. 이 단계는 원본 바이트의 복원 검사이며 Lean 재컴파일이나 수학적 증명 검증은 아닙니다.

## 71번과 76번에서 확인되는 차이

| 파일 단위 비교 | 개수 | 해석 |
| --- | ---: | --- |
| 같은 경로·같은 바이트 | 1,090 | 기존 Lean 모듈 387개, 원고 및 환경 고정 파일 포함 |
| 같은 경로·다른 바이트 | 25 | 루트 import 파일, 현재 보고서·의존성·체크리스트·포장 메타데이터 등 |
| 76번 최상위 ZIP에 추가 | 81 | 새 모듈, 76번 기록·도구, 원본 71번 ZIP 등 |
| 76번 최상위 ZIP에서 빠짐 | 38 | 모두 과거 `checkpoints/` 자료이며, 원본 71번 ZIP 내부에 그대로 보존 |

수학 모듈 10개가 추가되었습니다: `AllDimCoefficientSpace`, `AllDimCoefficientModel`, `AllDimPolynomialQuotient`, `AllDimAffinePullback`, `AllDimCoefficientChange`, `AllDimIndexWeights`, `AllDimDiagonalCharacter`, `AllDimAffineCharacterTargets`, `AllDimGeneralAffineCharacter`, `AllDimAffineCharacterUses`. 이외에 `Batch76AxiomAudit.lean`과 실패한 중간 감사 초안 1개가 추가됩니다. 루트 `PaperILean.lean`에는 위 수학 모듈의 import 10개가 추가되었습니다. 기존 모듈 387개의 바이트는 모두 같습니다.

76번의 보존된 보고서는 전 차원 계수 공간, 상수로 나눈 다항식 공간, 실제 아핀 작용, 행렬식 character 및 계수 측도 변환을 해당 배치의 범위로 설명합니다. 65개 theorem proof와 37개 다른 선언의 검증 기록을 보고하지만, **이 조사는 그 수학적 주장을 새로 검증하지 않았습니다.** 원래 삼각화·동차 성분·직교/SVD 중간 논증과의 차이도 당시 보고서에 남아 있습니다. 76번의 추가분을 72–75번에 배정할 근거는 없습니다.

정식 체크리스트는 2,793개에서 2,895개 항목으로 늘었습니다. 102개 ID가 추가되고 기존 ID는 삭제되지 않았습니다. 기존 항목 중 2,785개는 그대로이고 8개는 내용이 바뀌었습니다: `ARG:coefficient_basis`, `ARG:degree_filtration`, `ARG:monomial_character`, `ARG:seminorm_uniformity`, `an:character`, `an:cube-reduction`, `an:physical-assembly`, `root:main`. 이는 보존된 체크리스트의 비교 결과입니다. 각 차이는 `checklist_diff.json`에 기록했습니다.

같은 이름의 `reports/Paper_I_Lean_Checkpoint_71_Report.pdf`도 두 ZIP에서 바이트가 다릅니다(76,807 → 108,685 bytes). 두 해시를 `comparison_71_76.json`에 각각 보존했습니다. 이름만으로 같은 파일이라고 간주하지 않았습니다. 원래 71번 ZIP 자체는 76번 안에 정확히 보존되어 있으므로 기존 71번 보고서 바이트도 남아 있습니다.

본문 원고 SHA-256은 양쪽 모두 `91c19e28f6e6a0733505ce066d6a42be9bfb6df1c8c31185849bc4b34b0ab914`, 보충 원고는 양쪽 모두 `31b5340997aac383d037029596d1c52c88679cab366263b25ecda7d594aef312`입니다. `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`도 같습니다.

## 실제 원본과 추정을 구분한 결론

1. **원본 확인:** 위 해시의 71번·76번 원본 ZIP과 별도 복원 파일. 기존 Pilot·2–71·76–93 보존 목록을 변경할 이유는 발견되지 않았습니다.
2. **관측된 변경:** 위 파일 비교와 체크리스트 비교. 76번은 71번을 직접 부모로 삼습니다.
3. **당시 기록의 진술:** 76번의 `Checkpoint76_Recovery.json`은 `unrecovered_checkpoints: [72,73,74,75]`를 명시합니다. `checkpoint_76_reconstruction_method.json`은 `later_source_bytes_recovered: false`이며 71번에서 새 차원 매개변수 선언을 만들었다고 설명합니다.
4. **확인할 수 없는 부분:** 72–75번의 실제 원본 바이트·독립적인 원본 해시·그 번호별 정확한 변경 내용. 과거 대화나 후속 요약으로 이를 대체하지 않았습니다.

72–75번이라는 이름으로 재구성 ZIP이나 선언 목록을 만들지 않았습니다. 원고·기존 체크포인트·기존 보존 목록·Release 첨부 파일을 수정하지 않았습니다. 이번 조사 기록만 별도 경로에 추가했습니다. 다른 환경의 사본이나 과거 버전 바이트가 이후 제공되면, 이 기록의 해시·출처 표를 기준으로 추가 대조할 수 있습니다.

## 증거 파일

- `RESULT.json`: 결과와 명시적인 범위·한계.
- `source_provenance.json`: 조사한 아카이브 27개의 식별자·버전·경로·SHA-256.
- `archive_scan.json.xz`: 전체 컨테이너 그래프, 파일별 해시, 중첩 경로, 본문 검색 흔적. Python 표준 `lzma`로 열 수 있습니다.
- `endpoint_routes.json`: 82번 이력에서 76번·71번에 이르는 해시 검증 경로.
- `comparison_71_76.json`, `changed_text_files.diff`: 파일별 비교 및 변경 텍스트 diff.
- `checklist_diff.json`: 체크리스트 ID별 비교.
- `restored_71_manifest.json.gz`, `restored_76_manifest.json.gz`: 복원 파일 전체 목록과 해시.
- `target_name_check.json`, `prior_workspace_checks.json`, `lookup_scope.json`: 검색 범위와 미확인 결과.
- `archived-evidence/`: 원본 76번에서 바이트 그대로 복사한 출처 관련 기록. 새 검증 결과로 취급하지 않습니다.
- `executed-scripts/`, `execution_results.json`: 이 조사에서 실행한 코드와 종료 상태. 스크립트는 당시 작업 디렉터리 배치를 전제로 하는 실행 기록입니다.
- `SHA256SUMS`: 이 조사 디렉터리의 파일 해시.
