# QPBT Publication Report

Publication date: 2026-10-29.

The QPBT description update covered 193 definition bundles. All 193 were read back with byte-for-byte matching text:

- 193 descriptions requested.
- 191 descriptions patched.
- 2 descriptions were already exact.
- 193/193 descriptions verified after readback.
- The PATCH reason was `Full statement and description before publication`.

The publication census covered 863 QPBT entries: 670 theorem records and 193 definition records.

- 12 `make-public` requests were accepted: four target theorems and eight definition records.
- 851 entries were already public when encountered after target closure.
- 863/863 entries were public in the authenticated final visibility audit.
- 0 entries were private and 0 had another visibility state.
- 0 definition publication calls were unsupported.
- 0 terms or licensing errors occurred; no terms or licensing were accepted.

Signed-out verification used `GET https://prove2.me/theorems/<id>` with no Authorization header and no cookies, at no more than two requests per second. The definition records were checked through the same theorem-page URL pattern using each definition id. An entry counted as verified only when the response was HTTP 200 and the page contained the first sentence of its description after decoding the page's serialized HTML escapes.

- 863/863 signed-out page checks verified.
- 0 HTTP failures.
- 0 HTTP 200 sentence mismatches.
- 670 theorem pages and 193 definition pages were verified.

Nothing remains private according to the authenticated final visibility audit.

Public target URLs:

- `MIPStarRE.QPBT.Palomar.exists_spcc_value_one`: https://prove2.me/theorems/1de50f6e-433e-4a73-8b0a-9c1abf9cc4a4
- `MIPStarRE.QPBT.Palomar.exists_ld_soundness`: https://prove2.me/theorems/416c9a7c-e177-431c-8a89-75370acdcafd
- `MIPStarRE.QPBT.Palomar.pauli_soundness`: https://prove2.me/theorems/365d161d-0635-4dce-89f5-335ed8b46f8a
- `MIPStarRE.QPBT.Palomar.pauli_soundness_qubit`: https://prove2.me/theorems/ec8b14f9-d46f-4633-9134-2e44797adbce

The resumable publication state is in `prove2me/records/qpbt_publish_state.json`; the call log is in `prove2me/records/qpbt_publish.log`; and the signed-out run log is in `prove2me/records/qpbt_page_verify_run.log`.
