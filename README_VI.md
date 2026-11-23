## Bản V17 — 23/11/2026

Bổ sung mã Lean ứng viên: chứng minh giới hạn chỉ số khối dyadic
`Fin (2^k)`, lựa chọn mặt nạ zero, bất đẳng thức Bessel một lớp,
và trường hợp hữu hạn thực `m = 1` của Lemma 3.3 với hệ số `(k+1)²`.
Có thêm mã liệt kê tuple bề rộng cho bài toán không giao hoán.
442.192 kiểm tra số học chính xác đã vượt qua; **chưa biên dịch bằng
Lean kernel**, không được xem là chứng nhận định lý. Chạy
`bash verify_smoke_v17.sh`, xem `V17_PROGRESS.md`.
Theorem 1.1 vẫn chưa được chứng minh trong repository độc lập này.

---

## V14 — Bổ sung chứng minh tổ hợp hữu hạn (23/11/2026)

Thêm 6 module Lean **ứng viên chưa biên dịch**: xử lý đủ `H+lag` độ cao của Bổ đề 8.6 (kể cả `lag` độ cao xấu ban đầu), suy ra cận độ dài chuỗi *nghiêm ngặt* từ điều kiện mật độ nghiêm ngặt, , chứng minh các khối dyadic có kích thước khác nhau và điểm đầu đúng lưới, và một bước cộng năng lượng theo `L` mức dyadic với hệ số `L²` cho Bổ đề 3.3. Xem `V14_PROGRESS.md` và chạy `bash verify_smoke_v14.sh`. Đã kiểm thử 471.877 trường hợp số học chính xác, nhưng **chưa chạy Lean kernel và Định lý 1.1 vẫn chưa được chứng minh**.

---

## V13 — Đếm nhãn theo lần xuất hiện đầu tiên

Đã bổ sung mã Lean dạng **ứng viên** tạo thứ hạng trực tiếp từ các tập hữu
hạn tăng dần, tự suy ra cận kích thước tập, đổi thứ tự tổng điều hòa và
áp dụng cho hai chiều của Lemma 8.6. Đếm riêng các độ cao xấu ban đầu.
Chi tiết: `V13_PROGRESS.md`. Chạy `bash verify_smoke_v13.sh`.
**Chưa có Lean kernel build; Theorem 1.1 vẫn chưa được chứng minh.**

## Cập nhật V9 (22/11/2026) — mới nhất

- Ba module Lean độc lập: `HeightLagTelescoping`, `HeightLagChainBridge`,
  `FinitePredictorOrthogonality`, liên hệ trực tiếp Bổ đề 8.6 và 5.3.
- Bổ đề 3.3: sửa kiểu toán tử hàng thành **ánh xạ tuyến tính**,
  tránh mục tiêu cũ không đúng khi cho phép hàm phi tuyến tùy ý.
- Bộ kiểm thử V9: 6.301 trường hợp số học chính xác đạt, kiểm tra import /
  trạng thái 59 kết quả đạt. **Chưa build bằng Lean kernel** do không có `lake`.
- Định lý 1.1 và các bổ đề chính còn MỞ; không được coi mã nguồn này là
  chứng minh hoàn chỉnh. Chi tiết: `V9_PROGRESS.md`.

Lệnh Ubuntu/WSL: `bash verify_smoke_v9.sh`.

---

## Trạng thái hiện tại — V7 (22/11/2026)

- **59/59** kết quả có đầu mối mã Lean; **21/59** có thành phần chứng minh hữu hạn liên quan; **38/59** chỉ có mô hình hữu hạn chưa chứng minh phát biểu bài báo.
- **0/59** kết quả của bài báo được chứng nhận đầy đủ. Phần mã Lean mới vẫn **chưa chạy qua kernel**, vì không có `lake` trong môi trường tạo gói.
- Thêm 6 module cho khai triển dyadic ở cấp toán tử tuyến tính, tích có thứ tự không giao hoán, giới hạn số nhãn catalog và các khai triển bốn đầu vào.
- Chạy `bash verify_smoke_v7.sh` và, trên Ubuntu/WSL có Lean, `bash verify_ubuntu.sh`. Xem `V7_PROOF_PROGRESS.md`.

---

# OpenAI #086 — Lean 4 partial formalization độc lập

Đây là mã nguồn **chưa chứng minh xong** bài báo 93 trang *An L³ Bound for the Trilinear Hilbert Transform* (05/10/2026). Chương trình không nhập hoặc sao chép mã Lean của Joris Roos. Hai file lịch sử `Lemma33Reviewed.lean` và `Lemma33Check.lean` đã được loại khỏi ZIP độc lập.

## Cấu trúc

- `OpenAI086/PaperStatement.lean`: phát biểu `Theorem1_1_Goal : Prop` **chưa có chứng minh**.
- `OpenAI086.lean`, `OpenAI086Whole.lean`: hai entrypoint cho thư viện Lean.
- `OpenAI086/FiniteTonelliBudget.lean`: đổi thứ tự tổng và ước lượng ngân sách theo đường đi hữu hạn (§3.1).
- `OpenAI086/FiniteMultifamilyStops.lean`: cận hợp của nhiều họ điểm dừng (§§2–3).
- `OpenAI086/ArbitraryColoredPaths.lean`: dãy màu xác định duy nhất đường đi có độ dài chẵn bất kỳ (§9.1).
- `OpenAI086/CompressionRowError.lean`: đánh giá lỗi hệ số bằng giả thiết Cauchy–Schwarz/Bessel hữu hạn (§3.4).
- `OpenAI086/FirstFailureAnyRole.lean`: chọn vai trò lỗi đầu tiên cho số lượng vai trò hữu hạn bất kỳ (§9.1).
- `OpenAI086/FiniteFirstSuccessWeights.lean`: phân tích tổng hình học và trọng số thành công đầu tiên (§9.1).
- `tools/`: kiểm toán mã, các phép thử số học và bộ kiểm chứng đăng ký kết quả.
- `.github/workflows/kernel-check.yml`: biên dịch và kiểm tra trên GitHub Actions.

## Cách chạy (Ubuntu/WSL)

```bash
# Cần cài Lean bằng elan; phiên bản được ghim trong lean-toolchain.
bash verify_ubuntu.sh  # tự dùng venv cho numpy/sympy nếu thiếu
# Hoặc chạy trực tiếp bash verify_all.sh nếu đã cài dependencies
# Nếu không có Lake, script dừng và báo lỗi rõ ràng.
```

Nếu không có `lake`, script dừng với mã 2 và ghi **UNVERIFIED**; các phép thử Python không tương đương với việc Lean kernel kiểm chứng.

Kiểm tra độc lập các bổ đề hữu hạn mới:

```bash
python3 tools/test_new_finite_bridges.py
```

## Tình trạng

- Danh mục bài báo: 59 kết quả; 17 kết quả có mã thành phần liên quan, **0/59** được chứng nhận đầy đủ.
- Chưa chứng minh trọn Lemma 3.3, Lemma 3.4, các ước lượng chính của §§4–9, Proposition 2.3, Theorem 2.2, Theorem 1.1 và phép mở rộng toán tử trên `L³`.
- Các định lý Lean mới đã được viết theo hướng độc lập, nhưng **chưa được kernel biên dịch trong môi trường tạo ZIP**.
- Kiểm tra mức độ hoàn tất nghiêm ngặt: `python3 tools/paper_obligation_report.py --require-complete` phải trả về trạng thái chưa đạt cho tới khi chứng minh cuối được thiết lập.


### Bản tiếp tục v2 — 22/11/2026

Xem `CONTINUATION_V2_2026_11_22.md`: bổ sung 5 module Lean gồm ước lượng
năng lượng bình phương cho họ phép chiếu trực giao lồng nhau (trường hợp
m=1 hữu hạn chiều thực), sai số tích các contraction không giao hoán,
Cauchy–Schwarz hữu hạn và lựa chọn lần thành công đầu tiên với xác suất
thất bại biến thiên. **Chưa chạy Lean kernel**; không khẳng định đã chứng
minh Lemma 3.3/3.4 đầy đủ hay Theorem 1.1.

### Bản tiếp tục V3 — 22/11/2026

Xem `CONTINUATION_V3_2026_11_22.md`. Đã bổ sung 6 module về cận
Gram hai phía trong mô hình hữu hạn thực, trực giao gia số projection,
Bessel rows được chọn thích nghi, nhiều lớp không giao hoán, và đếm
đường đi 2/4 cạnh trong đồ thị. Bản V3 có **71 file Lean** và
**193 khai báo theorem**, thử **82.352** trường hợp số học/số học chính xác
đều đạt. **Chưa thể chạy Lean kernel**; vẫn **17/59 partial, 0/59 full**.

## Bản tiếp tục V4 (22/11/2026)

Xem `CONTINUATION_V4_2026_11_22.md` và `verification/V4_RELEASE_AUDIT.json`. Bản này thêm bổ đề năng lượng block của phép chiếu lồng nhau và phép lọc bad-partner hữu hạn. **Chưa chứng minh Theorem 1.1, chưa chạy Lean kernel.**

## Bổ sung V8 (22/11/2026)

Bản V8 mở rộng các bất đẳng thức Bessel sang không gian có chuẩn tổng quát (`OpenAI086/NormedAdaptiveBessel.lean`); chứng minh ứng viên cho các trường hợp biên `m=0` và biến thiên `m=1` của chính `FiniteLemma33Target.lean`; và xây dựng cận hữu hạn **chưa tối ưu** `(T+1)` cho row-prefix, `4T` cho square variation khi có nhiều lớp projection không giao hoán. Xem `CONTINUATION_V8_2026_11_22.md`.

Chạy `bash verify_smoke_v8.sh` trên Ubuntu/WSL. Khi thiếu `lake`, lệnh trả mã 2: chỉ kiểm tra Python/nguồn, **không chứng nhận Lean**. Theorem 1.1 và Lemma 3.3 tổng quát vẫn chưa chứng minh xong.


## V10 (22/11/2026)

Năm mô-đun Lean mới tập trung vào Lemma 8.6 (hai phép cộng dồn,
đếm ngoại lệ theo thứ hạng, kiểm tra điểm xấu từ tập hữu hạn) và
Lemma 3.3 (ước lượng các hàng với K lựa chọn độ sâu).
Có 11.976 kiểm tra hữu hạn đạt, nhưng **chưa biên dịch bằng Lean kernel**.
Đọc `V10_PROGRESS.md` và chạy `./verify_smoke_v10.sh`.
**Theorem 1.1 vẫn chưa được chứng minh độc lập.**

### Tiến độ V12

Xem [`V12_PROGRESS.md`](V12_PROGRESS.md): bổ sung chứng minh ứng viên cho
lũy thừa 11/10, độ đầy đủ của cửa sổ tìm kiếm, cận đếm thứ hạng và
định lý cầu nối Lemma 8.6 từ tập nhãn hữu hạn. Chạy
`./verify_smoke_v12.sh`. **Chưa có chứng nhận Lean kernel** trong môi
trường hiện tại; các giả thiết về thứ tự nhãn xuất hiện đầu tiên vẫn
được giữ tường minh.


## V15: khối dyadic từ phép chiếu thực (mã ứng viên chưa biên dịch)

Xem [V15_PROGRESS.md](V15_PROGRESS.md). Các module mới xử lý chính xác `Δ₀=P₀`, nối khối dyadic với bất đẳng thức Bessel và tích phép chiếu không giao hoán. Vẫn thiếu chứng minh Lean về phân rã đồng nhất theo bộ độ dài của từng dòng; chưa xác nhận bằng Lean kernel. Chạy `bash verify_smoke_v15.sh`.


### V16 (chưa được Lean kernel chứng nhận)

Chạy `bash verify_smoke_v16.sh`. Bổ sung phép phân nhóm độ dài dyadic chung cho mọi hàng, xác định block duy nhất hoặc zero, và chặn Bessel có mặt nạ cho các tích phép chiếu không giao hoán. Xem `V16_PROGRESS.md` về các bước còn thiếu.
