## Trạng thái hiện tại — V7 (22/11/2026)

- **59/59** kết quả có đầu mối mã Lean; **21/59** có thành phần chứng minh hữu hạn liên quan; **38/59** chỉ có mô hình hữu hạn chưa chứng minh phát biểu bài báo.
- **0/59** kết quả của bài báo được chứng nhận đầy đủ. Phần mã Lean mới vẫn **chưa chạy qua kernel**, vì không có `lake` trong môi trường tạo gói.
- Thêm 5 module cho khai triển dyadic ở cấp toán tử tuyến tính, tích có thứ tự không giao hoán, giới hạn số nhãn catalog và các khai triển bốn đầu vào.
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
