# OpenAI #086 — Dự án Lean 4 đầy đủ về mặt mã nguồn

**Đây là một dự án có đầy đủ mã nguồn hiện có, KHÔNG phải formalization hoàn chỉnh của bài báo.**

- `OpenAI086Whole.lean`: điểm vào để build **toàn bộ** mã Lean, gồm cả Lemma 3.3.
- `OpenAI086.lean`: các bổ đề độc lập đã viết trước đó.
- `OpenAI086/Lemma33Reviewed.lean`: ứng viên chứng minh hai bất đẳng thức logarithm
  cho phép chiếu không giao hoán; được thích nghi và ghi nguồn rõ ràng.
- `OpenAI086/PaperStatement.lean`: phát biểu Theorem 1.1 còn mở, không giả lập chứng minh.
- `lakefile.toml`, `lean-toolchain`, `.github/workflows/`: cấu hình dựng dự án.

**Lệnh chuẩn:**

```bash
python3 -m pip install sympy numpy
bash verify_all.sh
```

**Chỉ kiểm tra phần lõi:**

```bash
bash verify_core.sh
```

**Điều chưa hoàn thành:** Lemma 3.4, các ước lượng định lượng Sections 4–9,
Proposition 2.3, Theorem 2.2, Theorem 1.1. Chưa có kết quả build bằng Lean kernel
trong môi trường tạo ZIP vì máy không có Lean/Lake và không truy cập được máy chủ tải.
