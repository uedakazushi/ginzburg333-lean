# ログの区別

現在の検証結果はlake_build.log、kernel_axioms.log、kernel_axioms_all.log、
final_verification.log、verification_exit_code.txtを参照する。
これらはv3の最終ビルドと公理監査のログである。
restore_*、support_*、normalized_* 等は今回の復旧と中間ビルドの履歴である。

first_build、build_round、*_build2等のログは途中のエラー修正の履歴。
network_check.txtと独立Python検査のログは入力v1の記録を保存したもの。
初版の環境未導入や中間ビルドのエラーを、現在の状態と取り違えないこと。
source_audit.jsonは文字列監査であり、kernel検証結果はVERIFICATION.jsonにある。
