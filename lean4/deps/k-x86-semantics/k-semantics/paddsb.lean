def paddsb1 : instruction :=
  definst "paddsb" $ do
    pattern fun (v_3226 : reg (bv 128)) (v_3227 : reg (bv 128)) => do
      v_5751 <- getRegister v_3227;
      v_5754 <- getRegister v_3226;
      v_5757 <- eval (add (sext (extract v_5751 0 8) 16) (sext (extract v_5754 0 8) 16));
      v_5767 <- eval (add (sext (extract v_5751 8 16) 16) (sext (extract v_5754 8 16) 16));
      v_5777 <- eval (add (sext (extract v_5751 16 24) 16) (sext (extract v_5754 16 24) 16));
      v_5787 <- eval (add (sext (extract v_5751 24 32) 16) (sext (extract v_5754 24 32) 16));
      v_5797 <- eval (add (sext (extract v_5751 32 40) 16) (sext (extract v_5754 32 40) 16));
      v_5807 <- eval (add (sext (extract v_5751 40 48) 16) (sext (extract v_5754 40 48) 16));
      v_5817 <- eval (add (sext (extract v_5751 48 56) 16) (sext (extract v_5754 48 56) 16));
      v_5827 <- eval (add (sext (extract v_5751 56 64) 16) (sext (extract v_5754 56 64) 16));
      v_5837 <- eval (add (sext (extract v_5751 64 72) 16) (sext (extract v_5754 64 72) 16));
      v_5847 <- eval (add (sext (extract v_5751 72 80) 16) (sext (extract v_5754 72 80) 16));
      v_5857 <- eval (add (sext (extract v_5751 80 88) 16) (sext (extract v_5754 80 88) 16));
      v_5867 <- eval (add (sext (extract v_5751 88 96) 16) (sext (extract v_5754 88 96) 16));
      v_5877 <- eval (add (sext (extract v_5751 96 104) 16) (sext (extract v_5754 96 104) 16));
      v_5887 <- eval (add (sext (extract v_5751 104 112) 16) (sext (extract v_5754 104 112) 16));
      v_5897 <- eval (add (sext (extract v_5751 112 120) 16) (sext (extract v_5754 112 120) 16));
      v_5907 <- eval (add (sext (extract v_5751 120 128) 16) (sext (extract v_5754 120 128) 16));
      setRegister (lhs.of_reg v_3227) (concat (mux (sgt v_5757 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5757 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5757 8 16))) (concat (mux (sgt v_5767 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5767 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5767 8 16))) (concat (mux (sgt v_5777 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5777 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5777 8 16))) (concat (mux (sgt v_5787 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5787 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5787 8 16))) (concat (mux (sgt v_5797 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5797 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5797 8 16))) (concat (mux (sgt v_5807 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5807 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5807 8 16))) (concat (mux (sgt v_5817 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5817 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5817 8 16))) (concat (mux (sgt v_5827 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5827 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5827 8 16))) (concat (mux (sgt v_5837 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5837 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5837 8 16))) (concat (mux (sgt v_5847 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5847 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5847 8 16))) (concat (mux (sgt v_5857 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5857 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5857 8 16))) (concat (mux (sgt v_5867 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5867 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5867 8 16))) (concat (mux (sgt v_5877 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5877 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5877 8 16))) (concat (mux (sgt v_5887 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5887 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5887 8 16))) (concat (mux (sgt v_5897 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5897 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5897 8 16))) (mux (sgt v_5907 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5907 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5907 8 16))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3222 : Mem) (v_3223 : reg (bv 128)) => do
      v_9677 <- getRegister v_3223;
      v_9680 <- evaluateAddress v_3222;
      v_9681 <- load v_9680 16;
      v_9684 <- eval (add (sext (extract v_9677 0 8) 16) (sext (extract v_9681 0 8) 16));
      v_9694 <- eval (add (sext (extract v_9677 8 16) 16) (sext (extract v_9681 8 16) 16));
      v_9704 <- eval (add (sext (extract v_9677 16 24) 16) (sext (extract v_9681 16 24) 16));
      v_9714 <- eval (add (sext (extract v_9677 24 32) 16) (sext (extract v_9681 24 32) 16));
      v_9724 <- eval (add (sext (extract v_9677 32 40) 16) (sext (extract v_9681 32 40) 16));
      v_9734 <- eval (add (sext (extract v_9677 40 48) 16) (sext (extract v_9681 40 48) 16));
      v_9744 <- eval (add (sext (extract v_9677 48 56) 16) (sext (extract v_9681 48 56) 16));
      v_9754 <- eval (add (sext (extract v_9677 56 64) 16) (sext (extract v_9681 56 64) 16));
      v_9764 <- eval (add (sext (extract v_9677 64 72) 16) (sext (extract v_9681 64 72) 16));
      v_9774 <- eval (add (sext (extract v_9677 72 80) 16) (sext (extract v_9681 72 80) 16));
      v_9784 <- eval (add (sext (extract v_9677 80 88) 16) (sext (extract v_9681 80 88) 16));
      v_9794 <- eval (add (sext (extract v_9677 88 96) 16) (sext (extract v_9681 88 96) 16));
      v_9804 <- eval (add (sext (extract v_9677 96 104) 16) (sext (extract v_9681 96 104) 16));
      v_9814 <- eval (add (sext (extract v_9677 104 112) 16) (sext (extract v_9681 104 112) 16));
      v_9824 <- eval (add (sext (extract v_9677 112 120) 16) (sext (extract v_9681 112 120) 16));
      v_9834 <- eval (add (sext (extract v_9677 120 128) 16) (sext (extract v_9681 120 128) 16));
      setRegister (lhs.of_reg v_3223) (concat (mux (sgt v_9684 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9684 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9684 8 16))) (concat (mux (sgt v_9694 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9694 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9694 8 16))) (concat (mux (sgt v_9704 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9704 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9704 8 16))) (concat (mux (sgt v_9714 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9714 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9714 8 16))) (concat (mux (sgt v_9724 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9724 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9724 8 16))) (concat (mux (sgt v_9734 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9734 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9734 8 16))) (concat (mux (sgt v_9744 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9744 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9744 8 16))) (concat (mux (sgt v_9754 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9754 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9754 8 16))) (concat (mux (sgt v_9764 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9764 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9764 8 16))) (concat (mux (sgt v_9774 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9774 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9774 8 16))) (concat (mux (sgt v_9784 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9784 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9784 8 16))) (concat (mux (sgt v_9794 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9794 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9794 8 16))) (concat (mux (sgt v_9804 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9804 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9804 8 16))) (concat (mux (sgt v_9814 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9814 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9814 8 16))) (concat (mux (sgt v_9824 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9824 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9824 8 16))) (mux (sgt v_9834 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9834 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9834 8 16))))))))))))))))));
      pure ()
    pat_end
