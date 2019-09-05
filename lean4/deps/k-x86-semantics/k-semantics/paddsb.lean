def paddsb1 : instruction :=
  definst "paddsb" $ do
    pattern fun (v_3201 : reg (bv 128)) (v_3202 : reg (bv 128)) => do
      v_5724 <- getRegister v_3202;
      v_5727 <- getRegister v_3201;
      v_5730 <- eval (add (sext (extract v_5724 0 8) 16) (sext (extract v_5727 0 8) 16));
      v_5740 <- eval (add (sext (extract v_5724 8 16) 16) (sext (extract v_5727 8 16) 16));
      v_5750 <- eval (add (sext (extract v_5724 16 24) 16) (sext (extract v_5727 16 24) 16));
      v_5760 <- eval (add (sext (extract v_5724 24 32) 16) (sext (extract v_5727 24 32) 16));
      v_5770 <- eval (add (sext (extract v_5724 32 40) 16) (sext (extract v_5727 32 40) 16));
      v_5780 <- eval (add (sext (extract v_5724 40 48) 16) (sext (extract v_5727 40 48) 16));
      v_5790 <- eval (add (sext (extract v_5724 48 56) 16) (sext (extract v_5727 48 56) 16));
      v_5800 <- eval (add (sext (extract v_5724 56 64) 16) (sext (extract v_5727 56 64) 16));
      v_5810 <- eval (add (sext (extract v_5724 64 72) 16) (sext (extract v_5727 64 72) 16));
      v_5820 <- eval (add (sext (extract v_5724 72 80) 16) (sext (extract v_5727 72 80) 16));
      v_5830 <- eval (add (sext (extract v_5724 80 88) 16) (sext (extract v_5727 80 88) 16));
      v_5840 <- eval (add (sext (extract v_5724 88 96) 16) (sext (extract v_5727 88 96) 16));
      v_5850 <- eval (add (sext (extract v_5724 96 104) 16) (sext (extract v_5727 96 104) 16));
      v_5860 <- eval (add (sext (extract v_5724 104 112) 16) (sext (extract v_5727 104 112) 16));
      v_5870 <- eval (add (sext (extract v_5724 112 120) 16) (sext (extract v_5727 112 120) 16));
      v_5880 <- eval (add (sext (extract v_5724 120 128) 16) (sext (extract v_5727 120 128) 16));
      setRegister (lhs.of_reg v_3202) (concat (mux (sgt v_5730 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5730 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5730 8 16))) (concat (mux (sgt v_5740 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5740 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5740 8 16))) (concat (mux (sgt v_5750 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5750 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5750 8 16))) (concat (mux (sgt v_5760 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5760 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5760 8 16))) (concat (mux (sgt v_5770 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5770 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5770 8 16))) (concat (mux (sgt v_5780 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5780 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5780 8 16))) (concat (mux (sgt v_5790 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5790 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5790 8 16))) (concat (mux (sgt v_5800 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5800 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5800 8 16))) (concat (mux (sgt v_5810 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5810 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5810 8 16))) (concat (mux (sgt v_5820 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5820 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5820 8 16))) (concat (mux (sgt v_5830 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5830 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5830 8 16))) (concat (mux (sgt v_5840 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5840 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5840 8 16))) (concat (mux (sgt v_5850 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5850 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5850 8 16))) (concat (mux (sgt v_5860 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5860 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5860 8 16))) (concat (mux (sgt v_5870 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5870 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5870 8 16))) (mux (sgt v_5880 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5880 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5880 8 16))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3196 : Mem) (v_3197 : reg (bv 128)) => do
      v_9650 <- getRegister v_3197;
      v_9653 <- evaluateAddress v_3196;
      v_9654 <- load v_9653 16;
      v_9657 <- eval (add (sext (extract v_9650 0 8) 16) (sext (extract v_9654 0 8) 16));
      v_9667 <- eval (add (sext (extract v_9650 8 16) 16) (sext (extract v_9654 8 16) 16));
      v_9677 <- eval (add (sext (extract v_9650 16 24) 16) (sext (extract v_9654 16 24) 16));
      v_9687 <- eval (add (sext (extract v_9650 24 32) 16) (sext (extract v_9654 24 32) 16));
      v_9697 <- eval (add (sext (extract v_9650 32 40) 16) (sext (extract v_9654 32 40) 16));
      v_9707 <- eval (add (sext (extract v_9650 40 48) 16) (sext (extract v_9654 40 48) 16));
      v_9717 <- eval (add (sext (extract v_9650 48 56) 16) (sext (extract v_9654 48 56) 16));
      v_9727 <- eval (add (sext (extract v_9650 56 64) 16) (sext (extract v_9654 56 64) 16));
      v_9737 <- eval (add (sext (extract v_9650 64 72) 16) (sext (extract v_9654 64 72) 16));
      v_9747 <- eval (add (sext (extract v_9650 72 80) 16) (sext (extract v_9654 72 80) 16));
      v_9757 <- eval (add (sext (extract v_9650 80 88) 16) (sext (extract v_9654 80 88) 16));
      v_9767 <- eval (add (sext (extract v_9650 88 96) 16) (sext (extract v_9654 88 96) 16));
      v_9777 <- eval (add (sext (extract v_9650 96 104) 16) (sext (extract v_9654 96 104) 16));
      v_9787 <- eval (add (sext (extract v_9650 104 112) 16) (sext (extract v_9654 104 112) 16));
      v_9797 <- eval (add (sext (extract v_9650 112 120) 16) (sext (extract v_9654 112 120) 16));
      v_9807 <- eval (add (sext (extract v_9650 120 128) 16) (sext (extract v_9654 120 128) 16));
      setRegister (lhs.of_reg v_3197) (concat (mux (sgt v_9657 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9657 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9657 8 16))) (concat (mux (sgt v_9667 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9667 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9667 8 16))) (concat (mux (sgt v_9677 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9677 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9677 8 16))) (concat (mux (sgt v_9687 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9687 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9687 8 16))) (concat (mux (sgt v_9697 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9697 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9697 8 16))) (concat (mux (sgt v_9707 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9707 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9707 8 16))) (concat (mux (sgt v_9717 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9717 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9717 8 16))) (concat (mux (sgt v_9727 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9727 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9727 8 16))) (concat (mux (sgt v_9737 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9737 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9737 8 16))) (concat (mux (sgt v_9747 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9747 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9747 8 16))) (concat (mux (sgt v_9757 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9757 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9757 8 16))) (concat (mux (sgt v_9767 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9767 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9767 8 16))) (concat (mux (sgt v_9777 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9777 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9777 8 16))) (concat (mux (sgt v_9787 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9787 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9787 8 16))) (concat (mux (sgt v_9797 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9797 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9797 8 16))) (mux (sgt v_9807 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9807 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9807 8 16))))))))))))))))));
      pure ()
    pat_end
