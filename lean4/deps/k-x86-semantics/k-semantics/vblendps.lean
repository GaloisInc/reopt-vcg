def vblendps1 : instruction :=
  definst "vblendps" $ do
    pattern fun (v_2805 : imm int) (v_2809 : reg (bv 128)) (v_2810 : reg (bv 128)) (v_2811 : reg (bv 128)) => do
      v_5751 <- eval (handleImmediateWithSignExtend v_2805 8 8);
      v_5754 <- getRegister v_2810;
      v_5756 <- getRegister v_2809;
      setRegister (lhs.of_reg v_2811) (concat (mux (eq (extract v_5751 4 5) (expression.bv_nat 1 0)) (extract v_5754 0 32) (extract v_5756 0 32)) (concat (mux (eq (extract v_5751 5 6) (expression.bv_nat 1 0)) (extract v_5754 32 64) (extract v_5756 32 64)) (concat (mux (eq (extract v_5751 6 7) (expression.bv_nat 1 0)) (extract v_5754 64 96) (extract v_5756 64 96)) (mux (eq (extract v_5751 7 8) (expression.bv_nat 1 0)) (extract v_5754 96 128) (extract v_5756 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2818 : imm int) (v_2819 : reg (bv 256)) (v_2820 : reg (bv 256)) (v_2821 : reg (bv 256)) => do
      v_5784 <- eval (handleImmediateWithSignExtend v_2818 8 8);
      v_5787 <- getRegister v_2820;
      v_5789 <- getRegister v_2819;
      setRegister (lhs.of_reg v_2821) (concat (mux (eq (extract v_5784 0 1) (expression.bv_nat 1 0)) (extract v_5787 0 32) (extract v_5789 0 32)) (concat (mux (eq (extract v_5784 1 2) (expression.bv_nat 1 0)) (extract v_5787 32 64) (extract v_5789 32 64)) (concat (mux (eq (extract v_5784 2 3) (expression.bv_nat 1 0)) (extract v_5787 64 96) (extract v_5789 64 96)) (concat (mux (eq (extract v_5784 3 4) (expression.bv_nat 1 0)) (extract v_5787 96 128) (extract v_5789 96 128)) (concat (mux (eq (extract v_5784 4 5) (expression.bv_nat 1 0)) (extract v_5787 128 160) (extract v_5789 128 160)) (concat (mux (eq (extract v_5784 5 6) (expression.bv_nat 1 0)) (extract v_5787 160 192) (extract v_5789 160 192)) (concat (mux (eq (extract v_5784 6 7) (expression.bv_nat 1 0)) (extract v_5787 192 224) (extract v_5789 192 224)) (mux (eq (extract v_5784 7 8) (expression.bv_nat 1 0)) (extract v_5787 224 256) (extract v_5789 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_2800 : imm int) (v_2799 : Mem) (v_2803 : reg (bv 128)) (v_2804 : reg (bv 128)) => do
      v_11218 <- eval (handleImmediateWithSignExtend v_2800 8 8);
      v_11221 <- getRegister v_2803;
      v_11223 <- evaluateAddress v_2799;
      v_11224 <- load v_11223 16;
      setRegister (lhs.of_reg v_2804) (concat (mux (eq (extract v_11218 4 5) (expression.bv_nat 1 0)) (extract v_11221 0 32) (extract v_11224 0 32)) (concat (mux (eq (extract v_11218 5 6) (expression.bv_nat 1 0)) (extract v_11221 32 64) (extract v_11224 32 64)) (concat (mux (eq (extract v_11218 6 7) (expression.bv_nat 1 0)) (extract v_11221 64 96) (extract v_11224 64 96)) (mux (eq (extract v_11218 7 8) (expression.bv_nat 1 0)) (extract v_11221 96 128) (extract v_11224 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2813 : imm int) (v_2812 : Mem) (v_2814 : reg (bv 256)) (v_2815 : reg (bv 256)) => do
      v_11246 <- eval (handleImmediateWithSignExtend v_2813 8 8);
      v_11249 <- getRegister v_2814;
      v_11251 <- evaluateAddress v_2812;
      v_11252 <- load v_11251 32;
      setRegister (lhs.of_reg v_2815) (concat (mux (eq (extract v_11246 0 1) (expression.bv_nat 1 0)) (extract v_11249 0 32) (extract v_11252 0 32)) (concat (mux (eq (extract v_11246 1 2) (expression.bv_nat 1 0)) (extract v_11249 32 64) (extract v_11252 32 64)) (concat (mux (eq (extract v_11246 2 3) (expression.bv_nat 1 0)) (extract v_11249 64 96) (extract v_11252 64 96)) (concat (mux (eq (extract v_11246 3 4) (expression.bv_nat 1 0)) (extract v_11249 96 128) (extract v_11252 96 128)) (concat (mux (eq (extract v_11246 4 5) (expression.bv_nat 1 0)) (extract v_11249 128 160) (extract v_11252 128 160)) (concat (mux (eq (extract v_11246 5 6) (expression.bv_nat 1 0)) (extract v_11249 160 192) (extract v_11252 160 192)) (concat (mux (eq (extract v_11246 6 7) (expression.bv_nat 1 0)) (extract v_11249 192 224) (extract v_11252 192 224)) (mux (eq (extract v_11246 7 8) (expression.bv_nat 1 0)) (extract v_11249 224 256) (extract v_11252 224 256)))))))));
      pure ()
    pat_end
