def pcmpeqw1 : instruction :=
  definst "pcmpeqw" $ do
    pattern fun (v_2383 : reg (bv 128)) (v_2384 : reg (bv 128)) => do
      v_3809 <- getRegister v_2384;
      v_3811 <- getRegister v_2383;
      setRegister (lhs.of_reg v_2384) (concat (mux (eq (extract v_3809 0 16) (extract v_3811 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3809 16 32) (extract v_3811 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3809 32 48) (extract v_3811 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3809 48 64) (extract v_3811 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3809 64 80) (extract v_3811 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3809 80 96) (extract v_3811 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_3809 96 112) (extract v_3811 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (eq (extract v_3809 112 128) (extract v_3811 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end;
    pattern fun (v_2378 : Mem) (v_2379 : reg (bv 128)) => do
      v_11288 <- getRegister v_2379;
      v_11290 <- evaluateAddress v_2378;
      v_11291 <- load v_11290 16;
      setRegister (lhs.of_reg v_2379) (concat (mux (eq (extract v_11288 0 16) (extract v_11291 0 16)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_11288 16 32) (extract v_11291 16 32)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_11288 32 48) (extract v_11291 32 48)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_11288 48 64) (extract v_11291 48 64)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_11288 64 80) (extract v_11291 64 80)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_11288 80 96) (extract v_11291 80 96)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (concat (mux (eq (extract v_11288 96 112) (extract v_11291 96 112)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)) (mux (eq (extract v_11288 112 128) (extract v_11291 112 128)) (expression.bv_nat 16 65535) (expression.bv_nat 16 0)))))))));
      pure ()
    pat_end
