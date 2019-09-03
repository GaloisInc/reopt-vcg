def pcmpeqd1 : instruction :=
  definst "pcmpeqd" $ do
    pattern fun (v_3271 : reg (bv 128)) (v_3272 : reg (bv 128)) => do
      v_6883 <- getRegister v_3272;
      v_6885 <- getRegister v_3271;
      setRegister (lhs.of_reg v_3272) (concat (mux (eq (extract v_6883 0 32) (extract v_6885 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_6883 32 64) (extract v_6885 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_6883 64 96) (extract v_6885 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_6883 96 128) (extract v_6885 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3267 : Mem) (v_3268 : reg (bv 128)) => do
      v_10917 <- getRegister v_3268;
      v_10919 <- evaluateAddress v_3267;
      v_10920 <- load v_10919 16;
      setRegister (lhs.of_reg v_3268) (concat (mux (eq (extract v_10917 0 32) (extract v_10920 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10917 32 64) (extract v_10920 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10917 64 96) (extract v_10920 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_10917 96 128) (extract v_10920 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end
