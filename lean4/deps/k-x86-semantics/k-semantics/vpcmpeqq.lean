def vpcmpeqq : instruction :=
  definst "vpcmpeqq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      setRegister (lhs.of_reg xmm_2) (concat (mux (eq (extract v_3 0 64) (extract v_5 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_3 64 128) (extract v_5 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 32;
      setRegister (lhs.of_reg ymm_2) (concat (mux (eq (extract v_3 0 64) (extract v_5 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_3 64 128) (extract v_5 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_3 128 192) (extract v_5 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_3 192 256) (extract v_5 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_2) (concat (mux (eq (extract v_3 0 64) (extract v_4 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_3 64 128) (extract v_4 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- getRegister (lhs.of_reg ymm_0);
      setRegister (lhs.of_reg ymm_2) (concat (mux (eq (extract v_3 0 64) (extract v_4 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_3 64 128) (extract v_4 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (concat (mux (eq (extract v_3 128 192) (extract v_4 128 192)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_3 192 256) (extract v_4 192 256)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)))));
      pure ()
    pat_end
