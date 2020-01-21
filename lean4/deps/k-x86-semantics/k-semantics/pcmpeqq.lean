def pcmpeqq : instruction :=
  definst "pcmpeqq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      setRegister (lhs.of_reg xmm_1) (concat (mux (eq (extract v_2 0 64) (extract v_4 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_2 64 128) (extract v_4 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_1) (concat (mux (eq (extract v_2 0 64) (extract v_3 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_2 64 128) (extract v_3 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
