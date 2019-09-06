def pcmpeqq1 : instruction :=
  definst "pcmpeqq" $ do
    pattern fun (v_3356 : reg (bv 128)) (v_3357 : reg (bv 128)) => do
      v_6800 <- getRegister v_3357;
      v_6802 <- getRegister v_3356;
      setRegister (lhs.of_reg v_3357) (concat (mux (eq (extract v_6800 0 64) (extract v_6802 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_6800 64 128) (extract v_6802 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3352 : Mem) (v_3353 : reg (bv 128)) => do
      v_10682 <- getRegister v_3353;
      v_10684 <- evaluateAddress v_3352;
      v_10685 <- load v_10684 16;
      setRegister (lhs.of_reg v_3353) (concat (mux (eq (extract v_10682 0 64) (extract v_10685 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_10682 64 128) (extract v_10685 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
