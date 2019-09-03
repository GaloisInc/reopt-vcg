def pcmpeqq1 : instruction :=
  definst "pcmpeqq" $ do
    pattern fun (v_3268 : reg (bv 128)) (v_3269 : reg (bv 128)) => do
      v_6929 <- getRegister v_3269;
      v_6931 <- getRegister v_3268;
      setRegister (lhs.of_reg v_3269) (concat (mux (eq (extract v_6929 0 64) (extract v_6931 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_6929 64 128) (extract v_6931 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3263 : Mem) (v_3264 : reg (bv 128)) => do
      v_10972 <- getRegister v_3264;
      v_10974 <- evaluateAddress v_3263;
      v_10975 <- load v_10974 16;
      setRegister (lhs.of_reg v_3264) (concat (mux (eq (extract v_10972 0 64) (extract v_10975 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_10972 64 128) (extract v_10975 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
