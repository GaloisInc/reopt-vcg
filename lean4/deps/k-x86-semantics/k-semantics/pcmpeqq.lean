def pcmpeqq1 : instruction :=
  definst "pcmpeqq" $ do
    pattern fun (v_3331 : reg (bv 128)) (v_3332 : reg (bv 128)) => do
      v_6773 <- getRegister v_3332;
      v_6775 <- getRegister v_3331;
      setRegister (lhs.of_reg v_3332) (concat (mux (eq (extract v_6773 0 64) (extract v_6775 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_6773 64 128) (extract v_6775 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_3326 : Mem) (v_3327 : reg (bv 128)) => do
      v_10655 <- getRegister v_3327;
      v_10657 <- evaluateAddress v_3326;
      v_10658 <- load v_10657 16;
      setRegister (lhs.of_reg v_3327) (concat (mux (eq (extract v_10655 0 64) (extract v_10658 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (eq (extract v_10655 64 128) (extract v_10658 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
