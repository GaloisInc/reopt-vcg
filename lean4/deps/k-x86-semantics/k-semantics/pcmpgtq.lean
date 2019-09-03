def pcmpgtq1 : instruction :=
  definst "pcmpgtq" $ do
    pattern fun (v_2410 : reg (bv 128)) (v_2411 : reg (bv 128)) => do
      v_3967 <- getRegister v_2411;
      v_3969 <- getRegister v_2410;
      setRegister (lhs.of_reg v_2411) (concat (mux (sgt (extract v_3967 0 64) (extract v_3969 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_3967 64 128) (extract v_3969 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2405 : Mem) (v_2406 : reg (bv 128)) => do
      v_11437 <- getRegister v_2406;
      v_11439 <- evaluateAddress v_2405;
      v_11440 <- load v_11439 16;
      setRegister (lhs.of_reg v_2406) (concat (mux (sgt (extract v_11437 0 64) (extract v_11440 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_11437 64 128) (extract v_11440 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
