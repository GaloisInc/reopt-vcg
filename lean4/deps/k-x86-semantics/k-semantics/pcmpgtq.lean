def pcmpgtq1 : instruction :=
  definst "pcmpgtq" $ do
    pattern fun (v_2424 : reg (bv 128)) (v_2425 : reg (bv 128)) => do
      v_3980 <- getRegister v_2425;
      v_3982 <- getRegister v_2424;
      setRegister (lhs.of_reg v_2425) (concat (mux (sgt (extract v_3980 0 64) (extract v_3982 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_3980 64 128) (extract v_3982 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2420 : Mem) (v_2421 : reg (bv 128)) => do
      v_11120 <- getRegister v_2421;
      v_11122 <- evaluateAddress v_2420;
      v_11123 <- load v_11122 16;
      setRegister (lhs.of_reg v_2421) (concat (mux (sgt (extract v_11120 0 64) (extract v_11123 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_11120 64 128) (extract v_11123 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
