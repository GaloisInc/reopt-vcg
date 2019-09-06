def pcmpgtq1 : instruction :=
  definst "pcmpgtq" $ do
    pattern fun (v_2501 : reg (bv 128)) (v_2502 : reg (bv 128)) => do
      v_4058 <- getRegister v_2502;
      v_4060 <- getRegister v_2501;
      setRegister (lhs.of_reg v_2502) (concat (mux (sgt (extract v_4058 0 64) (extract v_4060 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_4058 64 128) (extract v_4060 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2497 : Mem) (v_2498 : reg (bv 128)) => do
      v_10973 <- getRegister v_2498;
      v_10975 <- evaluateAddress v_2497;
      v_10976 <- load v_10975 16;
      setRegister (lhs.of_reg v_2498) (concat (mux (sgt (extract v_10973 0 64) (extract v_10976 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_10973 64 128) (extract v_10976 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
