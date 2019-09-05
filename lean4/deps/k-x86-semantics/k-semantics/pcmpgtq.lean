def pcmpgtq1 : instruction :=
  definst "pcmpgtq" $ do
    pattern fun (v_2473 : reg (bv 128)) (v_2474 : reg (bv 128)) => do
      v_4031 <- getRegister v_2474;
      v_4033 <- getRegister v_2473;
      setRegister (lhs.of_reg v_2474) (concat (mux (sgt (extract v_4031 0 64) (extract v_4033 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_4031 64 128) (extract v_4033 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (v_2470 : Mem) (v_2469 : reg (bv 128)) => do
      v_10997 <- getRegister v_2469;
      v_10999 <- evaluateAddress v_2470;
      v_11000 <- load v_10999 16;
      setRegister (lhs.of_reg v_2469) (concat (mux (sgt (extract v_10997 0 64) (extract v_11000 0 64)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)) (mux (sgt (extract v_10997 64 128) (extract v_11000 64 128)) (expression.bv_nat 64 18446744073709551615) (expression.bv_nat 64 0)));
      pure ()
    pat_end
