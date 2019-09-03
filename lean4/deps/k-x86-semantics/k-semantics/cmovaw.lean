def cmovaw1 : instruction :=
  definst "cmovaw" $ do
    pattern fun (v_2419 : reg (bv 16)) (v_2420 : reg (bv 16)) => do
      v_4089 <- getRegister cf;
      v_4092 <- getRegister zf;
      v_4096 <- getRegister v_2419;
      v_4097 <- getRegister v_2420;
      setRegister (lhs.of_reg v_2420) (mux (bit_and (notBool_ (eq v_4089 (expression.bv_nat 1 1))) (notBool_ (eq v_4092 (expression.bv_nat 1 1)))) v_4096 v_4097);
      pure ()
    pat_end;
    pattern fun (v_2416 : Mem) (v_2415 : reg (bv 16)) => do
      v_7848 <- getRegister cf;
      v_7851 <- getRegister zf;
      v_7855 <- evaluateAddress v_2416;
      v_7856 <- load v_7855 2;
      v_7857 <- getRegister v_2415;
      setRegister (lhs.of_reg v_2415) (mux (bit_and (notBool_ (eq v_7848 (expression.bv_nat 1 1))) (notBool_ (eq v_7851 (expression.bv_nat 1 1)))) v_7856 v_7857);
      pure ()
    pat_end
