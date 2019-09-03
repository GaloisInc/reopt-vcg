def cmovaq1 : instruction :=
  definst "cmovaq" $ do
    pattern fun (v_2422 : reg (bv 64)) (v_2423 : reg (bv 64)) => do
      v_4087 <- getRegister cf;
      v_4090 <- getRegister zf;
      v_4094 <- getRegister v_2422;
      v_4095 <- getRegister v_2423;
      setRegister (lhs.of_reg v_2423) (mux (bit_and (notBool_ (eq v_4087 (expression.bv_nat 1 1))) (notBool_ (eq v_4090 (expression.bv_nat 1 1)))) v_4094 v_4095);
      pure ()
    pat_end;
    pattern fun (v_2418 : Mem) (v_2419 : reg (bv 64)) => do
      v_7809 <- getRegister cf;
      v_7812 <- getRegister zf;
      v_7816 <- evaluateAddress v_2418;
      v_7817 <- load v_7816 8;
      v_7818 <- getRegister v_2419;
      setRegister (lhs.of_reg v_2419) (mux (bit_and (notBool_ (eq v_7809 (expression.bv_nat 1 1))) (notBool_ (eq v_7812 (expression.bv_nat 1 1)))) v_7817 v_7818);
      pure ()
    pat_end
