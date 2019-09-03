def cmovnew1 : instruction :=
  definst "cmovnew" $ do
    pattern fun (v_2869 : reg (bv 16)) (v_2870 : reg (bv 16)) => do
      v_4663 <- getRegister zf;
      v_4666 <- getRegister v_2869;
      v_4667 <- getRegister v_2870;
      setRegister (lhs.of_reg v_2870) (mux (notBool_ (eq v_4663 (expression.bv_nat 1 1))) v_4666 v_4667);
      pure ()
    pat_end;
    pattern fun (v_2866 : Mem) (v_2865 : reg (bv 16)) => do
      v_8260 <- getRegister zf;
      v_8263 <- evaluateAddress v_2866;
      v_8264 <- load v_8263 2;
      v_8265 <- getRegister v_2865;
      setRegister (lhs.of_reg v_2865) (mux (notBool_ (eq v_8260 (expression.bv_nat 1 1))) v_8264 v_8265);
      pure ()
    pat_end
