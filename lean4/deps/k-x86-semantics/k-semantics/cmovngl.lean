def cmovngl1 : instruction :=
  definst "cmovngl" $ do
    pattern fun (v_2971 : reg (bv 32)) (v_2972 : reg (bv 32)) => do
      v_4780 <- getRegister zf;
      v_4782 <- getRegister sf;
      v_4784 <- getRegister of;
      v_4789 <- getRegister v_2971;
      v_4790 <- getRegister v_2972;
      setRegister (lhs.of_reg v_2972) (mux (bit_or (eq v_4780 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_4782 (expression.bv_nat 1 1)) (eq v_4784 (expression.bv_nat 1 1))))) v_4789 v_4790);
      pure ()
    pat_end;
    pattern fun (v_2964 : Mem) (v_2967 : reg (bv 32)) => do
      v_8287 <- getRegister zf;
      v_8289 <- getRegister sf;
      v_8291 <- getRegister of;
      v_8296 <- evaluateAddress v_2964;
      v_8297 <- load v_8296 4;
      v_8298 <- getRegister v_2967;
      setRegister (lhs.of_reg v_2967) (mux (bit_or (eq v_8287 (expression.bv_nat 1 1)) (notBool_ (eq (eq v_8289 (expression.bv_nat 1 1)) (eq v_8291 (expression.bv_nat 1 1))))) v_8297 v_8298);
      pure ()
    pat_end
