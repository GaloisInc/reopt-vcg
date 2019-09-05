def cmovzl1 : instruction :=
  definst "cmovzl" $ do
    pattern fun (v_3343 : reg (bv 32)) (v_3344 : reg (bv 32)) => do
      v_5236 <- getRegister zf;
      v_5238 <- getRegister v_3343;
      v_5239 <- getRegister v_3344;
      setRegister (lhs.of_reg v_3344) (mux (eq v_5236 (expression.bv_nat 1 1)) v_5238 v_5239);
      pure ()
    pat_end;
    pattern fun (v_3336 : Mem) (v_3339 : reg (bv 32)) => do
      v_8611 <- getRegister zf;
      v_8613 <- evaluateAddress v_3336;
      v_8614 <- load v_8613 4;
      v_8615 <- getRegister v_3339;
      setRegister (lhs.of_reg v_3339) (mux (eq v_8611 (expression.bv_nat 1 1)) v_8614 v_8615);
      pure ()
    pat_end
