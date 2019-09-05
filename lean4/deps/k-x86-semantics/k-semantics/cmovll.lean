def cmovll1 : instruction :=
  definst "cmovll" $ do
    pattern fun (v_2755 : reg (bv 32)) (v_2756 : reg (bv 32)) => do
      v_4483 <- getRegister sf;
      v_4485 <- getRegister of;
      v_4489 <- getRegister v_2755;
      v_4490 <- getRegister v_2756;
      setRegister (lhs.of_reg v_2756) (mux (notBool_ (eq (eq v_4483 (expression.bv_nat 1 1)) (eq v_4485 (expression.bv_nat 1 1)))) v_4489 v_4490);
      pure ()
    pat_end;
    pattern fun (v_2748 : Mem) (v_2751 : reg (bv 32)) => do
      v_8062 <- getRegister sf;
      v_8064 <- getRegister of;
      v_8068 <- evaluateAddress v_2748;
      v_8069 <- load v_8068 4;
      v_8070 <- getRegister v_2751;
      setRegister (lhs.of_reg v_2751) (mux (notBool_ (eq (eq v_8062 (expression.bv_nat 1 1)) (eq v_8064 (expression.bv_nat 1 1)))) v_8069 v_8070);
      pure ()
    pat_end
