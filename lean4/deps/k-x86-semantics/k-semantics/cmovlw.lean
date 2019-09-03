def cmovlw1 : instruction :=
  definst "cmovlw" $ do
    pattern fun (v_2721 : reg (bv 16)) (v_2722 : reg (bv 16)) => do
      v_4460 <- getRegister sf;
      v_4462 <- getRegister of;
      v_4466 <- getRegister v_2721;
      v_4467 <- getRegister v_2722;
      setRegister (lhs.of_reg v_2722) (mux (notBool_ (eq (eq v_4460 (expression.bv_nat 1 1)) (eq v_4462 (expression.bv_nat 1 1)))) v_4466 v_4467);
      pure ()
    pat_end;
    pattern fun (v_2715 : Mem) (v_2717 : reg (bv 16)) => do
      v_8071 <- getRegister sf;
      v_8073 <- getRegister of;
      v_8077 <- evaluateAddress v_2715;
      v_8078 <- load v_8077 2;
      v_8079 <- getRegister v_2717;
      setRegister (lhs.of_reg v_2717) (mux (notBool_ (eq (eq v_8071 (expression.bv_nat 1 1)) (eq v_8073 (expression.bv_nat 1 1)))) v_8078 v_8079);
      pure ()
    pat_end
