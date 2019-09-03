def cmovlq1 : instruction :=
  definst "cmovlq" $ do
    pattern fun (v_2699 : reg (bv 64)) (v_2700 : reg (bv 64)) => do
      v_4433 <- getRegister sf;
      v_4435 <- getRegister of;
      v_4439 <- getRegister v_2699;
      v_4440 <- getRegister v_2700;
      setRegister (lhs.of_reg v_2700) (mux (notBool_ (eq (eq v_4433 (expression.bv_nat 1 1)) (eq v_4435 (expression.bv_nat 1 1)))) v_4439 v_4440);
      pure ()
    pat_end;
    pattern fun (v_2694 : Mem) (v_2695 : reg (bv 64)) => do
      v_8087 <- getRegister sf;
      v_8089 <- getRegister of;
      v_8093 <- evaluateAddress v_2694;
      v_8094 <- load v_8093 8;
      v_8095 <- getRegister v_2695;
      setRegister (lhs.of_reg v_2695) (mux (notBool_ (eq (eq v_8087 (expression.bv_nat 1 1)) (eq v_8089 (expression.bv_nat 1 1)))) v_8094 v_8095);
      pure ()
    pat_end
