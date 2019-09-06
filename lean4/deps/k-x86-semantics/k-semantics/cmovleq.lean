def cmovleq1 : instruction :=
  definst "cmovleq" $ do
    pattern fun (v_2753 : reg (bv 64)) (v_2754 : reg (bv 64)) => do
      v_4430 <- getRegister zf;
      v_4431 <- getRegister sf;
      v_4432 <- getRegister of;
      v_4436 <- getRegister v_2753;
      v_4437 <- getRegister v_2754;
      setRegister (lhs.of_reg v_2754) (mux (bit_or v_4430 (notBool_ (eq v_4431 v_4432))) v_4436 v_4437);
      pure ()
    pat_end;
    pattern fun (v_2745 : Mem) (v_2746 : reg (bv 64)) => do
      v_7845 <- getRegister zf;
      v_7846 <- getRegister sf;
      v_7847 <- getRegister of;
      v_7851 <- evaluateAddress v_2745;
      v_7852 <- load v_7851 8;
      v_7853 <- getRegister v_2746;
      setRegister (lhs.of_reg v_2746) (mux (bit_or v_7845 (notBool_ (eq v_7846 v_7847))) v_7852 v_7853);
      pure ()
    pat_end
